(* See the .mli for a description of the purpose of this module. *)
open Core
open Coda_base
open Coda_numbers
open Signature_lib

(* Fee increase required to replace a transaction. This represents the cost to
   the network as a whole of checking, gossiping, and storing a transaction
   until it is included in a block. I did some napkin math and came up with
   $0.00007. Ideally we'd fetch an exchange rate and convert that into an amount
   of currency, but a made up number will do for the testnets at least. See
   issue #2385.
*)
let replace_fee : Currency.Fee.t = Currency.Fee.of_int 5

(* Invariants, maintained whenever a t is exposed from this module:
   * Iff a command is in all_by_fee it is also in all_by_sender.
   * Iff a command is at the head of its sender's queue it is also in
     applicable_by_fee.
   * Sequences in all_by_sender are ordered by nonce and "dense".
   * There are no empty sets or sequences.
   * Fee indices are correct.
   * Total currency required is correct.
   * size = the sum of sizes of the sets in all_by_fee = the sum of the lengths
     of the queues in all_by_sender
*)
type t =
  { applicable_by_fee:
      User_command.With_valid_signature.Set.t Currency.Fee.Map.t
        (** Transactions valid against the current ledger, indexed by fee. *)
  ; all_by_sender:
      (User_command.With_valid_signature.t F_sequence.t * Currency.Amount.t)
      Public_key.Compressed.Map.t
        (** All pending transactions along with the total currency required to
            execute them, indexed by sender account. Ordered by nonce inside the
            accounts. *)
  ; all_by_fee: User_command.With_valid_signature.Set.t Currency.Fee.Map.t
        (** All transactions in the pool indexed by fee. *)
  ; size: int }
[@@deriving sexp_of]

(* Compute the total currency required from the sender to execute a command.
   Returns None in case of overflow.
*)
let currency_consumed :
    User_command.With_valid_signature.t -> Currency.Amount.t option =
 fun cmd ->
  let cmd' = User_command.forget_check cmd in
  let fee_amt = Currency.Amount.of_fee @@ User_command.fee cmd' in
  Currency.Amount.(
    fee_amt
    +
    match cmd'.payload.body with
    | Payment {amount; _} ->
        amount
    | Stake_delegation _ ->
        zero)

let currency_consumed' :
       User_command.With_valid_signature.t
    -> (Currency.Amount.t, [> `Overflow]) Result.t =
 fun cmd -> cmd |> currency_consumed |> Result.of_option ~error:`Overflow

module For_tests = struct
  (* Check the invariants of the pool structure as listed in the comment above.
  *)
  let assert_invariants : t -> unit =
   fun {applicable_by_fee; all_by_sender; all_by_fee; size} ->
    let assert_all_by_fee tx =
      if
        Set.mem
          (Map.find_exn all_by_fee
             (User_command.forget_check tx |> User_command.fee))
          tx
      then ()
      else
        failwith
        @@ sprintf
             !"Not found in all_by_fee: %{sexp: \
               User_command.With_valid_signature.t}"
             tx
    in
    Map.iteri applicable_by_fee ~f:(fun ~key ~data ->
        Set.iter data ~f:(fun tx ->
            let unchecked = User_command.forget_check tx in
            [%test_eq: Currency.Fee.t] key (User_command.fee unchecked) ;
            let tx' =
              Map.find_exn all_by_sender (User_command.sender unchecked)
              |> Tuple2.get1 |> F_sequence.head_exn
            in
            [%test_eq: User_command.With_valid_signature.t] tx tx' ;
            assert_all_by_fee tx ) ) ;
    Map.iteri all_by_sender
      ~f:(fun ~key:sender ~data:(tx_seq, currency_reserved) ->
        assert (F_sequence.length tx_seq > 0) ;
        let check_consistent tx =
          [%test_eq: Public_key.Compressed.t]
            (User_command.forget_check tx |> User_command.sender)
            sender ;
          assert_all_by_fee tx
        in
        let applicable, inapplicables =
          Option.value_exn (F_sequence.uncons tx_seq)
        in
        let applicable_unchecked = User_command.forget_check applicable in
        check_consistent applicable ;
        assert (
          Set.mem
            (Map.find_exn applicable_by_fee
               (User_command.fee applicable_unchecked))
            applicable ) ;
        let _last_nonce, currency_reserved' =
          F_sequence.foldl
            (fun (prev_nonce, currency_acc) tx ->
              let unchecked = User_command.forget_check tx in
              [%test_eq: Account_nonce.t]
                (User_command.nonce unchecked)
                (Account_nonce.succ prev_nonce) ;
              check_consistent tx ;
              ( User_command.nonce unchecked
              , Option.value_exn
                  Currency.Amount.(
                    Option.value_exn (currency_consumed tx) + currency_acc) )
              )
            ( User_command.nonce applicable_unchecked
            , Option.value_exn (currency_consumed applicable) )
            inapplicables
        in
        [%test_eq: Currency.Amount.t] currency_reserved currency_reserved' ) ;
    Map.iteri all_by_fee ~f:(fun ~key:fee ~data:tx_set ->
        Set.iter tx_set ~f:(fun tx ->
            let unchecked = User_command.forget_check tx in
            [%test_eq: Currency.Fee.t] fee (User_command.fee unchecked) ;
            let sender_txs, _currency_reserved =
              Map.find_exn all_by_sender (User_command.sender unchecked)
            in
            let applicable, _inapplicables =
              Option.value_exn (F_sequence.uncons sender_txs)
            in
            assert (
              Set.mem
                (Map.find_exn applicable_by_fee
                   (applicable |> User_command.forget_check |> User_command.fee))
                applicable ) ;
            let first_nonce =
              applicable |> User_command.forget_check |> User_command.nonce
              |> Account_nonce.to_int
            in
            let _split_l, split_r =
              F_sequence.split_at sender_txs
                ( Account_nonce.to_int (User_command.nonce unchecked)
                - first_nonce )
            in
            let tx' = F_sequence.head_exn split_r in
            [%test_eq: User_command.With_valid_signature.t] tx tx' ) ) ;
    [%test_eq: int]
      (Map.fold all_by_fee ~init:0 ~f:(fun ~key:_ ~data:cmd_set acc ->
           Set.length cmd_set + acc ))
      size
end

let empty : t =
  { applicable_by_fee= Currency.Fee.Map.empty
  ; all_by_sender= Public_key.Compressed.Map.empty
  ; all_by_fee= Currency.Fee.Map.empty
  ; size= 0 }

let size : t -> int = fun t -> t.size

let min_fee : t -> Currency.Fee.t option =
 fun {all_by_fee; _} -> Option.map ~f:Tuple2.get1 @@ Map.min_elt all_by_fee

let member : t -> User_command.With_valid_signature.t -> bool =
 fun t cmd ->
  match
    Map.find t.all_by_fee (User_command.forget_check cmd |> User_command.fee)
  with
  | None ->
      false
  | Some cmds_at_fee ->
      Set.mem cmds_at_fee cmd

(* Remove a command from the applicable_by_fee field. This may break an
   invariant. *)
let remove_applicable_exn : t -> User_command.With_valid_signature.t -> t =
 fun t cmd ->
  let fee = User_command.forget_check cmd |> User_command.fee in
  {t with applicable_by_fee= Map_set.remove_exn t.applicable_by_fee fee cmd}

(* Remove a command from the all_by_fee field and decrement size. This may break
   an invariant. *)
let remove_all_by_fee_exn : t -> User_command.With_valid_signature.t -> t =
 fun t cmd ->
  let fee = User_command.forget_check cmd |> User_command.fee in
  {t with all_by_fee= Map_set.remove_exn t.all_by_fee fee cmd; size= t.size - 1}

(* Remove a given command from the pool, as well as any commands that depend on
   it. Called from revalidate and remove_lowest_fee, and when replacing
   transactions. *)
let remove_with_dependents_exn :
       t
    -> User_command.With_valid_signature.t
    -> User_command.With_valid_signature.t Sequence.t * t =
 fun t cmd ->
  let unchecked = User_command.forget_check cmd in
  let sender = User_command.sender unchecked in
  let sender_queue, reserved_currency = Map.find_exn t.all_by_sender sender in
  assert (not @@ F_sequence.is_empty sender_queue) ;
  let first_cmd = F_sequence.head_exn sender_queue in
  let first_nonce =
    User_command.forget_check first_cmd
    |> User_command.nonce |> Account_nonce.to_int
  in
  let cmd_nonce = User_command.nonce unchecked |> Account_nonce.to_int in
  assert (cmd_nonce >= first_nonce) ;
  let index = cmd_nonce - first_nonce in
  let keep_queue, drop_queue = F_sequence.split_at sender_queue index in
  assert (not (F_sequence.is_empty drop_queue)) ;
  let currency_to_remove =
    F_sequence.foldl
      (fun acc cmd' ->
        Option.value_exn
          (* safe because we check for overflow when we add commands. *)
          (let open Option.Let_syntax in
          let%bind consumed = currency_consumed cmd' in
          Currency.Amount.(consumed + acc)) )
      Currency.Amount.zero drop_queue
  in
  let reserved_currency' =
    (* This is safe because the currency in a subset of the commands much be <=
       total currency in all the commands. *)
    Option.value_exn Currency.Amount.(reserved_currency - currency_to_remove)
  in
  let t' =
    F_sequence.foldl
      (fun acc cmd' -> remove_all_by_fee_exn acc cmd')
      t drop_queue
  in
  ( F_sequence.to_seq drop_queue
  , { t' with
      all_by_sender=
        ( if not (F_sequence.is_empty keep_queue) then
          Map.set t'.all_by_sender ~key:sender
            ~data:(keep_queue, reserved_currency')
        else (
          assert (Currency.Amount.(equal reserved_currency' zero)) ;
          Map.remove t'.all_by_sender sender ) )
    ; applicable_by_fee=
        ( if User_command.With_valid_signature.equal first_cmd cmd then
          Map_set.remove_exn t'.applicable_by_fee
            (User_command.fee unchecked)
            cmd
        else t'.applicable_by_fee ) } )

(** Drop commands from the end of the queue until the total currency consumed is
    <= the current balance. *)
let drop_until_sufficient_balance :
       User_command.With_valid_signature.t F_sequence.t * Currency.Amount.t
    -> Currency.Amount.t
    -> User_command.With_valid_signature.t F_sequence.t
       * Currency.Amount.t
       * User_command.With_valid_signature.t Sequence.t =
 fun (queue, currency_reserved) current_balance ->
  let rec go queue' currency_reserved' dropped_so_far =
    if Currency.Amount.(currency_reserved' <= current_balance) then
      (queue', currency_reserved', dropped_so_far)
    else
      let daeh, liat =
        Option.value_exn
          ~message:
            "couldn't drop any more transactions when trying to preserve \
             sufficient balance"
          (F_sequence.unsnoc queue')
      in
      let consumed = Option.value_exn (currency_consumed liat) in
      go daeh
        (Option.value_exn Currency.Amount.(currency_reserved' - consumed))
        (Sequence.append dropped_so_far @@ Sequence.singleton liat)
  in
  go queue currency_reserved Sequence.empty

(* Iterate over all commands in the pool, removing them if they require too much
   currency or have too low of a nonce.
*)
let revalidate :
       t
    -> (Public_key.Compressed.t -> Account_nonce.t * Currency.Amount.t)
    -> t * User_command.With_valid_signature.t Sequence.t =
 fun t f ->
  Map.fold t.all_by_sender ~init:(t, Sequence.empty)
    ~f:(fun ~key:sender
       ~data:(queue, currency_reserved)
       ((t', dropped_acc) as acc)
       ->
      let current_nonce, current_balance = f sender in
      let first_cmd = F_sequence.head_exn queue in
      let first_nonce = User_command.(first_cmd |> forget_check |> nonce) in
      if Account_nonce.(current_nonce < first_nonce) then
        let dropped, t'' = remove_with_dependents_exn t first_cmd in
        (t'', Sequence.append dropped_acc dropped)
      else
        (* current_nonce >= first_nonce *)
        let idx = Account_nonce.(to_int current_nonce - to_int first_nonce) in
        let drop_queue, keep_queue = F_sequence.split_at queue idx in
        let currency_reserved' =
          F_sequence.foldl
            (fun c cmd ->
              Option.value_exn
                Currency.Amount.(c - Option.value_exn (currency_consumed cmd))
              )
            currency_reserved drop_queue
        in
        let keep_queue', currency_reserved'', dropped_for_balance =
          drop_until_sufficient_balance
            (keep_queue, currency_reserved')
            current_balance
        in
        let to_drop =
          Sequence.append (F_sequence.to_seq drop_queue) dropped_for_balance
        in
        match Sequence.next to_drop with
        | None ->
            acc
        | Some (head, tail) ->
            let t'' =
              Sequence.fold tail
                ~init:
                  (remove_all_by_fee_exn (remove_applicable_exn t' head) head)
                ~f:remove_all_by_fee_exn
            in
            ( { t'' with
                all_by_sender=
                  Map.set t''.all_by_sender ~key:sender
                    ~data:(keep_queue', currency_reserved'') }
            , Sequence.append dropped_acc to_drop ) )

let handle_committed_txn :
    t -> Public_key.Compressed.t -> Account_nonce.t -> Currency.Amount.t -> t =
 fun t sender nonce_to_remove current_balance ->
  match Map.find t.all_by_sender sender with
  | None ->
      t
  | Some (cmds, currency_reserved) ->
      let first_cmd, rest_cmds = Option.value_exn (F_sequence.uncons cmds) in
      let first_nonce =
        first_cmd |> User_command.forget_check |> User_command.nonce
      in
      if Account_nonce.(nonce_to_remove <> first_nonce) then
        failwith
          "Tried to handle a committed transaction in the pool but its nonce \
           doesn't match the head of the queue for that sender."
      else
        let first_cmd_consumed =
          (* safe since we checked this when we added it to the pool originally *)
          Option.value_exn (currency_consumed first_cmd)
        in
        let currency_reserved' =
          (* safe since the sum reserved must be >= reserved by any individual
             command *)
          Option.value_exn
            Currency.Amount.(currency_reserved - first_cmd_consumed)
        in
        let t' =
          t
          |> Fn.flip remove_applicable_exn first_cmd
          |> Fn.flip remove_all_by_fee_exn first_cmd
        in
        let new_queued_cmds, currency_reserved'', dropped_cmds =
          drop_until_sufficient_balance
            (rest_cmds, currency_reserved')
            current_balance
        in
        let t'' =
          Sequence.fold dropped_cmds ~init:t' ~f:remove_all_by_fee_exn
        in
        { t'' with
          all_by_sender=
            ( if F_sequence.is_empty new_queued_cmds then
              Map.remove t.all_by_sender sender
            else
              Map.set t.all_by_sender ~key:sender
                ~data:(new_queued_cmds, currency_reserved'') )
        ; applicable_by_fee=
            ( match F_sequence.uncons new_queued_cmds with
            | None ->
                t''.applicable_by_fee
            | Some (head_cmd, _) ->
                Map_set.insert
                  (module User_command.With_valid_signature)
                  t''.applicable_by_fee
                  (head_cmd |> User_command.forget_check |> User_command.fee)
                  head_cmd ) }

let remove_lowest_fee : t -> User_command.With_valid_signature.t Sequence.t * t
    =
 fun t ->
  match Map.min_elt t.all_by_fee with
  | None ->
      (Sequence.empty, t)
  | Some (_min_fee, min_fee_set) ->
      remove_with_dependents_exn t @@ Set.min_elt_exn min_fee_set

let get_highest_fee : t -> User_command.With_valid_signature.t option =
 fun t ->
  Option.map ~f:(Fn.compose Set.min_elt_exn Tuple2.get2)
  @@ Map.max_elt t.applicable_by_fee

(* Add a command that came in from gossip, or return an error. We need to check
   a whole bunch of conditions here and return the appropriate errors.
   Conditions:
   1. Command nonce must be >= account nonce.
   1a. If the sender's queue is empty, command nonce must equal account nonce.
   1b. If the sender's queue is non-empty, command nonce must be <= the nonce of
       the last queued command + 1
   2. The sum of the currency consumed by all queued commands for the sender
      must be <= the sender's balance.
   3. If a command is replaced, the new command must have a fee greater than the
      replaced command by at least replace fee * (number of commands after the
      the replaced command + 1)
   4. No integer overflows are allowed.

   These conditions are referenced in the comments below.
*)
let rec add_from_gossip_exn :
       t
    -> User_command.With_valid_signature.t
    -> Account_nonce.t
    -> Currency.Amount.t
    -> ( t * User_command.With_valid_signature.t Sequence.t
       , [ `Invalid_nonce
         | `Insufficient_funds
         | `Insufficient_replace_fee
         | `Overflow ] )
       Result.t =
 fun t cmd current_nonce balance ->
  let unchecked = User_command.forget_check cmd in
  let fee = User_command.fee unchecked in
  let sender = User_command.sender unchecked in
  let nonce = User_command.nonce unchecked in
  (* Result errors indicate problems with the command, while assert failures
     indicate bugs in Coda. *)
  let open Result.Let_syntax in
  let%bind consumed = currency_consumed' cmd in
  (* C4 *)
  match Map.find t.all_by_sender (User_command.sender unchecked) with
  | None ->
      (* nothing queued for this sender *)
      let%bind () =
        Result.ok_if_true
          (Account_nonce.equal current_nonce nonce)
          ~error:`Invalid_nonce
        (* C1/1a *)
      in
      let%bind () =
        Result.ok_if_true
          Currency.Amount.(consumed <= balance)
          ~error:`Insufficient_funds
        (* C2 *)
      in
      Result.Ok
        ( { applicable_by_fee=
              Map_set.insert
                (module User_command.With_valid_signature)
                t.applicable_by_fee fee cmd
          ; all_by_sender=
              Map.set t.all_by_sender ~key:sender
                ~data:(F_sequence.singleton cmd, consumed)
          ; all_by_fee=
              Map_set.insert
                (module User_command.With_valid_signature)
                t.all_by_fee fee cmd
          ; size= t.size + 1 }
        , Sequence.empty )
  | Some (queued_cmds, reserved_currency) -> (
      (* commands queued for this sender *)
      assert (not @@ F_sequence.is_empty queued_cmds) ;
      let last_queued_nonce =
        F_sequence.last_exn queued_cmds
        |> User_command.forget_check |> User_command.nonce
      in
      if Account_nonce.equal (Account_nonce.succ last_queued_nonce) nonce then
        (* this command goes on the end *)
        let%bind reserved_currency' =
          Currency.Amount.(consumed + reserved_currency)
          |> Result.of_option ~error:`Overflow
          (* C4 *)
        in
        let%bind () =
          Result.ok_if_true
            Currency.Amount.(balance >= reserved_currency')
            ~error:`Insufficient_funds
          (* C2 *)
        in
        Result.Ok
          ( { t with
              all_by_sender=
                Map.set t.all_by_sender ~key:sender
                  ~data:(F_sequence.snoc queued_cmds cmd, reserved_currency')
            ; all_by_fee=
                Map_set.insert
                  (module User_command.With_valid_signature)
                  t.all_by_fee fee cmd
            ; size= t.size + 1 }
          , Sequence.empty )
      else
        (* we're replacing a command *)
        let first_queued_nonce =
          F_sequence.head_exn queued_cmds
          |> User_command.forget_check |> User_command.nonce
        in
        assert (Account_nonce.equal first_queued_nonce current_nonce) ;
        let%bind () =
          Result.ok_if_true
            (Account_nonce.between ~low:first_queued_nonce
               ~high:last_queued_nonce nonce)
            ~error:`Invalid_nonce
          (* C1/C1b *)
        in
        assert (
          F_sequence.length queued_cmds
          = Account_nonce.to_int last_queued_nonce
            - Account_nonce.to_int first_queued_nonce
            + 1 ) ;
        let _keep_queue, drop_queue =
          F_sequence.split_at queued_cmds
            ( Account_nonce.to_int nonce
            - Account_nonce.to_int first_queued_nonce )
        in
        let to_drop =
          F_sequence.head_exn drop_queue |> User_command.forget_check
        in
        assert (Account_nonce.equal (User_command.nonce to_drop) nonce) ;
        (* We check the fee increase twice because we need to be sure the
           subtraction is safe. *)
        let%bind () =
          Result.ok_if_true
            Currency.Fee.(fee >= User_command.fee to_drop)
            ~error:`Insufficient_replace_fee
          (* C3 *)
        in
        let increment =
          Currency.Fee.to_int
          @@ Option.value_exn Currency.Fee.(fee - User_command.fee to_drop)
        in
        let%bind () =
          Result.ok_if_true
            ( increment
            >= Currency.Fee.to_int replace_fee * F_sequence.length drop_queue
            )
            ~error:`Insufficient_replace_fee
          (* C3 *)
        in
        let dropped, t' =
          remove_with_dependents_exn t @@ F_sequence.head_exn drop_queue
        in
        (* check remove_exn dropped the right things *)
        [%test_eq: User_command.With_valid_signature.t Sequence.t] dropped
          (F_sequence.to_seq drop_queue) ;
        match add_from_gossip_exn t' cmd current_nonce balance with
        | Ok (t'', dropped') ->
            (* We've already removed them, so this should always be empty. *)
            assert (Sequence.is_empty dropped') ;
            Result.Ok (t'', dropped)
        | Error `Insufficient_funds ->
            Error `Insufficient_funds (* C2 *)
        | _ ->
            failwith "recursive add_exn failed" )

let add_from_backtrack : t -> User_command.With_valid_signature.t -> t =
 fun t cmd ->
  let unchecked = User_command.forget_check cmd in
  let sender = User_command.sender unchecked in
  let fee = User_command.fee unchecked in
  let consumed = Option.value_exn (currency_consumed cmd) in
  match Map.find t.all_by_sender sender with
  | None ->
      { all_by_sender=
          Map.add_exn t.all_by_sender
            ~key:
              sender
              (* If the command comes from backtracking, then we know it doesn't
               cause overflow, so it's OK to throw here.
              *)
            ~data:(F_sequence.singleton cmd, consumed)
      ; all_by_fee=
          Map_set.insert
            (module User_command.With_valid_signature)
            t.all_by_fee fee cmd
      ; applicable_by_fee=
          Map_set.insert
            (module User_command.With_valid_signature)
            t.applicable_by_fee fee cmd
      ; size= t.size + 1 }
  | Some (queue, currency_reserved) ->
      let first_queued = F_sequence.head_exn queue in
      if
        not
          (Account_nonce.equal
             (unchecked |> User_command.nonce |> Account_nonce.succ)
             (first_queued |> User_command.forget_check |> User_command.nonce))
      then
        failwith
        @@ sprintf
             !"indexed pool nonces inconsistent when adding from backtrack. \
               Trying to add %{sexp:User_command.With_valid_signature.t} to \
               %{sexp: t}"
             cmd t ;
      let t' = remove_applicable_exn t first_queued in
      { applicable_by_fee=
          Map_set.insert
            (module User_command.With_valid_signature)
            t'.applicable_by_fee fee cmd
      ; all_by_fee=
          Map_set.insert
            (module User_command.With_valid_signature)
            t'.all_by_fee fee cmd
      ; all_by_sender=
          Map.set t'.all_by_sender ~key:sender
            ~data:
              ( F_sequence.cons cmd queue
              , Option.value_exn Currency.Amount.(currency_reserved + consumed)
              )
      ; size= t.size + 1 }

let%test_module _ =
  ( module struct
    open For_tests

    let test_keys = Array.init 10 ~f:(fun _ -> Signature_lib.Keypair.create ())

    let gen_cmd =
      User_command.With_valid_signature.Gen.payment_with_random_participants
        ~keys:test_keys ~max_amount:1000 ~max_fee:10

    module Array_m (M : Monad.S) = struct
      (** Array.init but parameterized over a monad. *)
      let init : int -> f:(int -> 'a M.t) -> 'a array M.t =
       fun n ~f ->
        let rec go : 'a list -> int -> 'a list M.t =
         fun xs n' ->
          if n' > 0 then M.(f n' >>= fun x -> go (x :: xs) (n' - 1))
          else M.return @@ List.rev xs
        in
        M.map (go [] n) ~f:Array.of_list
    end

    module Generator_array = Array_m (Quickcheck.Generator)

    (* Generate an array with a Dirichlet distribution, used for coming up with
       random splits of a quantity. Symmetric Dirichlet distribution with alpha
       = 1.
    *)
    let gen_division : int -> float array Quickcheck.Generator.t =
     fun n ->
      let open Quickcheck.Generator.Let_syntax in
      let%map gammas =
        Generator_array.init n ~f:(fun _ ->
            let open Quickcheck.Generator.Let_syntax in
            (* technically this should be (0, 1] and not (0, 1) but I expect it
               doesn't matter for our purposes. *)
            let%map uniform = Float.gen_uniform_excl 0. 1. in
            Float.log uniform )
      in
      let sum = Array.fold gammas ~init:0. ~f:(fun x y -> x +. y) in
      Array.map gammas ~f:(fun gamma -> gamma /. sum)

    let gen_currency_division :
           int
        -> Currency.Amount.t
        -> Currency.Amount.t array Quickcheck.Generator.t =
     fun n total_currency ->
      let total_float =
        Float.of_int @@ Currency.Amount.to_int total_currency
      in
      Quickcheck.Generator.map (gen_division n) ~f:(fun prop_array ->
          Array.map prop_array ~f:(fun proportion ->
              Currency.Amount.of_int @@ Float.iround_down_exn
              @@ (proportion *. total_float) ) )

    let%test_unit "empty invariants" = assert_invariants empty

    let%test_unit "singleton properties" =
      Quickcheck.test (gen_cmd ()) ~f:(fun cmd ->
          let pool = empty in
          let add_res =
            add_from_gossip_exn pool cmd Account_nonce.zero
              (Currency.Amount.of_int 500)
          in
          if
            Option.value_exn (currency_consumed cmd)
            |> Currency.Amount.to_int > 500
          then
            match add_res with
            | Error `Insufficient_funds ->
                ()
            | _ ->
                failwith "should've returned nsf"
          else
            match add_res with
            | Ok (pool', dropped) ->
                assert_invariants pool' ;
                assert (Sequence.is_empty dropped) ;
                [%test_eq: int] (size pool') 1 ;
                [%test_eq: User_command.With_valid_signature.t option]
                  (get_highest_fee pool') (Some cmd) ;
                let dropped', pool'' = remove_lowest_fee pool' in
                [%test_eq: User_command.With_valid_signature.t Sequence.t]
                  dropped' (Sequence.singleton cmd) ;
                [%test_eq: t] pool pool''
            | _ ->
                failwith "should've succeeded" )

    let%test_unit "sequential adds (all valid)" =
      let gen :
          ( Account_nonce.t list
          * Currency.Amount.t list
          * (int * User_command.With_valid_signature.t) list )
          Quickcheck.Generator.t =
        let open Quickcheck.Generator.Let_syntax in
        let%bind initial_balances =
          List.gen_with_length 10
          @@ Currency.Amount.(gen_incl zero @@ of_int 10_000)
        in
        let current_balances = Array.of_list initial_balances in
        let%bind initial_nonces =
          Quickcheck.Generator.map ~f:(List.map ~f:Account_nonce.of_int)
          @@ List.gen_with_length 10 @@ Int.gen_incl 0 100
        in
        let current_nonces = Array.of_list initial_nonces in
        let%bind size = Quickcheck.Generator.size in
        let rec go n =
          if n > 0 then (
            let%bind sender =
              Quickcheck.Generator.filter ~f:(fun idx ->
                  current_balances.(idx) > Currency.Amount.of_int 10 )
              @@ Int.gen_incl 0 9
            in
            let%bind fee = Currency.Fee.(gen_incl zero (of_int 10)) in
            let%bind amount =
              Currency.Amount.(
                gen_incl zero
                  (Option.value_exn (current_balances.(sender) - of_fee fee)))
            in
            let nonce = current_nonces.(sender) in
            current_nonces.(sender)
            <- Account_nonce.succ current_nonces.(sender) ;
            current_balances.(sender)
            <- Option.value_exn
                 Currency.Amount.(
                   Option.value_exn (current_balances.(sender) - amount)
                   - of_fee fee) ;
            let%bind memo = String.quickcheck_generator in
            let%bind receiver =
              Quickcheck.Generator.filter (Int.gen_incl 0 9) ~f:(fun idx ->
                  idx <> sender )
            in
            let receiver_pk =
              Public_key.compress test_keys.(receiver).public_key
            in
            let cmd_payload =
              User_command.Payload.create ~fee ~nonce
                ~memo:(User_command_memo.create_exn memo)
                ~body:
                  (User_command.Payload.Body.Payment
                     {receiver= receiver_pk; amount})
            in
            let cmd =
              User_command.For_tests.fake_sign test_keys.(sender) cmd_payload
            in
            let%bind rest = go (n - 1) in
            return ((sender, cmd) :: rest) )
          else return []
        in
        let%map cmds = go size in
        (initial_nonces, initial_balances, cmds)
      in
      let shrinker :
          ( Account_nonce.t list
          * Currency.Amount.t list
          * (int * User_command.With_valid_signature.t) list )
          Quickcheck.Shrinker.t =
        Quickcheck.Shrinker.create
          (fun (initial_nonces, initial_balances, cmds) ->
            Sequence.singleton
              ( initial_nonces
              , initial_balances
              , List.take cmds (List.length cmds - 1) ) )
      in
      Quickcheck.test gen
        ~sexp_of:
          [%sexp_of:
            Account_nonce.t list
            * Currency.Amount.t list
            * (int * User_command.With_valid_signature.t) list] ~shrinker
        ~shrink_attempts:`Exhaustive ~seed:(`Deterministic "d")
        ~sizes:(Sequence.repeat 10)
        ~f:(fun (initial_nonces, initial_balances, cmds) ->
          let balances = Array.of_list initial_balances in
          let nonces = Array.of_list initial_nonces in
          let pool = ref empty in
          let rec go cmds_acc =
            match cmds_acc with
            | [] ->
                ()
            | (sender, cmd) :: rest -> (
                (* sanity check for the generator *)
                [%test_eq: Public_key.Compressed.t]
                  (Public_key.compress @@ test_keys.(sender).public_key)
                  (cmd |> User_command.forget_check |> User_command.sender) ;
                let add_res =
                  add_from_gossip_exn !pool cmd nonces.(sender)
                    balances.(sender)
                in
                match add_res with
                | Ok (pool', dropped) ->
                    [%test_eq: User_command.With_valid_signature.t Sequence.t]
                      dropped Sequence.empty ;
                    assert_invariants pool' ;
                    pool := pool' ;
                    go rest
                | Error `Invalid_nonce ->
                    failwith "bad nonce"
                | Error `Insufficient_funds ->
                    failwith "insufficient funds"
                | Error `Insufficient_replace_fee ->
                    failwith "insufficient replace fee"
                | Error `Overflow ->
                    failwith "overflow" )
          in
          go cmds )

    let%test_unit "replacement" =
      let gen :
          ( Account_nonce.t
          * Currency.Amount.t
          * User_command.With_valid_signature.t list
          * User_command.With_valid_signature.t )
          Quickcheck.Generator.t =
        let open Quickcheck.Generator.Let_syntax in
        let%bind sender_index = Int.gen_incl 0 9 in
        let sender = test_keys.(sender_index) in
        let%bind init_nonce =
          Quickcheck.Generator.map ~f:Account_nonce.of_int
          @@ Int.gen_incl 0 1000
        in
        let init_balance = Currency.Amount.of_int 100_000 in
        let%bind size = Quickcheck.Generator.size in
        let%bind amounts = gen_currency_division (size + 1) init_balance in
        let rec go current_nonce current_balance n =
          if n > 0 then
            let%bind cmd =
              let key_gen =
                Quickcheck.Generator.tuple2 (return sender)
                  (Quickcheck_lib.of_array test_keys)
              in
              User_command.Gen.payment ~sign_type:`Fake ~key_gen
                ~nonce:current_nonce ~max_amount:1 ~max_fee:0 ()
            in
            let cmd_currency = amounts.(n - 1) in
            let%bind fee =
              Currency.Amount.(gen_incl zero (min (of_int 10) cmd_currency))
            in
            let amount =
              Option.value_exn Currency.Amount.(cmd_currency - fee)
            in
            let modified_payload : User_command.Payload.t =
              match cmd.payload.body with
              | Payment {receiver; _} ->
                  { common=
                      {cmd.payload.common with fee= Currency.Amount.to_fee fee}
                  ; body= User_command.Payload.Body.Payment {receiver; amount}
                  }
              | _ ->
                  failwith "generated user command that wasn't a payment"
            in
            let cmd' =
              User_command.For_tests.fake_sign sender modified_payload
            in
            let consumed = Option.value_exn (currency_consumed cmd') in
            let%map rest =
              go
                (Account_nonce.succ current_nonce)
                (Option.value_exn Currency.Amount.(current_balance - consumed))
                (n - 1)
            in
            cmd' :: rest
          else return []
        in
        let%bind setup_cmds = go init_nonce init_balance (size + 1) in
        let init_nonce_int = Account.Nonce.to_int init_nonce in
        let%bind replaced_nonce =
          Int.gen_incl init_nonce_int
            (init_nonce_int + List.length setup_cmds - 1)
        in
        let%map replace_cmd_skeleton =
          let key_gen =
            Quickcheck.Generator.tuple2 (return sender)
              (Quickcheck_lib.of_array test_keys)
          in
          User_command.Gen.payment ~sign_type:`Fake ~key_gen
            ~nonce:(Account_nonce.of_int replaced_nonce)
            ~max_amount:(Currency.Amount.to_int init_balance)
            ~max_fee:0 ()
        in
        let replace_cmd_payload =
          { replace_cmd_skeleton.payload with
            common=
              { replace_cmd_skeleton.payload.common with
                fee= Currency.Fee.of_int (10 + (5 * (size + 1))) } }
        in
        let replace_cmd =
          User_command.For_tests.fake_sign sender replace_cmd_payload
        in
        (init_nonce, init_balance, setup_cmds, replace_cmd)
      in
      Quickcheck.test gen
        ~sexp_of:
          [%sexp_of:
            Account_nonce.t
            * Currency.Amount.t
            * User_command.With_valid_signature.t list
            * User_command.With_valid_signature.t]
        ~f:(fun (init_nonce, init_balance, setup_cmds, replace_cmd) ->
          let t =
            List.fold_left setup_cmds ~init:empty ~f:(fun t cmd ->
                match add_from_gossip_exn t cmd init_nonce init_balance with
                | Ok (t', removed) ->
                    [%test_eq: User_command.With_valid_signature.t Sequence.t]
                      removed Sequence.empty ;
                    t'
                | _ ->
                    failwith
                    @@ sprintf
                         !"adding command %{sexp: \
                           User_command.With_valid_signature.t} failed"
                         cmd )
          in
          let replaced_idx =
            Account_nonce.to_int
              (replace_cmd |> User_command.forget_check |> User_command.nonce)
            - Account_nonce.to_int
                ( List.hd_exn setup_cmds |> User_command.forget_check
                |> User_command.nonce )
          in
          let currency_consumed_pre_replace =
            List.fold_left
              (List.take setup_cmds (replaced_idx + 1))
              ~init:Currency.Amount.zero
              ~f:(fun consumed_so_far cmd ->
                Option.value_exn
                  Option.(
                    currency_consumed cmd
                    >>= fun consumed ->
                    Currency.Amount.(consumed + consumed_so_far)) )
          in
          assert (
            Currency.Amount.(currency_consumed_pre_replace <= init_balance) ) ;
          let currency_consumed_post_replace =
            Option.value_exn
              (let open Option.Let_syntax in
              let%bind replaced_currency_consumed =
                currency_consumed @@ List.nth_exn setup_cmds replaced_idx
              in
              let%bind replacer_currency_consumed =
                currency_consumed replace_cmd
              in
              let%bind a =
                Currency.Amount.(
                  currency_consumed_pre_replace - replaced_currency_consumed)
              in
              Currency.Amount.(a + replacer_currency_consumed))
          in
          let add_res =
            add_from_gossip_exn t replace_cmd init_nonce init_balance
          in
          if Currency.Amount.(currency_consumed_post_replace <= init_balance)
          then
            match add_res with
            | Ok (t', dropped) ->
                assert (not (Sequence.is_empty dropped)) ;
                assert_invariants t'
            | Error _ ->
                failwith "adding command failed"
          else
            match add_res with
            | Error `Insufficient_funds ->
                ()
            | _ ->
                failwith "should've returned nsf" )
  end )
