open Core
open Async
open Coda_worker
open Coda_inputs
open Coda_base

let name = "coda-delegation-test"

let logger = Logger.create ()

let heartbeat_flag = ref true

let print_heartbeat () =
  let rec loop () =
    if !heartbeat_flag then (
      Logger.warn logger ~module_:__MODULE__ ~location:__LOC__
        "Heartbeat for CI" ;
      let%bind () = after (Time.Span.of_min 1.) in
      loop () )
    else return ()
  in
  loop ()

let main () =
  let num_proposers = 3 in
  let snark_work_public_keys ndx =
    List.nth_exn Genesis_ledger.accounts ndx
    |> fun (_, acct) -> Some (Account.public_key acct)
  in
  let%bind testnet =
    Coda_worker_testnet.test logger num_proposers Option.some
      snark_work_public_keys Cli_lib.Arg_type.Seq
      ~max_concurrent_connections:None
  in
  Logger.info logger ~module_:__MODULE__ ~location:__LOC__ "Started test net" ;
  (* keep CI alive *)
  Deferred.don't_wait_for (print_heartbeat ()) ;
  (* dump account info to log *)
  List.iteri Genesis_ledger.accounts (fun ndx ((_, acct) as record) ->
      let keypair = Genesis_ledger.keypair_of_account_record_exn record in
      Logger.info logger ~module_:__MODULE__ ~location:__LOC__
        !"Account: %i private key: %{sexp: Import.Private_key.t} public key: \
          %{sexp: Account.key} balance: %{sexp: Currency.Balance.t}"
        ndx keypair.private_key (Account.public_key acct) acct.balance ) ;
  (* second account is delegator; see genesis_ledger/test_delegation_ledger.ml *)
  let ((_, delegator_account) as delegator) =
    List.nth_exn Genesis_ledger.accounts 2
  in
  let delegator_pubkey = Account.public_key delegator_account in
  let delegator_keypair =
    Genesis_ledger.keypair_of_account_record_exn delegator
  in
  (* zeroth account is delegatee *)
  let ((_, delegatee_account) as delegatee) =
    List.nth_exn Genesis_ledger.accounts 0
  in
  let delegatee_pubkey = Account.public_key delegatee_account in
  let worker = testnet.workers.(0) in
  (* setup readers for proposals by delegator, delegatee *)
  let%bind delegator_transition_reader =
    Coda_process.new_block_exn worker delegator_pubkey
  in
  (* delegator's transition reader will fill this ivar when it has seen a few blocks *)
  let delegator_ivar : unit Ivar.t = Ivar.create () in
  (* once the delegatee starts proposing, the delegator should
     no longer be proposing
  *)
  let delegatee_has_proposed = ref false in
  let delegator_proposal_count = ref 0 in
  let delegator_proposal_goal = 30 in
  Deferred.don't_wait_for
    (Pipe_lib.Linear_pipe.iter delegator_transition_reader
       ~f:(fun {With_hash.data= transition; _} ->
         assert (
           Signature_lib.Public_key.Compressed.equal transition.creator
             delegator_pubkey ) ;
         Logger.info logger ~module_:__MODULE__ ~location:__LOC__
           "Observed delegator proposal" ;
         assert (not !delegatee_has_proposed) ;
         incr delegator_proposal_count ;
         if Int.equal !delegator_proposal_count delegator_proposal_goal then
           Ivar.fill delegator_ivar () ;
         return () )) ;
  Logger.info logger ~module_:__MODULE__ ~location:__LOC__
    "Started delegator transition reader" ;
  let%bind delegatee_transition_reader =
    Coda_process.new_block_exn worker delegatee_pubkey
  in
  let delegatee_proposal_count = ref 0 in
  (* delegatee's transition reader will fill this ivar when it has seen a few blocks *)
  let delegatee_ivar : unit Ivar.t = Ivar.create () in
  (* how many blocks we should wait for from the delegatee *)
  let delegatee_proposal_goal = 10 in
  Deferred.don't_wait_for
    (Pipe_lib.Linear_pipe.iter delegatee_transition_reader
       ~f:(fun {With_hash.data= transition; _} ->
         assert (
           Signature_lib.Public_key.Compressed.equal transition.creator
             delegatee_pubkey ) ;
         Logger.info logger ~module_:__MODULE__ ~location:__LOC__
           "Observed delegatee proposal" ;
         delegatee_has_proposed := true ;
         incr delegatee_proposal_count ;
         if Int.equal !delegatee_proposal_count delegatee_proposal_goal then
           Ivar.fill delegatee_ivar () ;
         return () )) ;
  Logger.info logger ~module_:__MODULE__ ~location:__LOC__
    "Started delegatee transition reader" ;
  (* wait for delegator to propose some blocks *)
  let%bind () = Ivar.read delegator_ivar in
  assert (Int.equal !delegatee_proposal_count 0) ;
  Logger.info logger ~module_:__MODULE__ ~location:__LOC__
    "Before delegation, got %i proposals from delegator (and none from \
     delegatee)"
    !delegator_proposal_count ;
  let%bind () =
    Coda_worker_testnet.Delegation.delegate_stake testnet ~node:0
      ~delegator:delegator_keypair.private_key ~delegatee:delegatee_pubkey
  in
  Logger.info logger ~module_:__MODULE__ ~location:__LOC__
    "Ran delegation command" ;
  (* wait for delegatee to propose a few blocks *)
  let%bind () = Ivar.read delegatee_ivar in
  Logger.info logger ~module_:__MODULE__ ~location:__LOC__
    "Saw %i blocks proposed by delegatee" !delegatee_proposal_count ;
  heartbeat_flag := false ;
  Coda_worker_testnet.Api.teardown testnet

let command =
  let open Command.Let_syntax in
  Command.async
    ~summary:
      "Test whether stake delegation from a high-balance account to a \
       low-balance account works"
    (Command.Param.return main)
