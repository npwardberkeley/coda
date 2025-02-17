open Core_kernel
open Async_kernel
open Pipe_lib

module type Pool_intf = sig
  type t

  type transition_frontier

  val create :
       logger:Logger.t
    -> trust_system:Trust_system.t
    -> frontier_broadcast_pipe:transition_frontier Option.t
                               Broadcast_pipe.Reader.t
    -> t
end

module type Pool_diff_intf = sig
  type pool

  type t [@@deriving sexp]

  val summary : t -> string

  val apply : pool -> t Envelope.Incoming.t -> t Deferred.Or_error.t
end

module type Network_pool_intf = sig
  type t

  type pool

  type pool_diff

  type transition_frontier

  val create :
       logger:Logger.t
    -> trust_system:Trust_system.t
    -> incoming_diffs:pool_diff Envelope.Incoming.t Linear_pipe.Reader.t
    -> frontier_broadcast_pipe:transition_frontier Option.t
                               Broadcast_pipe.Reader.t
    -> t

  val of_pool_and_diffs :
       pool
    -> logger:Logger.t
    -> incoming_diffs:pool_diff Envelope.Incoming.t Linear_pipe.Reader.t
    -> t

  val pool : t -> pool

  val broadcasts : t -> pool_diff Linear_pipe.Reader.t

  val apply_and_broadcast :
    t -> pool_diff Envelope.Incoming.t -> unit Deferred.t
end

module Snark_pool_diff = Snark_pool_diff

module Make
    (Transition_frontier : T)
    (Pool : Pool_intf with type transition_frontier := Transition_frontier.t)
    (Pool_diff : Pool_diff_intf with type pool := Pool.t) :
  Network_pool_intf
  with type pool := Pool.t
   and type pool_diff := Pool_diff.t
   and type transition_frontier := Transition_frontier.t = struct
  type t =
    { pool: Pool.t
    ; logger: Logger.t
    ; write_broadcasts: Pool_diff.t Linear_pipe.Writer.t
    ; read_broadcasts: Pool_diff.t Linear_pipe.Reader.t }

  let pool {pool; _} = pool

  let broadcasts {read_broadcasts; _} = read_broadcasts

  let apply_and_broadcast t pool_diff =
    match%bind Pool_diff.apply t.pool pool_diff with
    | Ok diff' ->
        Logger.trace t.logger ~module_:__MODULE__ ~location:__LOC__
          "Broadcasting %s" (Pool_diff.summary diff') ;
        Linear_pipe.write t.write_broadcasts diff'
    | Error e ->
        Logger.info t.logger ~module_:__MODULE__ ~location:__LOC__
          "Pool diff apply feedback: %s" (Error.to_string_hum e) ;
        Deferred.unit

  let of_pool_and_diffs pool ~logger ~incoming_diffs =
    let read_broadcasts, write_broadcasts = Linear_pipe.create () in
    let network_pool = {pool; logger; read_broadcasts; write_broadcasts} in
    Linear_pipe.iter incoming_diffs ~f:(fun diff ->
        apply_and_broadcast network_pool diff )
    |> ignore ;
    network_pool

  let create ~logger ~trust_system ~incoming_diffs ~frontier_broadcast_pipe =
    of_pool_and_diffs
      (Pool.create ~logger ~trust_system ~frontier_broadcast_pipe)
      ~logger ~incoming_diffs
end

let%test_module "network pool test" =
  ( module struct
    module Int = struct
      include Int

      let to_yojson x = `Int x

      let of_yojson = function `Int x -> Ok x | _ -> Error "expected `Int"
    end

    module Mock_proof = struct
      module Stable = struct
        module V1 = struct
          module T = struct
            type t = int
            [@@deriving bin_io, sexp, yojson, version {unnumbered}]
          end

          include T
        end
      end

      include Stable.V1.T
    end

    module Mock_work = struct
      module T = struct
        type t = Int.t [@@deriving sexp, hash, compare, yojson]

        let gen = Int.quickcheck_generator
      end

      include T
      include Hashable.Make (T)

      module Stable = struct
        module V1 = struct
          module T = struct
            type t = int
            [@@deriving
              bin_io, sexp, yojson, hash, compare, version {unnumbered}]
          end

          include T
          module Table = Int.Table
          module Hash_queue = Int.Hash_queue
          module Hash_set = Int.Hash_set

          let hashable = Int.hashable
        end
      end
    end

    module Mock_transition_frontier = struct
      type t = Int.t

      let create () : t = 0

      module Extensions = struct
        module Work = Mock_work
      end

      let snark_pool_refcount_pipe _ =
        let reader, _writer =
          Pipe_lib.Broadcast_pipe.create (0, Extensions.Work.Table.create ())
        in
        reader
    end

    let trust_system = Trust_system.null ()

    module Mock_snark_pool =
      Snark_pool.Make (Mock_proof) (Mock_work) (Mock_transition_frontier)
    module Mock_snark_pool_diff =
      Snark_pool_diff.Make (Mock_proof) (Mock_work) (Int) (Mock_snark_pool)
    module Mock_network_pool =
      Make (Mock_transition_frontier) (Mock_snark_pool) (Mock_snark_pool_diff)

    let%test_unit "Work that gets fed into apply_and_broadcast will be \
                   received in the pool's reader" =
      let pool_reader, _pool_writer = Linear_pipe.create () in
      let frontier_broadcast_pipe_r, _ =
        Broadcast_pipe.create (Some (Mock_transition_frontier.create ()))
      in
      let network_pool =
        Mock_network_pool.create ~logger:(Logger.null ()) ~trust_system
          ~incoming_diffs:pool_reader
          ~frontier_broadcast_pipe:frontier_broadcast_pipe_r
      in
      let work = 1 in
      let priced_proof =
        { Snark_pool.Priced_proof.proof= []
        ; fee=
            { fee= Currency.Fee.of_int 0
            ; prover= Signature_lib.Public_key.Compressed.empty } }
      in
      let command =
        Snark_pool_diff.Diff.Add_solved_work (work, priced_proof)
      in
      (fun () ->
        don't_wait_for
        @@ Linear_pipe.iter (Mock_network_pool.broadcasts network_pool)
             ~f:(fun _ ->
               let pool = Mock_network_pool.pool network_pool in
               ( match Mock_snark_pool.request_proof pool 1 with
               | Some {proof; fee= _} ->
                   assert (proof = priced_proof.proof)
               | None ->
                   failwith "There should have been a proof here" ) ;
               Deferred.unit ) ;
        Mock_network_pool.apply_and_broadcast network_pool
          (Envelope.Incoming.local command) )
      |> Async.Thread_safe.block_on_async_exn

    let%test_unit "when creating a network, the incoming diffs in reader pipe \
                   will automatically get process" =
      let works = List.range 0 10 in
      let verify_unsolved_work () =
        let work_diffs =
          List.map works ~f:(fun work ->
              Envelope.Incoming.local
                (Snark_pool_diff.Diff.Add_solved_work
                   ( work
                   , Snark_pool.Priced_proof.
                       { proof= []
                       ; fee=
                           { fee= Currency.Fee.of_int 0
                           ; prover= Signature_lib.Public_key.Compressed.empty
                           } } )) )
          |> Linear_pipe.of_list
        in
        let frontier_broadcast_pipe_r, _ =
          Broadcast_pipe.create (Some (Mock_transition_frontier.create ()))
        in
        let network_pool =
          Mock_network_pool.create ~logger:(Logger.null ()) ~trust_system
            ~incoming_diffs:work_diffs
            ~frontier_broadcast_pipe:frontier_broadcast_pipe_r
        in
        don't_wait_for
        @@ Linear_pipe.iter (Mock_network_pool.broadcasts network_pool)
             ~f:(fun work_command ->
               let work =
                 match work_command with
                 | Snark_pool_diff.Diff.Add_solved_work (work, _) ->
                     work
               in
               assert (List.mem works work ~equal:( = )) ;
               Deferred.unit ) ;
        Deferred.unit
      in
      verify_unsolved_work |> Async.Thread_safe.block_on_async_exn
  end )
