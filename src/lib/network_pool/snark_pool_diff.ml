open Core_kernel
open Async_kernel
open Module_version

module Diff = struct
  module Stable = struct
    module V1 = struct
      module T = struct
        type ('work, 'proof) t =
          | Add_solved_work of
              'work * 'proof Snark_pool.Priced_proof.Stable.V1.t
        [@@deriving bin_io, sexp, yojson, version]
      end

      include T
    end

    module Latest = V1
  end

  type ('work, 'proof) t = ('work, 'proof) Stable.Latest.t =
    | Add_solved_work of 'work * 'proof Snark_pool.Priced_proof.Stable.V1.t
  [@@deriving sexp, yojson]
end

module Make (Ledger_proof : sig
  type t [@@deriving bin_io, sexp, yojson, version]
end) (Work : sig
  type t [@@deriving sexp]

  module Stable :
    sig
      module V1 : sig
        type t [@@deriving sexp, bin_io, yojson, version]
      end
    end
    with type V1.t = t
end)
(Transition_frontier : T)
(Pool : Snark_pool.S
        with type work := Work.t
         and type transition_frontier := Transition_frontier.t
         and type ledger_proof := Ledger_proof.t) =
struct
  module Stable = struct
    module V1 = struct
      module T = struct
        type t = (Work.Stable.V1.t, Ledger_proof.t list) Diff.Stable.V1.t
        [@@deriving bin_io, sexp, yojson, version]
      end

      include T
      include Registration.Make_latest_version (T)
    end

    module Latest = V1

    module Module_decl = struct
      let name = "snark_pool_diff"

      type latest = Latest.t
    end

    module Registrar = Registration.Make (Module_decl)
    module Registered_V1 = Registrar.Register (V1)
  end

  (* bin_io omitted *)
  type t = Stable.Latest.t [@@deriving sexp, yojson]

  let summary = function
    | Diff.Add_solved_work (_, {proof= _; fee}) ->
        Printf.sprintf
          !"Snark_pool_diff add with fee %{sexp: Coda_base.Fee_with_prover.t}"
          fee

  let apply (pool : Pool.t) (t : t Envelope.Incoming.t) :
      t Or_error.t Deferred.t =
    let t = Envelope.Incoming.data t in
    let to_or_error = function
      | `Don't_rebroadcast ->
          Or_error.error_string "Worse fee or already in pool"
      | `Rebroadcast ->
          Ok t
    in
    ( match t with
    | Add_solved_work (work, {proof; fee}) ->
        Pool.add_snark pool ~work ~proof ~fee )
    |> to_or_error |> Deferred.return
end

include Make (Ledger_proof.Stable.V1) (Transaction_snark_work.Statement)
          (Transition_frontier)
          (Snark_pool)
