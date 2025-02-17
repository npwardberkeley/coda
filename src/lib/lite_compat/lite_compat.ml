open Core
include Lite_compat_algebra

let verification_key vk =
  let open Crypto_params.Tock_backend.Full.GM_verification_key_accessors in
  let g_alpha = g_alpha vk |> g1 in
  let h_beta = h_beta vk |> g2 in
  let g_alpha_h_beta = LTock.Pairing.reduced_pairing g_alpha h_beta in
  { LTock.Groth_maller.Verification_key.h= h vk |> g2
  ; g_alpha
  ; h_beta
  ; g_alpha_h_beta
  ; g_gamma= g_gamma vk |> g1
  ; h_gamma= h_gamma vk |> g2
  ; query= query vk |> g1_vector }

let proof proof : LTock.Groth_maller.Proof.t =
  let module P = Crypto_params.Tock_backend.Full.GM_proof_accessors in
  {a= P.a proof |> g1; b= P.b proof |> g2; c= P.c proof |> g1}

let merkle_path :
       Coda_base.Ledger.Path.t
    -> [ `Left of Lite_base.Pedersen.Digest.t
       | `Right of Lite_base.Pedersen.Digest.t ]
       list =
  let f (e : Coda_base.Ledger.Path.elem) =
    match e with
    | `Left h ->
        `Left (digest (h :> Tick.Pedersen.Digest.t))
    | `Right h ->
        `Right (digest (h :> Tick.Pedersen.Digest.t))
  in
  List.map ~f

let public_key ({x; is_odd} : Signature_lib.Public_key.Compressed.t) :
    Lite_base.Public_key.Compressed.t =
  {x= field x; is_odd}

let length =
  Fn.compose Lite_base.Length.t_of_sexp Coda_numbers.Length.sexp_of_t

let account_nonce : Coda_base.Account.Nonce.t -> Lite_base.Account.Nonce.t =
  Fn.compose Lite_base.Account.Nonce.t_of_sexp
    Coda_base.Account.Nonce.sexp_of_t

let balance : Currency.Balance.t -> Lite_base.Account.Balance.t =
  Fn.compose Lite_base.Account.Balance.t_of_sexp Currency.Balance.sexp_of_t

let voting_for : Coda_base.State_hash.t -> Lite_base.State_hash.t =
  Fn.compose Lite_base.State_hash.t_of_sexp Coda_base.State_hash.sexp_of_t

let time : Coda_base.Block_time.t -> Lite_base.Block_time.t =
  Fn.compose Lite_base.Block_time.t_of_sexp Coda_base.Block_time.sexp_of_t

let account (account : Coda_base.Account.value) : Lite_base.Account.t =
  { public_key= public_key account.public_key
  ; nonce= account_nonce account.nonce
  ; balance= balance account.balance
  ; delegate= public_key account.delegate
  ; receipt_chain_hash=
      digest (account.receipt_chain_hash :> Tick.Pedersen.Digest.t)
  ; voting_for= voting_for account.voting_for }

let ledger_hash (h : Coda_base.Ledger_hash.t) : Lite_base.Ledger_hash.t =
  digest (h :> Tick.Pedersen.Digest.t)

let frozen_ledger_hash (h : Coda_base.Frozen_ledger_hash.t) :
    Lite_base.Ledger_hash.t =
  digest (h :> Tick.Pedersen.Digest.t)

let ledger_builder_hash (h : Staged_ledger_hash.t) =
  { Lite_base.Staged_ledger_hash.ledger_hash=
      ledger_hash (Staged_ledger_hash.ledger_hash h)
  ; aux_hash= Staged_ledger_hash.(Aux_hash.to_bytes (aux_hash h)) }

let blockchain_state
    ({staged_ledger_hash= lbh; snarked_ledger_hash= lh; timestamp} :
      Coda_state.Blockchain_state.Value.t) : Lite_base.Blockchain_state.t =
  { staged_ledger_hash= ledger_builder_hash lbh
  ; ledger_hash= frozen_ledger_hash lh
  ; timestamp= time timestamp }
