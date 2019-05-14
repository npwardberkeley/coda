[%%import
"../../config.mlh"]

module Bignum_bigint = Bigint
open Core_kernel
open Snarky

module type Message_intf = sig
  type boolean_var
  type curve_scalar
  type curve_scalar_var
  type (_, _) checked
  type t
  type var
  val hash : t -> nonce:bool list -> curve_scalar
  val hash_checked :
    var -> nonce:boolean_var list -> (curve_scalar_var, _) checked
end

module type S = sig
  type boolean_var
  type curve
  type curve_var
  type curve_scalar
  type curve_scalar_var
  type (_, _) checked
  type (_, _) typ
  module Shifted : sig
    module type S =
      Curves.Shifted_intf
      with type curve_var := curve_var
       and type boolean_var := boolean_var
       and type ('a, 'b) checked := ('a, 'b) checked
  end

  module Message :
    Message_intf
    with type boolean_var := boolean_var
     and type curve_scalar := curve_scalar
     and type curve_scalar_var := curve_scalar_var
     and type ('a, 'b) checked := ('a, 'b) checked

  module Signature : sig
    type t = curve_scalar * curve_scalar [@@deriving sexp]
    type var = curve_scalar_var * curve_scalar_var
    val typ : (var, t) typ
  end

  module Private_key : sig
    type t = curve_scalar
    val to_bits : t -> bool list
  end

  module Public_key : sig
    type t = curve
    type var = curve_var
  end

  module Checked : sig
    val compress : curve_var -> (boolean_var list, _) checked
    val verification_hash :
         (module Shifted.S with type t = 't)
      -> Signature.var
      -> Public_key.var
      -> Message.var
      -> (curve_scalar_var, _) checked

    val verifies :
         (module Shifted.S with type t = 't)
      -> Signature.var
      -> Public_key.var
      -> Message.var
      -> (boolean_var, _) checked

    val assert_verifies :
         (module Shifted.S with type t = 't)
      -> Signature.var
      -> Public_key.var
      -> Message.var
      -> (unit, _) checked
  end

  val compress : curve -> bool list
  val sign : Private_key.t -> Message.t -> Signature.t
  val shamir_sum : curve_scalar * curve -> curve_scalar * curve -> curve
  val verify : Signature.t -> Public_key.t -> Message.t -> bool
end

module Schnorr
    (Impl : Snark_intf.S) (Curve : sig
        open Impl
        module Scalar : sig
          type t [@@deriving sexp, eq]
          type var
          val typ : (var, t) Typ.t
          val order : t
          val random : unit -> t
          val ( * ) : t -> t -> t
          val ( - ) : t -> t -> t
          val test_bit : t -> int -> bool
          val length_in_bits : int
          module Checked : sig
            val equal : var -> var -> (Boolean.var, _) Checked.t
            val to_bits :
              var -> Boolean.var Bitstring_lib.Bitstring.Lsb_first.t
            module Assert : sig
              val equal : var -> var -> (unit, _) Checked.t
            end
          end
        end

        type t [@@deriving eq]

        type var = Field.Var.t * Field.Var.t

        module Checked :
          Curves.Weierstrass_checked_intf
          with module Impl := Impl
           and type t := t
           and type var := var
        (* why are these here instead of above? *)
        val one : t
        val zero : t
        val add : t -> t -> t
        val double : t -> t
        val scale : t -> Scalar.t -> t
        val to_affine_coordinates : t -> Field.t * Field.t
    end)
    (Message : Message_intf
               with type boolean_var := Impl.Boolean.var
                and type curve_scalar_var := Curve.Scalar.var
                and type curve_scalar := Curve.Scalar.t
                and type ('a, 'b) checked := ('a, 'b) Impl.Checked.t) :
  S
  with type boolean_var := Impl.Boolean.var
   and type curve := Curve.t
   and type curve_var := Curve.var
   and type curve_scalar := Curve.Scalar.t
   and type curve_scalar_var := Curve.Scalar.var
   and type ('a, 'b) checked := ('a, 'b) Impl.Checked.t
   and type ('a, 'b) typ := ('a, 'b) Impl.Typ.t
   and module Shifted := Curve.Checked.Shifted
   and module Message := Message = struct
  open Impl

  module Signature = struct
    type 'a t_ = 'a * 'a [@@deriving sexp]
    type var = Curve.Scalar.var t_
    type t = Curve.Scalar.t t_ [@@deriving sexp]
    let typ : (var, t) Typ.t =
      let typ = Curve.Scalar.typ in
      Typ.tuple2 typ typ
  end

  module Private_key = struct
    type t = Curve.Scalar.t
    let to_bits (t : Private_key.t) = 
      Curve.Scalar.to_bits t
  end

  let compress (t : Curve.t) =
    let x, _ = Curve.to_affine_coordinates t in
    Field.unpack x

  let get_y (t : Curve.t) =
    let _, y = Curve.to_affine_coordinates t in
    Field.unpack y

  module Public_key : sig
    type t = Curve.t
    type var = Curve.var
  end =
    Curve

  (* NOTE : do we need this? *)
  (* TODO : Have expect test for this *)
  let shamir_sum ((sp, p) : Curve.Scalar.t * Curve.t)
      ((sq, q) : Curve.Scalar.t * Curve.t) =
    let pq = Curve.add p q in
    let rec go i acc =
      if i < 0 then acc
      else
        let acc = Curve.double acc in
        let acc =
          match (Curve.Scalar.test_bit sp i, Curve.Scalar.test_bit sq i) with
          | true, false ->
              Curve.add p acc
          | false, true ->
              Curve.add q acc
          | true, true ->
              Curve.add pq acc
          | false, false ->
              acc
        in
        go (i - 1) acc
    in
    go (Curve.Scalar.length_in_bits - 1) Curve.zero

 (* Input:
-   The secret key *d*: an integer in the range *1..n-1*.
-   The message *m*: an arbitrary length tryte array
To sign *m* for public key *dG*:
-   Let k' = int(blake2s(bytes(d) || m)) mod n.
-   Fail if k' = 0.
-   Let R = k'G.
-   Let k = k' if y(R) is even, otherwise let k = n - k'.
-   Let e = int(hash(trytes(x(R)) || trytes(dG) || m)) mod n.
-   The signature is bytes(x(R)) || bytes(k + ed mod n).
*)
  let sign (d : Private_key.t) m =
    let is_odd (l : Curve.Scalar.t) : bool = true
      in
    let k_prime = Message.hash ~nonce:(Private_key.to_bits d) m in
    if k_prime = 0 then Error.of_string "k = 0 in Schnorr construction"
    else let r = Curve.(scale one k _prime) in
    let k = if is_odd (get_y r) then k_prime
            else Curve.Scalar.order - k_prime in
    let rx = compress r in
    let e_r = Bits.hash rx Curve.(scale one d) m in
    (* let s = Bits.concat rx Curve.Scalar.(k + (e * d)) in s *)
    let s = Curve.Scalar.(k + (e * d)) in (x.r, s)

(* Input:
-   The public key *pk*: a 96-byte array
-   The message *m*: an arbitrary length tryte array
-   A signature *sig*: a 190-byte array
The signature is valid if and only if the algorithm below does not fail.
-   Let *P = point(pk)*; fail if *point(pk)* fails.
-   Let *r = int(sig\[0:95\])*; fail if *r ≥ p*.
-   Let *s = int(sig\[95:190\])*; fail if *s ≥ n*.
-   Let *e = int(hash(trytes(r) || trytes(P) || m)) mod n*.
-   Let *R = sG - eP*.
-   Fail if *infinite(R)* or *y(R)* is not even or *x(R) ≠ r*.
*)
  let verify ((r, s) : Signature.t) (pk : Public_key.t) (m : Message.t) =
    if Curve.equal Curve.zero pk then false
    else if r > Field.size then false
    else if s > Curve.Scalar.order then false
    else
      (* have to have Curve.trytes and Curve.Scalar.trytes ? *)
      let e = Bits.hash (trytes r) (trytes pk) m in
      let r1 = Curve.(scale one s - scale pk e) in
      if Curve.(equal inf r1) then false
      else if is_odd r1.y then false
      else if Curve.Scalar.equal r r_point.x then true (* ? bad logic flow *)
      else false

  [%%if
  call_logger]

  let verify s pk m =
    Coda_debug.Call_logger.record_call "Signature_lib.Schnorr.verify" ;
    if Random.int 1000 = 0 then (
      print_endline "SCHNORR BACKTRACE:" ;
      Printexc.print_backtrace stdout ) ;
    verify s pk m

  [%%endif]

  module Checked = struct
    let compress ((x, _) : Curve.var) =
      Field.Checked.choose_preimage_var x ~length:Field.size_in_bits

    open Impl.Let_syntax

    let%snarkydef verification_hash (type s)
        ((module Shifted) as shifted :
          (module Curve.Checked.Shifted.S with type t = s))
        ((s, h) : Signature.var) (public_key : Public_key.var)
        (m : Message.var) =
      let%bind pre_r =
        (* s * g + h * public_key *)
        let%bind s_g =
          Curve.Checked.scale_known shifted Curve.one
            (Curve.Scalar.Checked.to_bits s)
            ~init:Shifted.zero
        in
        let%bind s_g_h_pk =
          Curve.Checked.scale shifted public_key
            (Curve.Scalar.Checked.to_bits h)
            ~init:s_g
        in
        Shifted.unshift_nonzero s_g_h_pk
      in
      let%bind r = compress pre_r in
      Message.hash_checked m ~nonce:r

    let%snarkydef verifies shifted ((_, h) as signature) pk m =
      verification_hash shifted signature pk m >>= Curve.Scalar.Checked.equal h

    let%snarkydef assert_verifies shifted ((_, h) as signature) pk m =
      verification_hash shifted signature pk m
      >>= Curve.Scalar.Checked.Assert.equal h
  end
end
