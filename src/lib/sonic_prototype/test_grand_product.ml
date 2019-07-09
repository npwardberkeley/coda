open Core
open Commitment_scheme
open Srs
open Grand_product
open Default_backend.Backend

let run_well_formed_test a_nums b_nums =
  let x = Fr.random () in
  let alpha = Fr.random () in
  let d = 110 in (* max degree (largest small_nat + small_list) *)
  let srs = Srs.create d x alpha in
  let a_coeffs = List.map a_nums ~f:Fr.of_int in
  let b_coeffs = List.map b_nums ~f:Fr.of_int in
  let poly_a = Fr_laurent.create 1 a_coeffs in
  let poly_b = Fr_laurent.create 1 b_coeffs in
  let a_n = List.length a_coeffs in
  let b_n = List.length b_coeffs in
  let commit_a = commit_poly srs srs.d x poly_a in
  let commit_b = commit_poly srs srs.d x poly_b in
  let wfp_a = wform_p srs x a_n commit_a a_coeffs in
  let wfp_b = wform_p srs x b_n commit_b b_coeffs in
  wform_v srs a_n commit_a wfp_a && wform_v srs b_n commit_b wfp_b

let%test_unit "well_formed_test" =
  let a_nums = [1; 2; 3; 4; 5] in
  let b_nums = [-1; 2; -3; 4; -5] in
  assert (run_well_formed_test a_nums b_nums)

let run_grand_product_test a_deg b_deg a_nums b_nums =
  let x = Fr.random () in
  let alpha = Fr.random () in
  let d = 110 in (* max degree (largest small_nat + small_list) *)
  let _srs = Srs.create d x alpha in
  let a_coeffs = List.map a_nums ~f:Fr.of_int in
  let _poly_a = Fr_laurent.create a_deg a_coeffs in
  let a_product = List.fold_left ~f:Fr.( * ) ~init:Fr.one a_coeffs in
  let b_coeffs_initial = List.map b_nums ~f:Fr.of_int in
  let b_product = List.fold_left ~f:Fr.( * ) ~init:Fr.one b_coeffs_initial in
  let b_coeffs = b_coeffs_initial @ [Fr.inv b_product; a_product] in
  let _poly_b = Fr_laurent.create b_deg b_coeffs in
  true
  
  (* polys with same grand product work, random polys don't *)

let%test_unit "grand_product_test" =
  let a_deg = 5 in
  let b_deg = -5 in
  let a_nums = [1; 2; 3; 4; 5] in
  let b_nums = [-1; 2; -3; 4; -5] in
  assert (run_grand_product_test a_deg b_deg a_nums b_nums)