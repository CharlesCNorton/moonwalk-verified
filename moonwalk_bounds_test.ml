(* Bound sensitivity test for the extracted validator. *)
open Moonwalk_validator

(* Convert positive int to Coq positive. *)
let rec pos_of_int n =
  if n <= 0 then invalid_arg "pos_of_int expects n > 0"
  else if n = 1 then XH
  else if n land 1 = 0 then XO (pos_of_int (n / 2))
  else XI (pos_of_int (n / 2))

(* Convert int to Coq Z. *)
let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (pos_of_int n)
  else Zneg (pos_of_int (-n))

(* Render Coq bool to string. *)
let string_of_bool = function
  | True -> "true"
  | False -> "false"

(* Baseline left-leading pose. *)
let pose_left =
  {
    lead = Left;
    phase_lead = Flat;
    phase_trail = Toe;
    mu_lead = z_of_int 200;
    mu_trail = z_of_int 800;
    com_delta = z_of_int (-3);
    lead_rel = z_of_int 2;
    trail_rel = z_of_int 3;
    heel_lead = z_of_int 0;
    heel_trail = z_of_int 1;
    toe_lead = z_of_int 0;
    toe_trail = z_of_int 0;
    dt_ms = z_of_int 100;
  }

(* Offset right-leading pose. *)
let pose_right_offset =
  {
    lead = Right;
    phase_lead = Flat;
    phase_trail = Toe;
    mu_lead = z_of_int 200;
    mu_trail = z_of_int 800;
    com_delta = z_of_int (-8);
    lead_rel = z_of_int 2;
    trail_rel = z_of_int 8;
    heel_lead = z_of_int 0;
    heel_trail = z_of_int 1;
    toe_lead = z_of_int 0;
    toe_trail = z_of_int 0;
    dt_ms = z_of_int 100;
  }

(* Two-pose sequence with offset. *)
let seq_offset = Cons (pose_left, Cons (pose_right_offset, Nil))

(* Fail fast with message. *)
let fail msg =
  prerr_endline ("FAIL: " ^ msg);
  exit 1

(* Monotonicity guard: larger bounds should not reject. *)
let assert_monotone label small large =
  match (small, large) with
  | True, False -> fail (label ^ " violated monotonicity")
  | _ -> ()

(* Execute bound comparisons. *)
let () =
  let b0 = z_of_int 0 in
  let b10 = z_of_int 10 in

  let k0 = validate_sequence_bounded_default b0 seq_offset in
  let k10 = validate_sequence_bounded_default b10 seq_offset in
  let f0 = validate_sequence_footpos_bounded_default b0 seq_offset in
  let f10 = validate_sequence_footpos_bounded_default b10 seq_offset in

  print_endline ("kinematic b0=" ^ string_of_bool k0 ^ " b10=" ^ string_of_bool k10);
  print_endline ("footpos  b0=" ^ string_of_bool f0 ^ " b10=" ^ string_of_bool f10);

  assert_monotone "kinematic" k0 k10;
  assert_monotone "footpos" f0 f10
