(* OCaml harness for the extracted validator. *)
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

(* Baseline right-leading pose. *)
let pose_right =
  {
    lead = Right;
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

(* Simple two-pose sequence. *)
let demo_seq = Cons (pose_left, Cons (pose_right, Nil))

(* Offset pose to test continuity bounds. *)
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

(* Sequence with larger offset. *)
let demo_seq_offset = Cons (pose_left, Cons (pose_right_offset, Nil))

(* Run validator with a specific bound. *)
let print_bounded label b seq =
  let bz = z_of_int b in
  let ok_k = validate_sequence_bounded_default bz seq in
  let ok_fp = validate_sequence_footpos_bounded_default bz seq in
  print_endline
    (label ^ " b=" ^ string_of_int b
     ^ " kinematic=" ^ string_of_bool ok_k
     ^ " footpos=" ^ string_of_bool ok_fp)

(* Demo outputs. *)
let () =
  let ok = validate_sequence demo_seq in
  let ok_fp = validate_sequence_footpos demo_seq in
  print_endline ("moonwalk_demo_valid=" ^ string_of_bool ok);
  print_endline ("moonwalk_demo_footpos_valid=" ^ string_of_bool ok_fp);
  print_bounded "demo_seq" 0 demo_seq;
  print_bounded "demo_seq" 10 demo_seq;
  print_bounded "demo_seq_offset" 0 demo_seq_offset;
  print_bounded "demo_seq_offset" 10 demo_seq_offset
