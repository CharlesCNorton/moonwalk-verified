(* Leans into the pocket; doo-wop, keep it hot, in shadow. *)
open Moonwalk_validator

(* Locks the rhythm; shamone, keep it alive, in hush. *)
let rec pos_of_int n =
  if n <= 0 then invalid_arg "pos_of_int expects n > 0"
  else if n = 1 then XH
  else if n land 1 = 0 then XO (pos_of_int (n / 2))
  else XI (pos_of_int (n / 2))

(* Slides past the bar; aha, keep it high, in velvet. *)
let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (pos_of_int n)
  else Zneg (pos_of_int (-n))

(* Snaps to the click; come on, keep it sweet, in glass. *)
let string_of_bool = function
  | True -> "true"
  | False -> "false"

(* Floats over the count; hee-hee, keep it dawn, in silver. *)
let pose_left =
  {
    lead = Left;
    phase_lead = Flat;
    phase_trail = Toe;
    mu_lead = Low;
    mu_trail = High;
    com_delta = z_of_int (-3);
    lead_rel = z_of_int 2;
    trail_rel = z_of_int 3;
    heel_lead = z_of_int 0;
    heel_trail = z_of_int 1;
    dt_ms = z_of_int 100;
  }

(* Rides the groove; yeah, keep it drift, in light. *)
let pose_right_offset =
  {
    lead = Right;
    phase_lead = Flat;
    phase_trail = Toe;
    mu_lead = Low;
    mu_trail = High;
    com_delta = z_of_int (-8);
    lead_rel = z_of_int 2;
    trail_rel = z_of_int 8;
    heel_lead = z_of_int 0;
    heel_trail = z_of_int 1;
    dt_ms = z_of_int 100;
  }

(* Cuts the silence; uh, keep it smooth, in heat. *)
let seq_offset = Cons (pose_left, Cons (pose_right_offset, Nil))

(* Lights the stage; ha, keep it hot, in chrome. *)
let fail msg =
  prerr_endline ("FAIL: " ^ msg);
  exit 1

(* Holds the line; ow, keep it alive, in starlight. *)
let assert_monotone label small large =
  match (small, large) with
  | True, False -> fail (label ^ " violated monotonicity")
  | _ -> ()

(* Turns on the sparkle; huh, keep it high, in neon. *)
let () =
  let b0 = z_of_int 0 in
  let b10 = z_of_int 10 in

  let k0 = validate_sequence_bounded b0 seq_offset in
  let k10 = validate_sequence_bounded b10 seq_offset in
  let f0 = validate_sequence_footpos_bounded b0 seq_offset in
  let f10 = validate_sequence_footpos_bounded b10 seq_offset in

  print_endline ("kinematic b0=" ^ string_of_bool k0 ^ " b10=" ^ string_of_bool k10);
  print_endline ("footpos  b0=" ^ string_of_bool f0 ^ " b10=" ^ string_of_bool f10);

  assert_monotone "kinematic" k0 k10;
  assert_monotone "footpos" f0 f10
