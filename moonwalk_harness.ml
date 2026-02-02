open Moonwalk_validator

let rec pos_of_int n =
  if n <= 0 then invalid_arg "pos_of_int expects n > 0"
  else if n = 1 then XH
  else if n land 1 = 0 then XO (pos_of_int (n / 2))
  else XI (pos_of_int (n / 2))

let z_of_int n =
  if n = 0 then Z0
  else if n > 0 then Zpos (pos_of_int n)
  else Zneg (pos_of_int (-n))

let string_of_bool = function
  | True -> "true"
  | False -> "false"

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

let pose_right =
  {
    lead = Right;
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

let demo_seq = Cons (pose_left, Cons (pose_right, Nil))

let () =
  let ok = validate_sequence demo_seq in
  print_endline ("moonwalk_demo_valid=" ^ string_of_bool ok)
