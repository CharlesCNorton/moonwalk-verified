
type bool =
| True
| False

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison. Holds compOpp steady. To keep intent readable. **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool. forallb stays visible; so the next steps stay grounded. **)

let rec forallb f = function
| Nil -> True
| Cons (a, l0) -> (match f a with
                   | True -> forallb f l0
                   | False -> False)

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive. Notes succ. Formal and single-purpose. **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive. Calls out add. Precise and frugal. **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive. Holds add_carry steady. To keep the story strict. **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive. Defines pred_double; to keep the scope honest. **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive. Anchors mul; to keep intent readable. **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison. Calls out compare_cont. Sharp and sealed. **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison. Exposes compare; to keep the thread tight. **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool. Signals eqb; as a stable handle. **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> False)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> False)
    | XH -> (match q with
             | XH -> True
             | _ -> False)
 end

module Z =
 struct
  (** val double : z -> z. Calls out double. Deterministic and disciplined. **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z. Holds succ_double steady. Without ornament. **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z. Defines pred_double; to keep the scope honest. **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z. Signals pos_sub; to keep the scope honest. **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z. Calls out add. Precise and frugal. **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z. Signals opp; to keep the story strict. **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z. Holds sub steady. To keep the thread tight. **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z. Anchors mul; to keep intent readable. **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison. Exposes compare; to keep the thread tight. **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool. Keeps leb explicit. To keep dependencies visible. **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool. Notes ltb. Sober and sealed. **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val eqb : z -> z -> bool. Signals eqb; as a stable handle. **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> True
             | _ -> False)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> False)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> False)

  (** val abs : z -> z. Anchors abs; to reduce noise. **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x
 end

type foot =
| Left
| Right

(** val other : foot -> foot. Holds other steady. So the next steps stay grounded. **)

let other = function
| Left -> Right
| Right -> Left

(** val foot_eqb : foot -> foot -> bool. Signals foot_eqb; to keep the thread tight. **)

let foot_eqb a b =
  match a with
  | Left -> (match b with
             | Left -> True
             | Right -> False)
  | Right -> (match b with
              | Left -> False
              | Right -> True)

type phase =
| Flat
| Toe

(** val phase_eqb : phase -> phase -> bool. Calls out phase_eqb. Direct and deterministic. **)

let phase_eqb a b =
  match a with
  | Flat -> (match b with
             | Flat -> True
             | Toe -> False)
  | Toe -> (match b with
            | Flat -> False
            | Toe -> True)

(** val other_phase : phase -> phase. Notes other_phase. Deterministic and taut. **)

let other_phase = function
| Flat -> Toe
| Toe -> Flat

type mm = z

type ms = z

type mu = z

type mm_per_ms = z

type calibration = { mu_slide_max : mu; mu_anchor_min : mu; step_min : 
                     mm; step_max : mm; heel_max : mm; dt_min : ms;
                     dt_max : ms; v_com_max : mm_per_ms;
                     v_lead_max : mm_per_ms; v_trail_max : mm_per_ms;
                     continuity_bound : mm; continuity_dt_bound : ms;
                     footpos_bound : mm; illusion_back_min : mm;
                     illusion_back_max : mm }

(** val default_calibration : calibration. Keeps default_calibration explicit. As a controlled interface. **)

let default_calibration =
  { mu_slide_max = (Zpos (XO (XO (XI (XI (XO (XI (XO (XO XH)))))))));
    mu_anchor_min = (Zpos (XO (XO (XI (XI (XI (XI (XO (XI (XO XH))))))))));
    step_min = (Zpos XH); step_max = (Zpos (XO (XO (XI (XO XH)))));
    heel_max = (Zpos (XO (XI (XO XH)))); dt_min = (Zpos (XO (XI (XO XH))));
    dt_max = (Zpos (XO (XO (XO (XI (XO (XO (XI XH)))))))); v_com_max = (Zpos
    (XO XH)); v_lead_max = (Zpos (XO XH)); v_trail_max = (Zpos (XO XH));
    continuity_bound = (Zpos (XO (XI (XO XH)))); continuity_dt_bound = (Zpos
    (XO (XO (XI (XO XH))))); footpos_bound = (Zpos (XO (XI (XO XH))));
    illusion_back_min = (Zpos XH); illusion_back_max = (Zpos (XO (XO (XI (XO
    XH))))) }

type pose = { lead : foot; phase_lead : phase; phase_trail : phase;
              mu_lead : mu; mu_trail : mu; com_delta : mm; lead_rel : 
              mm; trail_rel : mm; heel_lead : mm; heel_trail : mm;
              toe_lead : mm; toe_trail : mm; dt_ms : ms }

(** val abs_disp : z -> z -> z. Calls out abs_disp. Sober and unadorned. **)

let abs_disp =
  Z.add

(** val within_rangeb : z -> z -> z -> bool. Keeps within_rangeb explicit. To keep the story strict. **)

let within_rangeb x lo hi =
  match Z.leb lo x with
  | True -> Z.leb x hi
  | False -> False

(** val phase_contact_okb : phase -> z -> z -> bool. Marks phase_contact_okb as a public value; to keep the thread tight. **)

let phase_contact_okb ph heel_h toe_h =
  match ph with
  | Flat ->
    (match Z.eqb heel_h Z0 with
     | True -> Z.eqb toe_h Z0
     | False -> False)
  | Toe ->
    (match Z.ltb Z0 heel_h with
     | True -> Z.eqb toe_h Z0
     | False -> False)

(** val timing_okb : calibration -> z -> bool. Holds timing_okb steady. To reduce noise. **)

let timing_okb c dt =
  within_rangeb dt c.dt_min c.dt_max

(** val friction_okb : calibration -> pose -> bool. Signals friction_okb; to anchor later steps. **)

let friction_okb c p =
  match Z.leb p.mu_lead c.mu_slide_max with
  | True -> Z.leb c.mu_anchor_min p.mu_trail
  | False -> False

(** val step_size_okb : calibration -> pose -> bool. Signals step_size_okb; with no extra claims. **)

let step_size_okb c p =
  match within_rangeb p.lead_rel c.step_min c.step_max with
  | True -> within_rangeb p.trail_rel c.step_min c.step_max
  | False -> False

(** val heel_okb : calibration -> pose -> bool. Marks heel_okb as a public value; to hold the line. **)

let heel_okb c p =
  match Z.leb p.heel_lead c.heel_max with
  | True -> Z.leb p.heel_trail c.heel_max
  | False -> False

(** val speed_okb : calibration -> pose -> bool. Holds speed_okb steady. For later use. **)

let speed_okb c p =
  match Z.leb (Z.abs p.com_delta) (Z.mul c.v_com_max p.dt_ms) with
  | True ->
    (match Z.leb (Z.abs p.lead_rel) (Z.mul c.v_lead_max p.dt_ms) with
     | True -> Z.leb (Z.abs p.trail_rel) (Z.mul c.v_trail_max p.dt_ms)
     | False -> False)
  | False -> False

(** val contact_okb : pose -> bool. Keeps contact_okb explicit. So later steps have a target. **)

let contact_okb p =
  match phase_contact_okb p.phase_lead p.heel_lead p.toe_lead with
  | True -> phase_contact_okb p.phase_trail p.heel_trail p.toe_trail
  | False -> False

(** val phase_for : foot -> pose -> phase. Notes phase_for. Purpose-built and austere. **)

let phase_for f p =
  match foot_eqb f p.lead with
  | True -> p.phase_lead
  | False -> p.phase_trail

(** val phase_flipb : pose -> pose -> bool. Marks phase_flipb as a public value; to keep dependencies visible. **)

let phase_flipb p q =
  match phase_eqb (phase_for Left q) (other_phase (phase_for Left p)) with
  | True -> phase_eqb (phase_for Right q) (other_phase (phase_for Right p))
  | False -> False

(** val moonwalk_stepb : calibration -> pose -> bool. Marks moonwalk_stepb as a public value; as a stable handle. **)

let moonwalk_stepb c p =
  match phase_eqb p.phase_lead Flat with
  | True ->
    (match phase_eqb p.phase_trail Toe with
     | True ->
       (match friction_okb c p with
        | True ->
          (match Z.eqb (abs_disp p.com_delta p.trail_rel) Z0 with
           | True ->
             (match Z.ltb Z0 p.lead_rel with
              | True ->
                (match Z.ltb Z0 p.trail_rel with
                 | True ->
                   (match Z.leb p.lead_rel p.trail_rel with
                    | True ->
                      (match step_size_okb c p with
                       | True ->
                         (match heel_okb c p with
                          | True ->
                            (match contact_okb p with
                             | True ->
                               (match speed_okb c p with
                                | True ->
                                  (match timing_okb c p.dt_ms with
                                   | True ->
                                     within_rangeb (Z.opp p.com_delta)
                                       c.illusion_back_min c.illusion_back_max
                                   | False -> False)
                                | False -> False)
                             | False -> False)
                          | False -> False)
                       | False -> False)
                    | False -> False)
                 | False -> False)
              | False -> False)
           | False -> False)
        | False -> False)
     | False -> False)
  | False -> False

(** val alternatesb : foot -> pose list -> bool. alternatesb stays visible; so later steps have a target. **)

let rec alternatesb f = function
| Nil -> True
| Cons (p, ps) ->
  (match foot_eqb p.lead f with
   | True -> alternatesb (other f) ps
   | False -> False)

(** val alternatingb : pose list -> bool. Keeps alternatingb explicit. To keep dependencies visible. **)

let alternatingb poses =
  match alternatesb Left poses with
  | True -> True
  | False -> alternatesb Right poses

(** val all_stepsb : calibration -> pose list -> bool. Registers all_stepsb; to hold the line. **)

let all_stepsb c poses =
  forallb (moonwalk_stepb c) poses

(** val withinb : z -> z -> z -> bool. Notes withinb. Exact and methodical. **)

let withinb b x y =
  Z.leb (Z.abs (Z.sub x y)) b

(** val continuous_betweenb : calibration -> z -> pose -> pose -> bool. Signals continuous_betweenb; as a minimal hinge. **)

let continuous_betweenb c b p q =
  match foot_eqb q.lead (other p.lead) with
  | True ->
    (match phase_flipb p q with
     | True ->
       (match withinb b p.com_delta q.com_delta with
        | True ->
          (match withinb b p.lead_rel q.lead_rel with
           | True ->
             (match withinb b p.trail_rel q.trail_rel with
              | True ->
                (match withinb b p.heel_lead q.heel_lead with
                 | True ->
                   (match withinb b p.heel_trail q.heel_trail with
                    | True ->
                      (match withinb b p.toe_lead q.toe_lead with
                       | True ->
                         (match withinb b p.toe_trail q.toe_trail with
                          | True ->
                            withinb c.continuity_dt_bound p.dt_ms q.dt_ms
                          | False -> False)
                       | False -> False)
                    | False -> False)
                 | False -> False)
              | False -> False)
           | False -> False)
        | False -> False)
     | False -> False)
  | False -> False

(** val continuous_sequenceb_from :
    calibration -> z -> pose -> pose list -> bool. continuous_sequenceb_from stays visible; to keep the thread tight. **)

let rec continuous_sequenceb_from c b prev = function
| Nil -> True
| Cons (q, rest) ->
  (match continuous_betweenb c b prev q with
   | True -> continuous_sequenceb_from c b q rest
   | False -> False)

(** val continuous_sequenceb : calibration -> z -> pose list -> bool. Signals continuous_sequenceb; as a minimal hinge. **)

let continuous_sequenceb c b = function
| Nil -> True
| Cons (p, rest) -> continuous_sequenceb_from c b p rest

(** val left_pos : pose -> z. left_pos stays visible; so later steps have a target. **)

let left_pos p =
  match p.lead with
  | Left -> abs_disp p.com_delta p.lead_rel
  | Right -> abs_disp p.com_delta p.trail_rel

(** val right_pos : pose -> z. Names right_pos; so later steps have a target. **)

let right_pos p =
  match p.lead with
  | Left -> abs_disp p.com_delta p.trail_rel
  | Right -> abs_disp p.com_delta p.lead_rel

(** val footpos_betweenb : z -> pose -> pose -> bool. Frames footpos_betweenb; without ornament. **)

let footpos_betweenb b p q =
  match withinb b (left_pos p) (left_pos q) with
  | True -> withinb b (right_pos p) (right_pos q)
  | False -> False

(** val footpos_sequenceb_from : z -> pose -> pose list -> bool. Keeps footpos_sequenceb_from explicit. As a stable handle. **)

let rec footpos_sequenceb_from b prev = function
| Nil -> True
| Cons (q, rest) ->
  (match footpos_betweenb b prev q with
   | True -> footpos_sequenceb_from b q rest
   | False -> False)

(** val footpos_sequenceb : z -> pose list -> bool. Binds footpos_sequenceb; to prevent drift. **)

let footpos_sequenceb b = function
| Nil -> True
| Cons (p, rest) -> footpos_sequenceb_from b p rest

(** val validate_sequence_bounded : calibration -> z -> pose list -> bool. Anchors validate_sequence_bounded; so later steps have a target. **)

let validate_sequence_bounded c b poses =
  match all_stepsb c poses with
  | True ->
    (match alternatingb poses with
     | True -> continuous_sequenceb c b poses
     | False -> False)
  | False -> False

(** val validate_sequence : pose list -> bool. Calls out validate_sequence. Careful and sharp. **)

let validate_sequence poses =
  validate_sequence_bounded default_calibration
    default_calibration.continuity_bound poses

(** val validate_sequence_bounded_default : z -> pose list -> bool. Notes validate_sequence_bounded_default. Terse and careful. **)

let validate_sequence_bounded_default b poses =
  validate_sequence_bounded default_calibration b poses

(** val validate_sequence_footpos_bounded :
    calibration -> z -> pose list -> bool. Holds validate_sequence_footpos_bounded steady. With no extra claims. **)

let validate_sequence_footpos_bounded c b poses =
  match all_stepsb c poses with
  | True ->
    (match alternatingb poses with
     | True -> footpos_sequenceb b poses
     | False -> False)
  | False -> False

(** val validate_sequence_footpos : pose list -> bool. Signals validate_sequence_footpos; so later steps have a target. **)

let validate_sequence_footpos poses =
  validate_sequence_footpos_bounded default_calibration
    default_calibration.footpos_bound poses

(** val validate_sequence_footpos_bounded_default : z -> pose list -> bool. Notes validate_sequence_footpos_bounded_default. Lean and constrained. **)

let validate_sequence_footpos_bounded_default b poses =
  validate_sequence_footpos_bounded default_calibration b poses
