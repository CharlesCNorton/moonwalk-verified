
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

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

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
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

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

  (** val add_carry : positive -> positive -> positive **)

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

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

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

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

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
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

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

  (** val add : z -> z -> z **)

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

  (** val compare : z -> z -> comparison **)

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

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val eqb : z -> z -> bool **)

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
 end

type foot =
| Left
| Right

(** val other : foot -> foot **)

let other = function
| Left -> Right
| Right -> Left

(** val foot_eqb : foot -> foot -> bool **)

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

(** val phase_eqb : phase -> phase -> bool **)

let phase_eqb a b =
  match a with
  | Flat -> (match b with
             | Flat -> True
             | Toe -> False)
  | Toe -> (match b with
            | Flat -> False
            | Toe -> True)

type friction =
| Low
| High

(** val friction_eqb : friction -> friction -> bool **)

let friction_eqb a b =
  match a with
  | Low -> (match b with
            | Low -> True
            | High -> False)
  | High -> (match b with
             | Low -> False
             | High -> True)

type pose = { lead : foot; phase_lead : phase; phase_trail : phase;
              mu_lead : friction; mu_trail : friction; com_delta : z;
              lead_rel : z; trail_rel : z; heel_lead : z; heel_trail : 
              z; dt_ms : z }

(** val abs_disp : z -> z -> z **)

let abs_disp =
  Z.add

(** val moonwalk_stepb : pose -> bool **)

let moonwalk_stepb p =
  match match match match match match match match match match phase_eqb
                                                                p.phase_lead
                                                                Flat with
                                                        | True ->
                                                          phase_eqb
                                                            p.phase_trail Toe
                                                        | False -> False with
                                                  | True ->
                                                    friction_eqb p.mu_lead Low
                                                  | False -> False with
                                            | True ->
                                              friction_eqb p.mu_trail High
                                            | False -> False with
                                      | True ->
                                        Z.eqb
                                          (abs_disp p.com_delta p.trail_rel)
                                          Z0
                                      | False -> False with
                                | True -> Z.ltb Z0 p.lead_rel
                                | False -> False with
                          | True -> Z.ltb Z0 p.trail_rel
                          | False -> False with
                    | True -> Z.leb p.lead_rel p.trail_rel
                    | False -> False with
              | True -> Z.eqb p.heel_lead Z0
              | False -> False with
        | True -> Z.ltb Z0 p.heel_trail
        | False -> False with
  | True -> Z.ltb Z0 p.dt_ms
  | False -> False

(** val alternatesb : foot -> pose list -> bool **)

let rec alternatesb f = function
| Nil -> True
| Cons (p, ps) ->
  (match foot_eqb p.lead f with
   | True -> alternatesb (other f) ps
   | False -> False)

(** val alternatingb : pose list -> bool **)

let alternatingb poses =
  match alternatesb Left poses with
  | True -> True
  | False -> alternatesb Right poses

(** val all_stepsb : pose list -> bool **)

let all_stepsb poses =
  forallb moonwalk_stepb poses

(** val validate_sequence : pose list -> bool **)

let validate_sequence poses =
  match all_stepsb poses with
  | True -> alternatingb poses
  | False -> False
