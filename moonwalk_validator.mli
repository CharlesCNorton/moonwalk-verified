
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

val compOpp : comparison -> comparison

val forallb : ('a1 -> bool) -> 'a1 list -> bool

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val abs : z -> z
 end

type foot =
| Left
| Right

val other : foot -> foot

val foot_eqb : foot -> foot -> bool

type phase =
| Flat
| Toe

val phase_eqb : phase -> phase -> bool

type friction =
| Low
| High

val friction_eqb : friction -> friction -> bool

type pose = { lead : foot; phase_lead : phase; phase_trail : phase;
              mu_lead : friction; mu_trail : friction; com_delta : z;
              lead_rel : z; trail_rel : z; heel_lead : z; heel_trail : 
              z; dt_ms : z }

val abs_disp : z -> z -> z

val moonwalk_stepb : pose -> bool

val alternatesb : foot -> pose list -> bool

val alternatingb : pose list -> bool

val all_stepsb : pose list -> bool

val withinb : z -> z -> z -> bool

val continuous_betweenb : z -> pose -> pose -> bool

val continuous_sequenceb_from : z -> pose -> pose list -> bool

val continuous_sequenceb : z -> pose list -> bool

val left_pos : pose -> z

val right_pos : pose -> z

val footpos_betweenb : z -> pose -> pose -> bool

val footpos_sequenceb_from : z -> pose -> pose list -> bool

val footpos_sequenceb : z -> pose list -> bool

val continuity_bound : z

val validate_sequence_bounded : z -> pose list -> bool

val validate_sequence : pose list -> bool

val footpos_bound : z

val validate_sequence_footpos_bounded : z -> pose list -> bool

val validate_sequence_footpos : pose list -> bool
