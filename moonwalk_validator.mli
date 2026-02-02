
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

  val mul : positive -> positive -> positive

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

  val mul : z -> z -> z

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

val other_phase : phase -> phase

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

val default_calibration : calibration

type pose = { lead : foot; phase_lead : phase; phase_trail : phase;
              mu_lead : mu; mu_trail : mu; com_delta : mm; lead_rel : 
              mm; trail_rel : mm; heel_lead : mm; heel_trail : mm;
              toe_lead : mm; toe_trail : mm; dt_ms : ms }

val abs_disp : z -> z -> z

val within_rangeb : z -> z -> z -> bool

val phase_contact_okb : phase -> z -> z -> bool

val timing_okb : calibration -> z -> bool

val friction_okb : calibration -> pose -> bool

val step_size_okb : calibration -> pose -> bool

val heel_okb : calibration -> pose -> bool

val speed_okb : calibration -> pose -> bool

val contact_okb : pose -> bool

val phase_for : foot -> pose -> phase

val phase_flipb : pose -> pose -> bool

val moonwalk_stepb : calibration -> pose -> bool

val alternatesb : foot -> pose list -> bool

val alternatingb : pose list -> bool

val all_stepsb : calibration -> pose list -> bool

val withinb : z -> z -> z -> bool

val continuous_betweenb : calibration -> z -> pose -> pose -> bool

val continuous_sequenceb_from : calibration -> z -> pose -> pose list -> bool

val continuous_sequenceb : calibration -> z -> pose list -> bool

val left_pos : pose -> z

val right_pos : pose -> z

val footpos_betweenb : z -> pose -> pose -> bool

val footpos_sequenceb_from : z -> pose -> pose list -> bool

val footpos_sequenceb : z -> pose list -> bool

val validate_sequence_bounded : calibration -> z -> pose list -> bool

val validate_sequence : pose list -> bool

val validate_sequence_bounded_default : z -> pose list -> bool

val validate_sequence_footpos_bounded : calibration -> z -> pose list -> bool

val validate_sequence_footpos : pose list -> bool

val validate_sequence_footpos_bounded_default : z -> pose list -> bool
