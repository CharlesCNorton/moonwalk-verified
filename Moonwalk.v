(******************************************************************************)
(*                                                                            *)
(*                       The Moonwalk: Backslide Kinematics                   *)
(*                                                                            *)
(*     Formalizes the biomechanics of the moonwalk (backslide): the           *)
(*     alternating flat-foot/toe-raised cycle, center-of-mass trajectory,     *)
(*     and visual paradox of apparent forward gait with net backward          *)
(*     displacement. Proves illusion conditions from friction constraints.    *)
(*     Extracts to a pose-sequence validator for motion capture training.     *)
(*                                                                            *)
(*     "I never tried to do the moonwalk, it just happened."                  *)
(*     - Michael Jackson, 1988                                                *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: February 2, 2026                                                 *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import List ZArith Bool Lia.
Import ListNotations.
Open Scope Z_scope.

(** Establishes Foot. Clear statement, as a thin bridge. *)
Inductive Foot : Type := Left | Right.

(** Labels other as a helper. Constrained and sober. *)
Definition other (f : Foot) : Foot :=
  match f with
  | Left => Right
  | Right => Left
  end.

(** Calls out foot_eqb. Terse definition, to keep the thread tight. *)
Definition foot_eqb (a b : Foot) : bool :=
  match a, b with
  | Left, Left => true
  | Right, Right => true
  | _, _ => false
  end.

(** foot_eqb_eq enters as a lemma. To keep intent readable. *)
Lemma foot_eqb_eq : forall a b, foot_eqb a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intros; try discriminate; reflexivity.
Qed.

(** Isolates Foot_eq_dec as a helper. Literal and measured. *)
Definition Foot_eq_dec : forall a b : Foot, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** Phase enters as an inductive type. To make the seam visible. *)
Inductive Phase : Type := Flat | Toe.

(** Exposes phase_eqb for later steps. Sober and measured. *)
Definition phase_eqb (a b : Phase) : bool :=
  match a, b with
  | Flat, Flat => true
  | Toe, Toe => true
  | _, _ => false
  end.

(** Binds phase_eqb_eq as a lemma. Formal and measured. *)
Lemma phase_eqb_eq : forall a b, phase_eqb a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intros; try discriminate; reflexivity.
Qed.

(** Marks Phase_eq_dec as a definition. Literal and frugal. *)
Definition Phase_eq_dec : forall a b : Phase, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** Pins other_phase down; so the next steps stay grounded. *)
Definition other_phase (ph : Phase) : Phase :=
  match ph with
  | Flat => Toe
  | Toe => Flat
  end.

(** mm: ordered definition kept formal. *)
Definition mm : Type := Z.
Definition ms : Type := Z.
Definition mu : Type := Z. (* friction coefficient scaled by 1000 *)
Definition mm_per_ms : Type := Z.

(** Defines Calibration. As a minimal hinge. *)
Record Calibration : Type := {
  mu_slide_max : mu;
  mu_anchor_min : mu;
  step_min : mm;
  step_max : mm;
  heel_max : mm;
  dt_min : ms;
  dt_max : ms;
  v_com_max : mm_per_ms;
  v_lead_max : mm_per_ms;
  v_trail_max : mm_per_ms;
  continuity_bound : mm;
  continuity_dt_bound : ms;
  footpos_bound : mm;
  illusion_back_min : mm;
  illusion_back_max : mm
}.

(** default_calibration stands as a definition. Exact and severe. *)
Definition default_calibration : Calibration := {|
  mu_slide_max := 300;
  mu_anchor_min := 700;
  step_min := 1;
  step_max := 20;
  heel_max := 10;
  dt_min := 10;
  dt_max := 200;
  v_com_max := 2;
  v_lead_max := 2;
  v_trail_max := 2;
  continuity_bound := 10;
  continuity_dt_bound := 20;
  footpos_bound := 10;
  illusion_back_min := 1;
  illusion_back_max := 20
|}.

(** Labels Pose. To hold the line. *)
Record Pose : Type := {
  lead : Foot;
  phase_lead : Phase;
  phase_trail : Phase;
  mu_lead : mu;
  mu_trail : mu;
  com_delta : mm;   (* center-of-mass displacement; negative = backward *)
  lead_rel : mm;    (* lead foot displacement relative to body *)
  trail_rel : mm;   (* trailing foot displacement relative to body *)
  heel_lead : mm;   (* lead heel height above ground *)
  heel_trail : mm;  (* trail heel height above ground *)
  toe_lead : mm;    (* lead toe height above ground *)
  toe_trail : mm;   (* trail toe height above ground *)
  dt_ms : ms        (* frame duration in milliseconds *)
}.

(** abs_disp is a minimal definition. So later proof steps have a target. *)
Definition abs_disp (com d : Z) : Z := com + d.

(** Establishes within_range. Clear statement, to prevent drift. *)
Definition within_range (x lo hi : Z) : Prop := lo <= x <= hi.

(** Captures within_rangeb. To keep dependencies visible. *)
Definition within_rangeb (x lo hi : Z) : bool :=
  Z.leb lo x && Z.leb x hi.

(** within_rangeb_sound: crisp lemma kept narrow. *)
Lemma within_rangeb_sound :
  forall x lo hi, within_rangeb x lo hi = true -> within_range x lo hi.
Proof.
  intros x lo hi H.
  unfold within_rangeb in H.
  apply andb_true_iff in H as [Hlo Hhi].
  unfold within_range.
  split.
  - apply (proj1 (Z.leb_le _ _)); exact Hlo.
  - apply (proj1 (Z.leb_le _ _)); exact Hhi.
Qed.

(** Spells out within_rangeb_complete. Direct and sealed. *)
Lemma within_rangeb_complete :
  forall x lo hi, within_range x lo hi -> within_rangeb x lo hi = true.
Proof.
  intros x lo hi H.
  unfold within_range in H.
  destruct H as [Hlo Hhi].
  unfold within_rangeb.
  apply andb_true_iff. split.
  - apply (proj2 (Z.leb_le _ _)); exact Hlo.
  - apply (proj2 (Z.leb_le _ _)); exact Hhi.
Qed.

(** Names phase_contact_ok in a precise style. To keep the scope honest. *)
Definition phase_contact_ok (ph : Phase) (heel_h toe_h : Z) : Prop :=
  match ph with
  | Flat => heel_h = 0 /\ toe_h = 0
  | Toe => 0 < heel_h /\ toe_h = 0
  end.

(** phase_contact_okb is a utility here; so the next steps stay grounded. *)
Definition phase_contact_okb (ph : Phase) (heel_h toe_h : Z) : bool :=
  match ph with
  | Flat => Z.eqb heel_h 0 && Z.eqb toe_h 0
  | Toe => Z.ltb 0 heel_h && Z.eqb toe_h 0
  end.

(** Sets phase_contact_okb_sound in scope. To prevent drift. *)
Lemma phase_contact_okb_sound :
  forall ph heel_h toe_h,
    phase_contact_okb ph heel_h toe_h = true ->
    phase_contact_ok ph heel_h toe_h.
Proof.
  intros ph heel_h toe_h H.
  destruct ph; simpl in H.
  - apply andb_true_iff in H as [Hheel Htoe].
    split.
    + apply (proj1 (Z.eqb_eq _ _)); exact Hheel.
    + apply (proj1 (Z.eqb_eq _ _)); exact Htoe.
  - apply andb_true_iff in H as [Hheel Htoe].
    split.
    + apply (proj1 (Z.ltb_lt 0 heel_h)); exact Hheel.
    + apply (proj1 (Z.eqb_eq _ _)); exact Htoe.
Qed.

(** Names phase_contact_okb_complete in a ordered style. To keep intent readable. *)
Lemma phase_contact_okb_complete :
  forall ph heel_h toe_h,
    phase_contact_ok ph heel_h toe_h ->
    phase_contact_okb ph heel_h toe_h = true.
Proof.
  intros ph heel_h toe_h H.
  destruct ph; simpl in H.
  - destruct H as [Hheel Htoe].
    apply andb_true_iff. split.
    + apply (proj2 (Z.eqb_eq _ _)); exact Hheel.
    + apply (proj2 (Z.eqb_eq _ _)); exact Htoe.
  - destruct H as [Hheel Htoe].
    apply andb_true_iff. split.
    + apply (proj2 (Z.ltb_lt 0 heel_h)); exact Hheel.
    + apply (proj2 (Z.eqb_eq _ _)); exact Htoe.
Qed.

(** timing_ok enters as a definition. For later use. *)
Definition timing_ok (c : Calibration) (dt : Z) : Prop :=
  within_range dt (dt_min c) (dt_max c).

(** Exposes timing_okb as a utility. Measured and grounded. *)
Definition timing_okb (c : Calibration) (dt : Z) : bool :=
  within_rangeb dt (dt_min c) (dt_max c).

(** Names timing_okb_sound in a measured style. To prevent drift. *)
Lemma timing_okb_sound :
  forall c dt, timing_okb c dt = true -> timing_ok c dt.
Proof.
  intros c dt H.
  unfold timing_okb, timing_ok in H |- *.
  apply within_rangeb_sound; exact H.
Qed.

(** Places timing_okb_complete here; as a controlled interface. *)
Lemma timing_okb_complete :
  forall c dt, timing_ok c dt -> timing_okb c dt = true.
Proof.
  intros c dt H.
  unfold timing_okb, timing_ok in H |- *.
  apply within_rangeb_complete; exact H.
Qed.

(** Highlights friction_ok as a definition. Concise and austere. *)
Definition friction_ok (c : Calibration) (p : Pose) : Prop :=
  mu_lead p <= mu_slide_max c /\ mu_anchor_min c <= mu_trail p.

(** Highlights friction_okb as a definition. Constrained and formal. *)
Definition friction_okb (c : Calibration) (p : Pose) : bool :=
  Z.leb (mu_lead p) (mu_slide_max c) && Z.leb (mu_anchor_min c) (mu_trail p).

(** Marks friction_okb_sound as a lemma; to keep dependencies visible. *)
Lemma friction_okb_sound :
  forall c p, friction_okb c p = true -> friction_ok c p.
Proof.
  intros c p H.
  unfold friction_okb in H.
  apply andb_true_iff in H as [Hlead Htrail].
  unfold friction_ok.
  split.
  - apply (proj1 (Z.leb_le _ _)); exact Hlead.
  - apply (proj1 (Z.leb_le _ _)); exact Htrail.
Qed.

(** Captures friction_okb_complete. To avoid ambiguity. *)
Lemma friction_okb_complete :
  forall c p, friction_ok c p -> friction_okb c p = true.
Proof.
  intros c p H.
  unfold friction_ok in H.
  destruct H as [Hlead Htrail].
  unfold friction_okb.
  apply andb_true_iff. split.
  - apply (proj2 (Z.leb_le _ _)); exact Hlead.
  - apply (proj2 (Z.leb_le _ _)); exact Htrail.
Qed.

(** step_size_ok: terse definition kept methodical. *)
Definition step_size_ok (c : Calibration) (p : Pose) : Prop :=
  within_range (lead_rel p) (step_min c) (step_max c) /\
  within_range (trail_rel p) (step_min c) (step_max c).

(** Lays out step_size_okb, to anchor later steps. *)
Definition step_size_okb (c : Calibration) (p : Pose) : bool :=
  within_rangeb (lead_rel p) (step_min c) (step_max c) &&
  within_rangeb (trail_rel p) (step_min c) (step_max c).

(** Registers step_size_okb_sound as a lemma. To keep dependencies visible. *)
Lemma step_size_okb_sound :
  forall c p, step_size_okb c p = true -> step_size_ok c p.
Proof.
  intros c p H.
  unfold step_size_okb in H.
  apply andb_true_iff in H as [Hlead Htrail].
  unfold step_size_ok.
  split.
  - apply within_rangeb_sound; exact Hlead.
  - apply within_rangeb_sound; exact Htrail.
Qed.

(** step_size_okb_complete is a lemma here; as a stable handle. *)
Lemma step_size_okb_complete :
  forall c p, step_size_ok c p -> step_size_okb c p = true.
Proof.
  intros c p H.
  unfold step_size_ok in H.
  destruct H as [Hlead Htrail].
  unfold step_size_okb.
  apply andb_true_iff. split.
  - apply within_rangeb_complete; exact Hlead.
  - apply within_rangeb_complete; exact Htrail.
Qed.

(** Notes heel_ok. Literal, measured, and disciplined. *)
Definition heel_ok (c : Calibration) (p : Pose) : Prop :=
  heel_lead p <= heel_max c /\ heel_trail p <= heel_max c.

(** Keeps heel_okb explicit. To keep the thread tight. *)
Definition heel_okb (c : Calibration) (p : Pose) : bool :=
  Z.leb (heel_lead p) (heel_max c) && Z.leb (heel_trail p) (heel_max c).

(** heel_okb_sound: structured lemma kept precise. *)
Lemma heel_okb_sound :
  forall c p, heel_okb c p = true -> heel_ok c p.
Proof.
  intros c p H.
  unfold heel_okb in H.
  apply andb_true_iff in H as [Hlead Htrail].
  unfold heel_ok.
  split.
  - apply (proj1 (Z.leb_le _ _)); exact Hlead.
  - apply (proj1 (Z.leb_le _ _)); exact Htrail.
Qed.

(** heel_okb_complete enters as a lemma. To keep dependencies visible. *)
Lemma heel_okb_complete :
  forall c p, heel_ok c p -> heel_okb c p = true.
Proof.
  intros c p H.
  unfold heel_ok in H.
  destruct H as [Hlead Htrail].
  unfold heel_okb.
  apply andb_true_iff. split.
  - apply (proj2 (Z.leb_le _ _)); exact Hlead.
  - apply (proj2 (Z.leb_le _ _)); exact Htrail.
Qed.

(** Keeps speed_ok explicit. So the next steps stay grounded. *)
Definition speed_ok (c : Calibration) (p : Pose) : Prop :=
  Z.abs (com_delta p) <= v_com_max c * dt_ms p /\
  Z.abs (lead_rel p) <= v_lead_max c * dt_ms p /\
  Z.abs (trail_rel p) <= v_trail_max c * dt_ms p.

(** One unadorned helper named speed_okb. To avoid ambiguity. *)
Definition speed_okb (c : Calibration) (p : Pose) : bool :=
  Z.leb (Z.abs (com_delta p)) (v_com_max c * dt_ms p) &&
  (Z.leb (Z.abs (lead_rel p)) (v_lead_max c * dt_ms p) &&
   Z.leb (Z.abs (trail_rel p)) (v_trail_max c * dt_ms p)).

(** Captures speed_okb_sound. To keep the scope honest. *)
Lemma speed_okb_sound :
  forall c p, speed_okb c p = true -> speed_ok c p.
Proof.
  intros c p H.
  unfold speed_okb in H.
  apply andb_true_iff in H as [Hcom Hrest].
  apply andb_true_iff in Hrest as [Hlead Htrail].
  unfold speed_ok.
  split.
  - apply (proj1 (Z.leb_le _ _)); exact Hcom.
  - split.
    + apply (proj1 (Z.leb_le _ _)); exact Hlead.
    + apply (proj1 (Z.leb_le _ _)); exact Htrail.
Qed.

(** Notes speed_okb_complete. Rigid, severe, and ordered. *)
Lemma speed_okb_complete :
  forall c p, speed_ok c p -> speed_okb c p = true.
Proof.
  intros c p H.
  unfold speed_ok in H.
  destruct H as [Hcom [Hlead Htrail]].
  unfold speed_okb.
  apply andb_true_iff. split.
  - apply (proj2 (Z.leb_le _ _)); exact Hcom.
  - apply andb_true_iff. split.
    + apply (proj2 (Z.leb_le _ _)); exact Hlead.
    + apply (proj2 (Z.leb_le _ _)); exact Htrail.
Qed.

(** Names contact_ok in a deterministic style. To keep the story strict. *)
Definition contact_ok (p : Pose) : Prop :=
  phase_contact_ok (phase_lead p) (heel_lead p) (toe_lead p) /\
  phase_contact_ok (phase_trail p) (heel_trail p) (toe_trail p).

(** Keeps contact_okb explicit. To make the seam visible. *)
Definition contact_okb (p : Pose) : bool :=
  phase_contact_okb (phase_lead p) (heel_lead p) (toe_lead p) &&
  phase_contact_okb (phase_trail p) (heel_trail p) (toe_trail p).

(** Names contact_okb_sound in a hard-edged style. To hold the line. *)
Lemma contact_okb_sound :
  forall p, contact_okb p = true -> contact_ok p.
Proof.
  intros p H.
  unfold contact_okb in H.
  apply andb_true_iff in H as [Hlead Htrail].
  unfold contact_ok.
  split.
  - apply phase_contact_okb_sound; exact Hlead.
  - apply phase_contact_okb_sound; exact Htrail.
Qed.

(** Marks out contact_okb_complete, as a controlled interface. *)
Lemma contact_okb_complete :
  forall p, contact_ok p -> contact_okb p = true.
Proof.
  intros p H.
  unfold contact_ok in H.
  destruct H as [Hlead Htrail].
  unfold contact_okb.
  apply andb_true_iff. split.
  - apply phase_contact_okb_complete; exact Hlead.
  - apply phase_contact_okb_complete; exact Htrail.
Qed.

(** Marks phase_for as a utility; to reduce noise. *)
Definition phase_for (f : Foot) (p : Pose) : Phase :=
  if foot_eqb f p.(lead) then phase_lead p else phase_trail p.

(** Establishes heel_for. Explicit statement, to keep the scope honest. *)
Definition heel_for (f : Foot) (p : Pose) : Z :=
  if foot_eqb f p.(lead) then heel_lead p else heel_trail p.

(** Places toe_for here; as a thin bridge. *)
Definition toe_for (f : Foot) (p : Pose) : Z :=
  if foot_eqb f p.(lead) then toe_lead p else toe_trail p.

(** Establishes phase_flip. Plain statement, without ornament. *)
Definition phase_flip (p q : Pose) : Prop :=
  phase_for Left q = other_phase (phase_for Left p) /\
  phase_for Right q = other_phase (phase_for Right p).

(** phase_flipb is a utility here; to keep dependencies visible. *)
Definition phase_flipb (p q : Pose) : bool :=
  phase_eqb (phase_for Left q) (other_phase (phase_for Left p)) &&
  phase_eqb (phase_for Right q) (other_phase (phase_for Right p)).

(** Registers phase_flipb_sound as a lemma. For later use. *)
Lemma phase_flipb_sound :
  forall p q, phase_flipb p q = true -> phase_flip p q.
Proof.
  intros p q H.
  unfold phase_flipb in H.
  apply andb_true_iff in H as [Hleft Hright].
  unfold phase_flip.
  split.
  - apply (proj1 (phase_eqb_eq _ _)); exact Hleft.
  - apply (proj1 (phase_eqb_eq _ _)); exact Hright.
Qed.

(** phase_flipb_complete is a lemma here; without ornament. *)
Lemma phase_flipb_complete :
  forall p q, phase_flip p q -> phase_flipb p q = true.
Proof.
  intros p q H.
  unfold phase_flip in H.
  destruct H as [Hleft Hright].
  unfold phase_flipb.
  apply andb_true_iff. split.
  - apply (proj2 (phase_eqb_eq _ _)); exact Hleft.
  - apply (proj2 (phase_eqb_eq _ _)); exact Hright.
Qed.

(** Declares anchor_fixed. To anchor later steps. *)
Definition anchor_fixed (p : Pose) : Prop :=
  abs_disp p.(com_delta) p.(trail_rel) = 0.

(** Marks apparent_forward as a definition; so the next steps stay grounded. *)
Definition apparent_forward (p : Pose) : Prop := 0 < p.(lead_rel).
(** Names net_backward in a unadorned style. To keep intent readable. *)
Definition net_backward (p : Pose) : Prop := p.(com_delta) < 0.
(** Calls out lead_slides_back. Terse utility, as a stable handle. *)
Definition lead_slides_back (p : Pose) : Prop :=
  abs_disp p.(com_delta) p.(lead_rel) <= 0.

(** Names moonwalk_step in a clear style. So the next steps stay grounded. *)
Definition moonwalk_step (c : Calibration) (p : Pose) : Prop :=
  phase_lead p = Flat /\
  phase_trail p = Toe /\
  friction_ok c p /\
  anchor_fixed p /\
  0 < lead_rel p /\
  0 < trail_rel p /\
  lead_rel p <= trail_rel p /\
  step_size_ok c p /\
  heel_ok c p /\
  contact_ok p /\
  speed_ok c p /\
  timing_ok c (dt_ms p) /\
  within_range (- (com_delta p)) (illusion_back_min c) (illusion_back_max c).

(** Pins illusion down; to keep dependencies visible. *)
Definition illusion (c : Calibration) (p : Pose) : Prop :=
  apparent_forward p /\
  net_backward p /\
  lead_slides_back p /\
  within_range (- (com_delta p)) (illusion_back_min c) (illusion_back_max c).

(** Isolates anchor_fixed_com_delta. To keep intent readable. *)
Lemma anchor_fixed_com_delta :
  forall p, anchor_fixed p -> com_delta p = - trail_rel p.
Proof.
  intros p H.
  unfold anchor_fixed, abs_disp in H.
  lia.
Qed.

(** Sets moonwalk_step_net_backward, with no extra claims. *)
Lemma moonwalk_step_net_backward :
  forall c p, moonwalk_step c p -> net_backward p.
Proof.
  intros c p H.
  unfold moonwalk_step in H.
  destruct H as (_ & _ & _ & Hanchor & _ & Htrail & _ & _ & _ & _ & _ & _ & _).
  unfold net_backward.
  pose proof anchor_fixed_com_delta p Hanchor as Hdelta.
  lia.
Qed.

(** Calls out moonwalk_step_lead_slides_back. Structured lemma, for later use. *)
Lemma moonwalk_step_lead_slides_back :
  forall c p, moonwalk_step c p -> lead_slides_back p.
Proof.
  intros c p H.
  unfold moonwalk_step in H.
  destruct H as (_ & _ & _ & Hanchor & _ & _ & Hle & _ & _ & _ & _ & _ & _).
  unfold lead_slides_back, abs_disp.
  pose proof anchor_fixed_com_delta p Hanchor as Hdelta.
  lia.
Qed.

(** Establishes moonwalk_step_implies_illusion. Sealed statement, to keep dependencies visible. *)
Lemma moonwalk_step_implies_illusion :
  forall c p, moonwalk_step c p -> illusion c p.
Proof.
  intros c p H.
  unfold illusion.
  split.
  - unfold apparent_forward.
    unfold moonwalk_step in H.
    tauto.
  - split.
    + apply moonwalk_step_net_backward with (c := c); exact H.
    + split.
      * apply moonwalk_step_lead_slides_back with (c := c); exact H.
      * unfold moonwalk_step in H. tauto.
Qed.

(** Pins alternates down; with no extra claims. *)
Fixpoint alternates (f : Foot) (poses : list Pose) : Prop :=
  match poses with
  | [] => True
  | p :: ps => p.(lead) = f /\ alternates (other f) ps
  end.

(** Calls out alternating. Structured helper, to keep the story strict. *)
Definition alternating (poses : list Pose) : Prop :=
  alternates Left poses \/ alternates Right poses.

(** Pins moonwalk_stepb down; to make the seam visible. *)
Definition moonwalk_stepb (c : Calibration) (p : Pose) : bool :=
  phase_eqb p.(phase_lead) Flat &&
  (phase_eqb p.(phase_trail) Toe &&
   (friction_okb c p &&
    (Z.eqb (abs_disp p.(com_delta) p.(trail_rel)) 0 &&
     (Z.ltb 0 p.(lead_rel) &&
      (Z.ltb 0 p.(trail_rel) &&
       (Z.leb p.(lead_rel) p.(trail_rel) &&
        (step_size_okb c p &&
         (heel_okb c p &&
          (contact_okb p &&
           (speed_okb c p &&
            (timing_okb c (dt_ms p) &&
             within_rangeb (- (com_delta p)) (illusion_back_min c) (illusion_back_max c)))))))))))).

(** Places moonwalk_stepb_sound here; to anchor later steps. *)
Lemma moonwalk_stepb_sound :
  forall c p, moonwalk_stepb c p = true -> moonwalk_step c p.
Proof.
  intros c p H.
  unfold moonwalk_stepb in H.
  apply andb_true_iff in H as [Hphase_lead Hrest].
  apply andb_true_iff in Hrest as [Hphase_trail Hrest].
  apply andb_true_iff in Hrest as [Hfriction Hrest].
  apply andb_true_iff in Hrest as [Hanchor Hrest].
  apply andb_true_iff in Hrest as [Hleadpos Hrest].
  apply andb_true_iff in Hrest as [Htrailpos Hrest].
  apply andb_true_iff in Hrest as [Hle Hrest].
  apply andb_true_iff in Hrest as [Hstep Hrest].
  apply andb_true_iff in Hrest as [Hheel Hrest].
  apply andb_true_iff in Hrest as [Hcontact Hrest].
  apply andb_true_iff in Hrest as [Hspeed Hrest].
  apply andb_true_iff in Hrest as [Htiming Hillusion].
  apply phase_eqb_eq in Hphase_lead.
  apply phase_eqb_eq in Hphase_trail.
  apply friction_okb_sound in Hfriction.
  apply (proj1 (Z.eqb_eq _ _)) in Hanchor.
  apply (proj1 (Z.ltb_lt 0 (lead_rel p))) in Hleadpos.
  apply (proj1 (Z.ltb_lt 0 (trail_rel p))) in Htrailpos.
  apply (proj1 (Z.leb_le (lead_rel p) (trail_rel p))) in Hle.
  apply step_size_okb_sound in Hstep.
  apply heel_okb_sound in Hheel.
  apply contact_okb_sound in Hcontact.
  apply speed_okb_sound in Hspeed.
  apply timing_okb_sound in Htiming.
  apply within_rangeb_sound in Hillusion.
  unfold moonwalk_step.
  split; [exact Hphase_lead |].
  split; [exact Hphase_trail |].
  split; [exact Hfriction |].
  split; [exact Hanchor |].
  split; [exact Hleadpos |].
  split; [exact Htrailpos |].
  split; [exact Hle |].
  split; [exact Hstep |].
  split; [exact Hheel |].
  split; [exact Hcontact |].
  split; [exact Hspeed |].
  split; [exact Htiming |].
  exact Hillusion.
Qed.

(** Spells out moonwalk_stepb_complete. Bounded and austere. *)
Lemma moonwalk_stepb_complete :
  forall c p, moonwalk_step c p -> moonwalk_stepb c p = true.
Proof.
  intros c p H.
  unfold moonwalk_step in H.
  destruct H as (Hphase_lead & Hphase_trail & Hfriction & Hanchor &
                 Hleadpos & Htrailpos & Hle & Hstep & Hheel & Hcontact &
                 Hspeed & Htiming & Hillusion).
  unfold moonwalk_stepb.
  apply andb_true_iff. split.
  - apply (proj2 (phase_eqb_eq _ _)); exact Hphase_lead.
  - apply andb_true_iff. split.
    + apply (proj2 (phase_eqb_eq _ _)); exact Hphase_trail.
    + apply andb_true_iff. split.
      * apply friction_okb_complete; exact Hfriction.
      * apply andb_true_iff. split.
        -- apply (proj2 (Z.eqb_eq _ _)); exact Hanchor.
        -- apply andb_true_iff. split.
           ++ apply (proj2 (Z.ltb_lt 0 (lead_rel p))); exact Hleadpos.
           ++ apply andb_true_iff. split.
              ** apply (proj2 (Z.ltb_lt 0 (trail_rel p))); exact Htrailpos.
              ** apply andb_true_iff. split.
                 --- apply (proj2 (Z.leb_le (lead_rel p) (trail_rel p))); exact Hle.
                 --- apply andb_true_iff. split.
                     +++ apply step_size_okb_complete; exact Hstep.
                     +++ apply andb_true_iff. split.
                         *** apply heel_okb_complete; exact Hheel.
                         *** apply andb_true_iff. split.
                             ---- apply contact_okb_complete; exact Hcontact.
                             ---- apply andb_true_iff. split.
                                 ++++ apply speed_okb_complete; exact Hspeed.
                                 ++++ apply andb_true_iff. split.
                                     **** apply timing_okb_complete; exact Htiming.
                                     **** apply within_rangeb_complete; exact Hillusion.
Qed.

(** Establishes alternatesb. Grounded statement, to keep the thread tight. *)
Fixpoint alternatesb (f : Foot) (poses : list Pose) : bool :=
  match poses with
  | [] => true
  | p :: ps => foot_eqb p.(lead) f && alternatesb (other f) ps
  end.

(** alternatingb enters as a definition. As a minimal hinge. *)
Definition alternatingb (poses : list Pose) : bool :=
  alternatesb Left poses || alternatesb Right poses.

(** One minimal lemma named alternatesb_sound. So the next steps stay grounded. *)
Lemma alternatesb_sound :
  forall f poses, alternatesb f poses = true -> alternates f poses.
Proof.
  intros f poses H.
  generalize dependent f.
  induction poses as [|p ps IH]; intros f H; simpl in H.
  - exact I.
  - apply andb_true_iff in H as [Hlead Hrest].
    split.
    + apply foot_eqb_eq; exact Hlead.
    + apply IH with (f := other f); exact Hrest.
Qed.

(** Sets alternatesb_complete in scope. To hold the line. *)
Lemma alternatesb_complete :
  forall f poses, alternates f poses -> alternatesb f poses = true.
Proof.
  intros f poses H.
  generalize dependent f.
  induction poses as [|p ps IH]; intros f H; simpl in H.
  - reflexivity.
  - destruct H as [Hlead Hrest].
    simpl.
    apply andb_true_iff. split.
    + apply (proj2 (foot_eqb_eq _ _)). exact Hlead.
    + apply IH with (f := other f); exact Hrest.
Qed.

(** Holds alternatingb_sound steady; to keep the thread tight. *)
Lemma alternatingb_sound :
  forall poses, alternatingb poses = true -> alternating poses.
Proof.
  intros poses H.
  unfold alternatingb in H.
  apply orb_true_iff in H as [Hleft | Hright].
  - left. apply alternatesb_sound; exact Hleft.
  - right. apply alternatesb_sound; exact Hright.
Qed.

(** Calls out alternatingb_complete. Minimal lemma, so later proof steps have a target. *)
Lemma alternatingb_complete :
  forall poses, alternating poses -> alternatingb poses = true.
Proof.
  intros poses H.
  unfold alternatingb.
  destruct H as [Hleft | Hright].
  - apply orb_true_iff. left. apply alternatesb_complete; exact Hleft.
  - apply orb_true_iff. right. apply alternatesb_complete; exact Hright.
Qed.

(** Sets all_stepsb in scope. To keep intent readable. *)
Definition all_stepsb (c : Calibration) (poses : list Pose) : bool :=
  forallb (moonwalk_stepb c) poses.

(** Notes all_stepsb_sound. Rigid, lean, and stark. *)
Lemma all_stepsb_sound :
  forall c poses, all_stepsb c poses = true -> Forall (moonwalk_step c) poses.
Proof.
  induction poses as [|p ps IH]; simpl; intros H.
  - constructor.
  - apply andb_true_iff in H as [Hstep Hrest].
    constructor.
    + apply moonwalk_stepb_sound; exact Hstep.
    + apply IH; exact Hrest.
Qed.

(** all_stepsb_complete stands as a lemma. Careful and focused. *)
Lemma all_stepsb_complete :
  forall c poses, Forall (moonwalk_step c) poses -> all_stepsb c poses = true.
Proof.
  induction poses as [|p ps IH]; simpl; intros H.
  - reflexivity.
  - inversion H as [|p' ps' Hp Hps]; subst.
    apply andb_true_iff. split.
    + apply moonwalk_stepb_complete; exact Hp.
    + apply IH; exact Hps.
Qed.

(** within: careful definition kept terse. *)
Definition within (b x y : Z) : Prop :=
  Z.abs (x - y) <= b.

(** States withinb as a definition. Compact and spare. *)
Definition withinb (b x y : Z) : bool :=
  Z.leb (Z.abs (x - y)) b.

(** Calls out withinb_sound. Hard-edged lemma, to keep the scope honest. *)
Lemma withinb_sound :
  forall b x y, withinb b x y = true -> within b x y.
Proof.
  intros b x y H.
  unfold withinb, within in H |- *.
  apply (proj1 (Z.leb_le _ _)); exact H.
Qed.

(** Marks withinb_complete as a lemma; to keep intent readable. *)
Lemma withinb_complete :
  forall b x y, within b x y -> withinb b x y = true.
Proof.
  intros b x y H.
  unfold withinb, within in H |- *.
  apply (proj2 (Z.leb_le _ _)); exact H.
Qed.

(** Marks within_mono as a lemma; to keep dependencies visible. *)
Lemma within_mono :
  forall b1 b2 x y, b1 <= b2 -> within b1 x y -> within b2 x y.
Proof.
  intros b1 b2 x y Hle Hwithin.
  unfold within in Hwithin |- *.
  eapply Z.le_trans; eauto.
Qed.

(** Registers withinb_mono as a lemma. Structured and single-purpose. *)
Lemma withinb_mono :
  forall b1 b2 x y,
    Z.leb b1 b2 = true ->
    withinb b1 x y = true ->
    withinb b2 x y = true.
Proof.
  intros b1 b2 x y Hle Hwithin.
  apply withinb_complete.
  apply within_mono with (b1 := b1).
  - apply (proj1 (Z.leb_le _ _)); exact Hle.
  - apply withinb_sound; exact Hwithin.
Qed.

(** Keeps within_refl_nonneg explicit. As a stable handle. *)
Lemma within_refl_nonneg :
  forall b x, 0 <= b -> within b x x.
Proof.
  intros b x Hb.
  unfold within.
  rewrite Z.sub_diag, Z.abs_0.
  exact Hb.
Qed.

(** Establishes withinb_refl_nonneg. Frugal statement, to keep dependencies visible. *)
Lemma withinb_refl_nonneg :
  forall b x, 0 <= b -> withinb b x x = true.
Proof.
  intros b x Hb.
  apply withinb_complete.
  apply within_refl_nonneg; exact Hb.
Qed.

(** Names continuous_between in a narrow style. For later use. *)
Definition continuous_between (c : Calibration) (b : Z) (p q : Pose) : Prop :=
  q.(lead) = other p.(lead) /\
  phase_flip p q /\
  within b p.(com_delta) q.(com_delta) /\
  within b p.(lead_rel) q.(lead_rel) /\
  within b p.(trail_rel) q.(trail_rel) /\
  within b p.(heel_lead) q.(heel_lead) /\
  within b p.(heel_trail) q.(heel_trail) /\
  within b p.(toe_lead) q.(toe_lead) /\
  within b p.(toe_trail) q.(toe_trail) /\
  within (continuity_dt_bound c) p.(dt_ms) q.(dt_ms).

(** Notes continuous_betweenb. Grounded, exact, and measured. *)
Definition continuous_betweenb (c : Calibration) (b : Z) (p q : Pose) : bool :=
  foot_eqb q.(lead) (other p.(lead)) &&
  (phase_flipb p q &&
   (withinb b p.(com_delta) q.(com_delta) &&
    (withinb b p.(lead_rel) q.(lead_rel) &&
     (withinb b p.(trail_rel) q.(trail_rel) &&
      (withinb b p.(heel_lead) q.(heel_lead) &&
       (withinb b p.(heel_trail) q.(heel_trail) &&
        (withinb b p.(toe_lead) q.(toe_lead) &&
         (withinb b p.(toe_trail) q.(toe_trail) &&
          withinb (continuity_dt_bound c) p.(dt_ms) q.(dt_ms))))))))).

(** Registers continuous_betweenb_sound as a lemma. As a minimal hinge. *)
Lemma continuous_betweenb_sound :
  forall c b p q, continuous_betweenb c b p q = true -> continuous_between c b p q.
Proof.
  intros c b p q H.
  unfold continuous_betweenb in H.
  apply andb_true_iff in H as [Hlead Hrest].
  apply andb_true_iff in Hrest as [Hphase Hrest].
  apply andb_true_iff in Hrest as [Hcom Hrest].
  apply andb_true_iff in Hrest as [Hleadrel Hrest].
  apply andb_true_iff in Hrest as [Htrailrel Hrest].
  apply andb_true_iff in Hrest as [Hheel_lead Hrest].
  apply andb_true_iff in Hrest as [Hheel_trail Hrest].
  apply andb_true_iff in Hrest as [Htoe_lead Hrest].
  apply andb_true_iff in Hrest as [Htoe_trail Hdt].
  unfold continuous_between.
  split.
  - apply (proj1 (foot_eqb_eq _ _)); exact Hlead.
  - split.
    + apply phase_flipb_sound; exact Hphase.
    + split.
      * apply withinb_sound; exact Hcom.
      * split.
        { apply withinb_sound; exact Hleadrel. }
        { split.
          - apply withinb_sound; exact Htrailrel.
          - split.
            + apply withinb_sound; exact Hheel_lead.
            + split.
              * apply withinb_sound; exact Hheel_trail.
              * split.
                { apply withinb_sound; exact Htoe_lead. }
                { split.
                  - apply withinb_sound; exact Htoe_trail.
                  - apply withinb_sound; exact Hdt. } }
Qed.

(** Captures continuous_betweenb_complete. To avoid ambiguity. *)
Lemma continuous_betweenb_complete :
  forall c b p q, continuous_between c b p q -> continuous_betweenb c b p q = true.
Proof.
  intros c b p q H.
  unfold continuous_between in H.
  destruct H as (Hlead & Hphase & Hcom & Hleadrel & Htrailrel & Hheel_lead &
                 Hheel_trail & Htoe_lead & Htoe_trail & Hdt).
  unfold continuous_betweenb.
  apply andb_true_iff. split.
  - apply (proj2 (foot_eqb_eq _ _)); exact Hlead.
  - apply andb_true_iff. split.
    + apply phase_flipb_complete; exact Hphase.
    + apply andb_true_iff. split.
      * apply withinb_complete; exact Hcom.
      * apply andb_true_iff. split.
        -- apply withinb_complete; exact Hleadrel.
        -- apply andb_true_iff. split.
           ++ apply withinb_complete; exact Htrailrel.
           ++ apply andb_true_iff. split.
              ** apply withinb_complete; exact Hheel_lead.
              ** apply andb_true_iff. split.
                 --- apply withinb_complete; exact Hheel_trail.
                 --- apply andb_true_iff. split.
                     +++ apply withinb_complete; exact Htoe_lead.
                     +++ apply andb_true_iff. split.
                         **** apply withinb_complete; exact Htoe_trail.
                         **** apply withinb_complete; exact Hdt.
Qed.

(** continuous_between_mono enters as a lemma. To keep the story strict. *)
Lemma continuous_between_mono :
  forall c b1 b2 p q,
    b1 <= b2 ->
    continuous_between c b1 p q ->
    continuous_between c b2 p q.
Proof.
  intros c b1 b2 p q Hle H.
  unfold continuous_between in H |- *.
  destruct H as (Hlead & Hphase & Hcom & Hleadrel & Htrailrel & Hheel_lead &
                 Hheel_trail & Htoe_lead & Htoe_trail & Hdt).
  split; [exact Hlead |].
  split; [exact Hphase |].
  split; [apply within_mono with (b1 := b1); [exact Hle | exact Hcom] |].
  split; [apply within_mono with (b1 := b1); [exact Hle | exact Hleadrel] |].
  split; [apply within_mono with (b1 := b1); [exact Hle | exact Htrailrel] |].
  split; [apply within_mono with (b1 := b1); [exact Hle | exact Hheel_lead] |].
  split; [apply within_mono with (b1 := b1); [exact Hle | exact Hheel_trail] |].
  split; [apply within_mono with (b1 := b1); [exact Hle | exact Htoe_lead] |].
  split; [apply within_mono with (b1 := b1); [exact Hle | exact Htoe_trail] |].
  exact Hdt.
Qed.

(** Names continuous_betweenb_mono in a sober style. To anchor later steps. *)
Lemma continuous_betweenb_mono :
  forall c b1 b2 p q,
    Z.leb b1 b2 = true ->
    continuous_betweenb c b1 p q = true ->
    continuous_betweenb c b2 p q = true.
Proof.
  intros c b1 b2 p q Hle H.
  apply continuous_betweenb_complete.
  apply continuous_between_mono with (b1 := b1).
  - apply (proj1 (Z.leb_le _ _)); exact Hle.
  - apply continuous_betweenb_sound; exact H.
Qed.

(** One unadorned recursive function named continuous_sequence_from. To keep dependencies visible. *)
Fixpoint continuous_sequence_from (c : Calibration) (b : Z) (prev : Pose) (poses : list Pose) : Prop :=
  match poses with
  | [] => True
  | q :: rest => continuous_between c b prev q /\ continuous_sequence_from c b q rest
  end.

(** Names continuous_sequence in a taut style. To keep intent readable. *)
Definition continuous_sequence (c : Calibration) (b : Z) (poses : list Pose) : Prop :=
  match poses with
  | [] => True
  | p :: rest => continuous_sequence_from c b p rest
  end.

(** Defines continuous_sequenceb_from. As a thin bridge. *)
Fixpoint continuous_sequenceb_from (c : Calibration) (b : Z) (prev : Pose) (poses : list Pose) : bool :=
  match poses with
  | [] => true
  | q :: rest => continuous_betweenb c b prev q && continuous_sequenceb_from c b q rest
  end.

(** Fixes continuous_sequenceb as a definition. Terse and careful. *)
Definition continuous_sequenceb (c : Calibration) (b : Z) (poses : list Pose) : bool :=
  match poses with
  | [] => true
  | p :: rest => continuous_sequenceb_from c b p rest
  end.

(** Sets continuous_sequenceb_from_sound in scope. Without ornament. *)
Lemma continuous_sequenceb_from_sound :
  forall c b prev poses,
    continuous_sequenceb_from c b prev poses = true ->
    continuous_sequence_from c b prev poses.
Proof.
  intros c b prev poses H.
  generalize dependent prev.
  induction poses as [|q rest IH]; intros prev H; simpl in *; auto.
  apply andb_true_iff in H as [Hstep Hrest].
  split.
  - apply continuous_betweenb_sound; exact Hstep.
  - apply IH with (prev := q); exact Hrest.
Qed.

(** Registers continuous_sequenceb_sound as a lemma. To hold the line. *)
Lemma continuous_sequenceb_sound :
  forall c b poses, continuous_sequenceb c b poses = true -> continuous_sequence c b poses.
Proof.
  intros c b poses H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply continuous_sequenceb_from_sound; exact H.
Qed.

(** Sets continuous_sequenceb_from_complete in scope. To make the seam visible. *)
Lemma continuous_sequenceb_from_complete :
  forall c b prev poses,
    continuous_sequence_from c b prev poses ->
    continuous_sequenceb_from c b prev poses = true.
Proof.
  intros c b prev poses H.
  generalize dependent prev.
  induction poses as [|q rest IH]; intros prev H; simpl in *; auto.
  destruct H as [Hstep Hrest].
  apply andb_true_iff. split.
  - apply continuous_betweenb_complete; exact Hstep.
  - apply IH with (prev := q); exact Hrest.
Qed.

(** Sets continuous_sequenceb_complete in scope. To avoid ambiguity. *)
Lemma continuous_sequenceb_complete :
  forall c b poses, continuous_sequence c b poses -> continuous_sequenceb c b poses = true.
Proof.
  intros c b poses H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply continuous_sequenceb_from_complete; exact H.
Qed.

(** continuous_sequence_from_mono enters as a lemma. To anchor later steps. *)
Lemma continuous_sequence_from_mono :
  forall c b1 b2 prev poses,
    b1 <= b2 ->
    continuous_sequence_from c b1 prev poses ->
    continuous_sequence_from c b2 prev poses.
Proof.
  intros c b1 b2 prev poses Hle H.
  generalize dependent prev.
  induction poses as [|q rest IH]; intros prev H; simpl in *; auto.
  destruct H as [Hstep Hrest].
  split.
  - apply continuous_between_mono with (b1 := b1); [exact Hle | exact Hstep].
  - apply IH with (prev := q); exact Hrest.
Qed.

(** continuous_sequence_mono stands as a lemma. Ordered and tight. *)
Lemma continuous_sequence_mono :
  forall c b1 b2 poses,
    b1 <= b2 ->
    continuous_sequence c b1 poses ->
    continuous_sequence c b2 poses.
Proof.
  intros c b1 b2 poses Hle H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply continuous_sequence_from_mono with (b1 := b1); [exact Hle | exact H].
Qed.

(** Names continuous_sequenceb_from_mono in a taut style. Without ornament. *)
Lemma continuous_sequenceb_from_mono :
  forall c b1 b2 prev poses,
    Z.leb b1 b2 = true ->
    continuous_sequenceb_from c b1 prev poses = true ->
    continuous_sequenceb_from c b2 prev poses = true.
Proof.
  intros c b1 b2 prev poses Hle H.
  generalize dependent prev.
  induction poses as [|q rest IH]; intros prev H; simpl in *; auto.
  apply andb_true_iff in H as [Hstep Hrest].
  apply andb_true_iff. split.
  - apply continuous_betweenb_mono with (b1 := b1); [exact Hle | exact Hstep].
  - apply IH with (prev := q); exact Hrest.
Qed.

(** continuous_sequenceb_mono is a sterile lemma. With no extra claims. *)
Lemma continuous_sequenceb_mono :
  forall c b1 b2 poses,
    Z.leb b1 b2 = true ->
    continuous_sequenceb c b1 poses = true ->
    continuous_sequenceb c b2 poses = true.
Proof.
  intros c b1 b2 poses Hle H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply continuous_sequenceb_from_mono with (b1 := b1); [exact Hle | exact H].
Qed.

(** One exact utility named left_pos. With no extra claims. *)
Definition left_pos (p : Pose) : Z :=
  match p.(lead) with
  | Left => abs_disp p.(com_delta) p.(lead_rel)
  | Right => abs_disp p.(com_delta) p.(trail_rel)
  end.

(** One direct definition named right_pos. To make the seam visible. *)
Definition right_pos (p : Pose) : Z :=
  match p.(lead) with
  | Left => abs_disp p.(com_delta) p.(trail_rel)
  | Right => abs_disp p.(com_delta) p.(lead_rel)
  end.

(** Defines footpos_between. To anchor later steps. *)
Definition footpos_between (b : Z) (p q : Pose) : Prop :=
  within b (left_pos p) (left_pos q) /\
  within b (right_pos p) (right_pos q).

(** Defines footpos_betweenb. To keep dependencies visible. *)
Definition footpos_betweenb (b : Z) (p q : Pose) : bool :=
  withinb b (left_pos p) (left_pos q) &&
  withinb b (right_pos p) (right_pos q).

(** Places footpos_betweenb_sound here; to make the seam visible. *)
Lemma footpos_betweenb_sound :
  forall b p q, footpos_betweenb b p q = true -> footpos_between b p q.
Proof.
  intros b p q H.
  unfold footpos_betweenb in H.
  apply andb_true_iff in H as [Hleft Hright].
  unfold footpos_between.
  split.
  - apply withinb_sound; exact Hleft.
  - apply withinb_sound; exact Hright.
Qed.

(** Defines footpos_betweenb_complete. To keep intent readable. *)
Lemma footpos_betweenb_complete :
  forall b p q, footpos_between b p q -> footpos_betweenb b p q = true.
Proof.
  intros b p q H.
  unfold footpos_between in H.
  destruct H as [Hleft Hright].
  unfold footpos_betweenb.
  apply andb_true_iff. split.
  - apply withinb_complete; exact Hleft.
  - apply withinb_complete; exact Hright.
Qed.

(** Sets footpos_between_mono in scope. Without ornament. *)
Lemma footpos_between_mono :
  forall b1 b2 p q,
    b1 <= b2 ->
    footpos_between b1 p q ->
    footpos_between b2 p q.
Proof.
  intros b1 b2 p q Hle H.
  destruct H as [Hleft Hright].
  split.
  - apply within_mono with (b1 := b1); [exact Hle | exact Hleft].
  - apply within_mono with (b1 := b1); [exact Hle | exact Hright].
Qed.

(** One terse lemma named footpos_betweenb_mono. To keep the scope honest. *)
Lemma footpos_betweenb_mono :
  forall b1 b2 p q,
    Z.leb b1 b2 = true ->
    footpos_betweenb b1 p q = true ->
    footpos_betweenb b2 p q = true.
Proof.
  intros b1 b2 p q Hle H.
  apply footpos_betweenb_complete.
  apply footpos_between_mono with (b1 := b1).
  - apply (proj1 (Z.leb_le _ _)); exact Hle.
  - apply footpos_betweenb_sound; exact H.
Qed.

(** Notes footpos_sequence_from. Clear, minimal, and bounded. *)
Fixpoint footpos_sequence_from (b : Z) (prev : Pose) (poses : list Pose) : Prop :=
  match poses with
  | [] => True
  | q :: rest => footpos_between b prev q /\ footpos_sequence_from b q rest
  end.

(** Keeps footpos_sequence explicit. Without ornament. *)
Definition footpos_sequence (b : Z) (poses : list Pose) : Prop :=
  match poses with
  | [] => True
  | p :: rest => footpos_sequence_from b p rest
  end.

(** Notes footpos_sequenceb_from. Sober, lean, and minimal. *)
Fixpoint footpos_sequenceb_from (b : Z) (prev : Pose) (poses : list Pose) : bool :=
  match poses with
  | [] => true
  | q :: rest => footpos_betweenb b prev q && footpos_sequenceb_from b q rest
  end.

(** Names footpos_sequenceb in a dry style. To make the seam visible. *)
Definition footpos_sequenceb (b : Z) (poses : list Pose) : bool :=
  match poses with
  | [] => true
  | p :: rest => footpos_sequenceb_from b p rest
  end.

(** Captures footpos_sequenceb_from_sound. As a controlled interface. *)
Lemma footpos_sequenceb_from_sound :
  forall b prev poses,
    footpos_sequenceb_from b prev poses = true ->
    footpos_sequence_from b prev poses.
Proof.
  intros b prev poses H.
  generalize dependent prev.
  induction poses as [|q rest IH]; intros prev H; simpl in *; auto.
  apply andb_true_iff in H as [Hstep Hrest].
  split.
  - apply footpos_betweenb_sound; exact Hstep.
  - apply IH with (prev := q); exact Hrest.
Qed.

(** Pins footpos_sequenceb_sound down; as a controlled interface. *)
Lemma footpos_sequenceb_sound :
  forall b poses, footpos_sequenceb b poses = true -> footpos_sequence b poses.
Proof.
  intros b poses H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply footpos_sequenceb_from_sound; exact H.
Qed.

(** Holds footpos_sequenceb_from_complete steady; to keep intent readable. *)
Lemma footpos_sequenceb_from_complete :
  forall b prev poses,
    footpos_sequence_from b prev poses ->
    footpos_sequenceb_from b prev poses = true.
Proof.
  intros b prev poses H.
  generalize dependent prev.
  induction poses as [|q rest IH]; intros prev H; simpl in *; auto.
  destruct H as [Hstep Hrest].
  apply andb_true_iff. split.
  - apply footpos_betweenb_complete; exact Hstep.
  - apply IH with (prev := q); exact Hrest.
Qed.

(** Exposes footpos_sequenceb_complete as a lemma. Rigid and purpose-built. *)
Lemma footpos_sequenceb_complete :
  forall b poses, footpos_sequence b poses -> footpos_sequenceb b poses = true.
Proof.
  intros b poses H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply footpos_sequenceb_from_complete; exact H.
Qed.

(** Keeps footpos_sequence_from_mono explicit. As a thin bridge. *)
Lemma footpos_sequence_from_mono :
  forall b1 b2 prev poses,
    b1 <= b2 ->
    footpos_sequence_from b1 prev poses ->
    footpos_sequence_from b2 prev poses.
Proof.
  intros b1 b2 prev poses Hle H.
  generalize dependent prev.
  induction poses as [|q rest IH]; intros prev H; simpl in *; auto.
  destruct H as [Hstep Hrest].
  split.
  - apply footpos_between_mono with (b1 := b1); [exact Hle | exact Hstep].
  - apply IH with (prev := q); exact Hrest.
Qed.

(** footpos_sequence_mono is a pragmatic lemma. As a controlled interface. *)
Lemma footpos_sequence_mono :
  forall b1 b2 poses,
    b1 <= b2 ->
    footpos_sequence b1 poses ->
    footpos_sequence b2 poses.
Proof.
  intros b1 b2 poses Hle H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply footpos_sequence_from_mono with (b1 := b1); [exact Hle | exact H].
Qed.

(** Marks out footpos_sequenceb_from_mono. To hold the line. *)
Lemma footpos_sequenceb_from_mono :
  forall b1 b2 prev poses,
    Z.leb b1 b2 = true ->
    footpos_sequenceb_from b1 prev poses = true ->
    footpos_sequenceb_from b2 prev poses = true.
Proof.
  intros b1 b2 prev poses Hle H.
  generalize dependent prev.
  induction poses as [|q rest IH]; intros prev H; simpl in *; auto.
  apply andb_true_iff in H as [Hstep Hrest].
  apply andb_true_iff. split.
  - apply footpos_betweenb_mono with (b1 := b1); [exact Hle | exact Hstep].
  - apply IH with (prev := q); exact Hrest.
Qed.

(** Exposes footpos_sequenceb_mono for later steps. Clean and formal. *)
Lemma footpos_sequenceb_mono :
  forall b1 b2 poses,
    Z.leb b1 b2 = true ->
    footpos_sequenceb b1 poses = true ->
    footpos_sequenceb b2 poses = true.
Proof.
  intros b1 b2 poses Hle H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply footpos_sequenceb_from_mono with (b1 := b1); [exact Hle | exact H].
Qed.

(** Captures valid_sequence_bounded. So the next steps stay grounded. *)
Definition valid_sequence_bounded (c : Calibration) (b : Z) (poses : list Pose) : Prop :=
  Forall (moonwalk_step c) poses /\ alternating poses /\ continuous_sequence c b poses.

(** valid_sequence stands as a utility. Austere and structured. *)
Definition valid_sequence (poses : list Pose) : Prop :=
  valid_sequence_bounded default_calibration (continuity_bound default_calibration) poses.

(** Names validate_sequence_bounded in a careful style. For later use. *)
Definition validate_sequence_bounded (c : Calibration) (b : Z) (poses : list Pose) : bool :=
  all_stepsb c poses && (alternatingb poses && continuous_sequenceb c b poses).

(** Spells out validate_sequence. Sparse and deterministic. *)
Definition validate_sequence (poses : list Pose) : bool :=
  validate_sequence_bounded default_calibration (continuity_bound default_calibration) poses.

(** Declares validate_sequence_bounded_default, to reduce noise. *)
Definition validate_sequence_bounded_default (b : Z) (poses : list Pose) : bool :=
  validate_sequence_bounded default_calibration b poses.

(** Pins validate_sequence_bounded_sound down; as a stable handle. *)
Lemma validate_sequence_bounded_sound :
  forall c b poses, validate_sequence_bounded c b poses = true -> valid_sequence_bounded c b poses.
Proof.
  intros c b poses H.
  unfold validate_sequence_bounded, valid_sequence_bounded in H |- *.
  apply andb_true_iff in H as [Hsteps Hrest].
  apply andb_true_iff in Hrest as [Halt Hcont].
  split.
  - apply all_stepsb_sound; exact Hsteps.
  - split.
    + apply alternatingb_sound; exact Halt.
    + apply continuous_sequenceb_sound; exact Hcont.
Qed.

(** validate_sequence_sound stands as a lemma. Sharp and clean. *)
Lemma validate_sequence_sound :
  forall poses, validate_sequence poses = true -> valid_sequence poses.
Proof.
  intros poses H.
  unfold validate_sequence, valid_sequence in H |- *.
  apply validate_sequence_bounded_sound; exact H.
Qed.

(** Sets validate_sequence_bounded_complete in scope. With no extra claims. *)
Lemma validate_sequence_bounded_complete :
  forall c b poses, valid_sequence_bounded c b poses -> validate_sequence_bounded c b poses = true.
Proof.
  intros c b poses H.
  unfold valid_sequence_bounded in H.
  destruct H as [Hsteps [Halt Hcont]].
  unfold validate_sequence_bounded.
  apply andb_true_iff. split.
  - apply all_stepsb_complete; exact Hsteps.
  - apply andb_true_iff. split.
    + apply alternatingb_complete; exact Halt.
    + apply continuous_sequenceb_complete; exact Hcont.
Qed.

(** Places validate_sequence_complete here; to anchor later steps. *)
Lemma validate_sequence_complete :
  forall poses, valid_sequence poses -> validate_sequence poses = true.
Proof.
  intros poses H.
  unfold validate_sequence, valid_sequence in H |- *.
  apply validate_sequence_bounded_complete; exact H.
Qed.

(** Keeps valid_sequence_bounded_mono explicit. So later proof steps have a target. *)
Lemma valid_sequence_bounded_mono :
  forall c b1 b2 poses,
    b1 <= b2 ->
    valid_sequence_bounded c b1 poses ->
    valid_sequence_bounded c b2 poses.
Proof.
  intros c b1 b2 poses Hle H.
  destruct H as [Hsteps [Halt Hcont]].
  unfold valid_sequence_bounded.
  repeat split; try exact Hsteps; try exact Halt.
  apply continuous_sequence_mono with (b1 := b1); [exact Hle | exact Hcont].
Qed.

(** Places validate_sequence_bounded_mono here; with no extra claims. *)
Lemma validate_sequence_bounded_mono :
  forall c b1 b2 poses,
    Z.leb b1 b2 = true ->
    validate_sequence_bounded c b1 poses = true ->
    validate_sequence_bounded c b2 poses = true.
Proof.
  intros c b1 b2 poses Hle H.
  apply validate_sequence_bounded_complete.
  apply valid_sequence_bounded_mono with (b1 := b1).
  - apply (proj1 (Z.leb_le _ _)); exact Hle.
  - apply validate_sequence_bounded_sound; exact H.
Qed.

(** Calls out valid_sequence_footpos_bounded. Rigid definition, to prevent drift. *)
Definition valid_sequence_footpos_bounded (c : Calibration) (b : Z) (poses : list Pose) : Prop :=
  Forall (moonwalk_step c) poses /\ alternating poses /\ footpos_sequence b poses.

(** Establishes valid_sequence_footpos. Minimal statement, so later proof steps have a target. *)
Definition valid_sequence_footpos (poses : list Pose) : Prop :=
  valid_sequence_footpos_bounded default_calibration (footpos_bound default_calibration) poses.

(** Anchors validate_sequence_footpos_bounded. As a stable handle. *)
Definition validate_sequence_footpos_bounded (c : Calibration) (b : Z) (poses : list Pose) : bool :=
  all_stepsb c poses && (alternatingb poses && footpos_sequenceb b poses).

(** Encodes validate_sequence_footpos. As a thin bridge. *)
Definition validate_sequence_footpos (poses : list Pose) : bool :=
  validate_sequence_footpos_bounded default_calibration (footpos_bound default_calibration) poses.

(** Binds validate_sequence_footpos_bounded_default, so the next steps stay grounded. *)
Definition validate_sequence_footpos_bounded_default (b : Z) (poses : list Pose) : bool :=
  validate_sequence_footpos_bounded default_calibration b poses.

(** validate_sequence_footpos_bounded_sound enters as a lemma. For later use. *)
Lemma validate_sequence_footpos_bounded_sound :
  forall c b poses,
    validate_sequence_footpos_bounded c b poses = true ->
    valid_sequence_footpos_bounded c b poses.
Proof.
  intros c b poses H.
  unfold validate_sequence_footpos_bounded, valid_sequence_footpos_bounded in H |- *.
  apply andb_true_iff in H as [Hsteps Hrest].
  apply andb_true_iff in Hrest as [Halt Hcont].
  split.
  - apply all_stepsb_sound; exact Hsteps.
  - split.
    + apply alternatingb_sound; exact Halt.
    + apply footpos_sequenceb_sound; exact Hcont.
Qed.

(** Names validate_sequence_footpos_sound, as a controlled interface. *)
Lemma validate_sequence_footpos_sound :
  forall poses,
    validate_sequence_footpos poses = true ->
    valid_sequence_footpos poses.
Proof.
  intros poses H.
  unfold validate_sequence_footpos, valid_sequence_footpos in H |- *.
  apply validate_sequence_footpos_bounded_sound; exact H.
Qed.

(** validate_sequence_footpos_bounded_complete stands as a lemma. Sharp and careful. *)
Lemma validate_sequence_footpos_bounded_complete :
  forall c b poses,
    valid_sequence_footpos_bounded c b poses ->
    validate_sequence_footpos_bounded c b poses = true.
Proof.
  intros c b poses H.
  unfold valid_sequence_footpos_bounded in H.
  destruct H as [Hsteps [Halt Hcont]].
  unfold validate_sequence_footpos_bounded.
  apply andb_true_iff. split.
  - apply all_stepsb_complete; exact Hsteps.
  - apply andb_true_iff. split.
    + apply alternatingb_complete; exact Halt.
    + apply footpos_sequenceb_complete; exact Hcont.
Qed.

(** Holds validate_sequence_footpos_complete steady; as a controlled interface. *)
Lemma validate_sequence_footpos_complete :
  forall poses,
    valid_sequence_footpos poses ->
    validate_sequence_footpos poses = true.
Proof.
  intros poses H.
  unfold validate_sequence_footpos, valid_sequence_footpos in H |- *.
  apply validate_sequence_footpos_bounded_complete; exact H.
Qed.

(** Registers trajectory_from as a recursive function. As a controlled interface. *)
Fixpoint trajectory_from (x : Z) (ds : list Z) : list Z :=
  match ds with
  | [] => [x]
  | d :: ds' => x :: trajectory_from (x + d) ds'
  end.

(** trajectory is a careful definition. Without ornament. *)
Definition trajectory (poses : list Pose) : list Z :=
  trajectory_from 0 (map com_delta poses).

(** Names trajectory_decreasing in a ordered style. To reduce noise. *)
Fixpoint trajectory_decreasing (x : Z) (ds : list Z) : Prop :=
  match ds with
  | [] => True
  | d :: ds' => x + d < x /\ trajectory_decreasing (x + d) ds'
  end.

(** trajectory_decreasing_poses enters as a definition. To keep intent readable. *)
Definition trajectory_decreasing_poses (poses : list Pose) : Prop :=
  trajectory_decreasing 0 (map com_delta poses).

(** Exposes trajectory_decreasing_from_deltas for later steps. Careful and stark. *)
Lemma trajectory_decreasing_from_deltas :
  forall x ds,
    Forall (fun d => d < 0) ds ->
    trajectory_decreasing x ds.
Proof.
  intros x ds H.
  generalize dependent x.
  induction H; intros x0; simpl; auto.
  split.
  - lia.
  - apply IHForall.
Qed.

(** Registers net_backward_forall_deltas as a lemma. So the next steps stay grounded. *)
Lemma net_backward_forall_deltas :
  forall poses,
    Forall net_backward poses ->
    Forall (fun d => d < 0) (map com_delta poses).
Proof.
  induction poses as [|p ps IH]; simpl; intros H; constructor.
  - inversion H as [|p' ps' Hp Hps]; subst.
    unfold net_backward in Hp.
    exact Hp.
  - inversion H as [|p' ps' _ Hps]; subst.
    apply IH; exact Hps.
Qed.

(** valid_sequence_bounded_trajectory_decreasing: methodical lemma kept rigid. *)
Lemma valid_sequence_bounded_trajectory_decreasing :
  forall c b poses,
    valid_sequence_bounded c b poses ->
    trajectory_decreasing_poses poses.
Proof.
  intros c b poses H.
  destruct H as [Hsteps _].
  apply trajectory_decreasing_from_deltas.
  apply net_backward_forall_deltas.
  induction Hsteps; constructor.
  - apply moonwalk_step_net_backward with (c := c); exact H.
  - apply IHHsteps.
Qed.

(** Attaches valid_sequence_trajectory_decreasing. Without ornament. *)
Lemma valid_sequence_trajectory_decreasing :
  forall poses,
    valid_sequence poses ->
    trajectory_decreasing_poses poses.
Proof.
  intros poses H.
  apply valid_sequence_bounded_trajectory_decreasing
    with (c := default_calibration) (b := continuity_bound default_calibration).
  exact H.
Qed.

(** pose_left is a definition here; to reduce noise. *)
Definition pose_left : Pose :=
  {| lead := Left;
     phase_lead := Flat;
     phase_trail := Toe;
     mu_lead := 200;
     mu_trail := 800;
     com_delta := -3;
     lead_rel := 2;
     trail_rel := 3;
     heel_lead := 0;
     heel_trail := 1;
     toe_lead := 0;
     toe_trail := 0;
     dt_ms := 100 |}.

(** Sets pose_right in scope. As a controlled interface. *)
Definition pose_right : Pose :=
  {| lead := Right;
     phase_lead := Flat;
     phase_trail := Toe;
     mu_lead := 200;
     mu_trail := 800;
     com_delta := -3;
     lead_rel := 2;
     trail_rel := 3;
     heel_lead := 0;
     heel_trail := 1;
     toe_lead := 0;
     toe_trail := 0;
     dt_ms := 100 |}.

(** Keeps pose_left_step explicit. With no extra claims. *)
Lemma pose_left_step : moonwalk_step default_calibration pose_left.
Proof.
  unfold moonwalk_step, pose_left, default_calibration, friction_ok, step_size_ok,
    heel_ok, contact_ok, speed_ok, timing_ok, within_range, phase_contact_ok,
    anchor_fixed, abs_disp.
  simpl.
  repeat split; try reflexivity; try lia.
Qed.

(** Pins pose_right_step down; to hold the line. *)
Lemma pose_right_step : moonwalk_step default_calibration pose_right.
Proof.
  unfold moonwalk_step, pose_right, default_calibration, friction_ok, step_size_ok,
    heel_ok, contact_ok, speed_ok, timing_ok, within_range, phase_contact_ok,
    anchor_fixed, abs_disp.
  simpl.
  repeat split; try reflexivity; try lia.
Qed.

(** pose_left_right_alternating enters as a lemma. To prevent drift. *)
Lemma pose_left_right_alternating : alternating [pose_left; pose_right].
Proof.
  left. simpl. split; [reflexivity | split; [reflexivity | exact I]].
Qed.

(** pose_left_right_continuous enters as a lemma. For later use. *)
Lemma pose_left_right_continuous :
  forall b, 0 <= b -> continuous_sequence default_calibration b [pose_left; pose_right].
Proof.
  intros b Hb.
  simpl. split.
  - unfold continuous_between, pose_left, pose_right. simpl.
    repeat split; try reflexivity.
    + apply within_refl_nonneg; exact Hb.
    + apply within_refl_nonneg; exact Hb.
    + apply within_refl_nonneg; exact Hb.
    + apply within_refl_nonneg; exact Hb.
    + apply within_refl_nonneg; exact Hb.
    + apply within_refl_nonneg; exact Hb.
    + apply within_refl_nonneg; exact Hb.
    + unfold default_calibration. simpl. apply within_refl_nonneg. lia.
  - exact I.
Qed.

(** Calls out validator_example_bounded. Ordered artifact, as a controlled interface. *)
Example validator_example_bounded :
  forall b, 0 <= b -> validate_sequence_bounded default_calibration b [pose_left; pose_right] = true.
Proof.
  intros b Hb.
  apply validate_sequence_bounded_complete.
  unfold valid_sequence_bounded.
  split.
  - constructor.
    + apply pose_left_step.
    + constructor.
      * apply pose_right_step.
      * constructor.
  - split.
    + apply pose_left_right_alternating.
    + apply pose_left_right_continuous; exact Hb.
Qed.

Require Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "moonwalk_validator.ml"
  validate_sequence
  validate_sequence_bounded
  validate_sequence_bounded_default
  validate_sequence_footpos
  validate_sequence_footpos_bounded
  validate_sequence_footpos_bounded_default.
