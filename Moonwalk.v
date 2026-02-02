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

Inductive Foot : Type := Left | Right.

Definition other (f : Foot) : Foot :=
  match f with
  | Left => Right
  | Right => Left
  end.

Definition foot_eqb (a b : Foot) : bool :=
  match a, b with
  | Left, Left => true
  | Right, Right => true
  | _, _ => false
  end.

Lemma foot_eqb_eq : forall a b, foot_eqb a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intros; try discriminate; reflexivity.
Qed.

Definition Foot_eq_dec : forall a b : Foot, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Inductive Phase : Type := Flat | Toe.

Definition phase_eqb (a b : Phase) : bool :=
  match a, b with
  | Flat, Flat => true
  | Toe, Toe => true
  | _, _ => false
  end.

Lemma phase_eqb_eq : forall a b, phase_eqb a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intros; try discriminate; reflexivity.
Qed.

Definition Phase_eq_dec : forall a b : Phase, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Inductive Friction : Type := Low | High.

Definition friction_eqb (a b : Friction) : bool :=
  match a, b with
  | Low, Low => true
  | High, High => true
  | _, _ => false
  end.

Lemma friction_eqb_eq : forall a b, friction_eqb a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intros; try discriminate; reflexivity.
Qed.

Definition Friction_eq_dec : forall a b : Friction, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** A single motion-capture pose frame. *)
Record Pose : Type := {
  lead : Foot;
  phase_lead : Phase;
  phase_trail : Phase;
  mu_lead : Friction;
  mu_trail : Friction;
  com_delta : Z;   (* center-of-mass displacement; negative = backward *)
  lead_rel : Z;    (* lead foot displacement relative to body *)
  trail_rel : Z;   (* trailing foot displacement relative to body *)
  heel_lead : Z;   (* lead heel height above ground *)
  heel_trail : Z;  (* trail heel height above ground *)
  dt_ms : Z        (* frame duration in milliseconds *)
}.

Definition abs_disp (com d : Z) : Z := com + d.

Definition phase_height_ok (ph : Phase) (heel_h : Z) : Prop :=
  match ph with
  | Flat => heel_h = 0
  | Toe => 0 < heel_h
  end.

Definition timing_ok (dt : Z) : Prop := 0 < dt.

Definition anchor_fixed (p : Pose) : Prop :=
  abs_disp p.(com_delta) p.(trail_rel) = 0.

Definition apparent_forward (p : Pose) : Prop := 0 < p.(lead_rel).
Definition net_backward (p : Pose) : Prop := p.(com_delta) < 0.
Definition lead_slides_back (p : Pose) : Prop :=
  abs_disp p.(com_delta) p.(lead_rel) <= 0.

(** Physical and kinematic constraints for a single moonwalk step. *)
Definition moonwalk_step (p : Pose) : Prop :=
  phase_lead p = Flat /\
  phase_trail p = Toe /\
  mu_lead p = Low /\
  mu_trail p = High /\
  anchor_fixed p /\
  0 < lead_rel p /\
  0 < trail_rel p /\
  lead_rel p <= trail_rel p /\
  phase_height_ok (phase_lead p) (heel_lead p) /\
  phase_height_ok (phase_trail p) (heel_trail p) /\
  timing_ok (dt_ms p).

Definition illusion (p : Pose) : Prop :=
  apparent_forward p /\ net_backward p /\ lead_slides_back p.

Lemma anchor_fixed_com_delta :
  forall p, anchor_fixed p -> com_delta p = - trail_rel p.
Proof.
  intros p H.
  unfold anchor_fixed, abs_disp in H.
  lia.
Qed.

Lemma moonwalk_step_net_backward :
  forall p, moonwalk_step p -> net_backward p.
Proof.
  intros p H.
  unfold moonwalk_step in H.
  destruct H as (_ & _ & _ & _ & Hanchor & _ & Htrail & _ & _ & _ & _).
  unfold net_backward.
  pose proof anchor_fixed_com_delta p Hanchor as Hdelta.
  lia.
Qed.

Lemma moonwalk_step_lead_slides_back :
  forall p, moonwalk_step p -> lead_slides_back p.
Proof.
  intros p H.
  unfold moonwalk_step in H.
  destruct H as (_ & _ & _ & _ & Hanchor & _ & _ & Hle & _ & _ & _).
  unfold lead_slides_back, abs_disp.
  pose proof anchor_fixed_com_delta p Hanchor as Hdelta.
  lia.
Qed.

Lemma moonwalk_step_implies_illusion :
  forall p, moonwalk_step p -> illusion p.
Proof.
  intros p H.
  unfold illusion.
  split.
  - unfold apparent_forward.
    unfold moonwalk_step in H.
    tauto.
  - split.
    + apply moonwalk_step_net_backward; exact H.
    + apply moonwalk_step_lead_slides_back; exact H.
Qed.

(** Alternating lead-foot cycle. *)
Fixpoint alternates (f : Foot) (poses : list Pose) : Prop :=
  match poses with
  | [] => True
  | p :: ps => p.(lead) = f /\ alternates (other f) ps
  end.

Definition alternating (poses : list Pose) : Prop :=
  alternates Left poses \/ alternates Right poses.

(** Boolean checker for a single step. *)
Definition moonwalk_stepb (p : Pose) : bool :=
  phase_eqb p.(phase_lead) Flat &&
  phase_eqb p.(phase_trail) Toe &&
  friction_eqb p.(mu_lead) Low &&
  friction_eqb p.(mu_trail) High &&
  Z.eqb (abs_disp p.(com_delta) p.(trail_rel)) 0 &&
  Z.ltb 0 p.(lead_rel) &&
  Z.ltb 0 p.(trail_rel) &&
  Z.leb p.(lead_rel) p.(trail_rel) &&
  Z.eqb p.(heel_lead) 0 &&
  Z.ltb 0 p.(heel_trail) &&
  Z.ltb 0 p.(dt_ms).

Lemma moonwalk_stepb_sound :
  forall p, moonwalk_stepb p = true -> moonwalk_step p.
Proof.
  intros p H.
  unfold moonwalk_stepb in H.
  apply andb_true_iff in H as [Hrest Hdt].
  apply andb_true_iff in Hrest as [Hrest Hheel_trail].
  apply andb_true_iff in Hrest as [Hrest Hheel_lead].
  apply andb_true_iff in Hrest as [Hrest Hle].
  apply andb_true_iff in Hrest as [Hrest Htrailpos].
  apply andb_true_iff in Hrest as [Hrest Hleadpos].
  apply andb_true_iff in Hrest as [Hrest Hanchor].
  apply andb_true_iff in Hrest as [Hrest Hmu_trail].
  apply andb_true_iff in Hrest as [Hrest Hmu_lead].
  apply andb_true_iff in Hrest as [Hphase_lead Hphase_trail].
  apply phase_eqb_eq in Hphase_lead.
  apply phase_eqb_eq in Hphase_trail.
  apply friction_eqb_eq in Hmu_lead.
  apply friction_eqb_eq in Hmu_trail.
  apply (proj1 (Z.eqb_eq _ _)) in Hanchor.
  apply (proj1 (Z.ltb_lt 0 (lead_rel p))) in Hleadpos.
  apply (proj1 (Z.ltb_lt 0 (trail_rel p))) in Htrailpos.
  apply (proj1 (Z.leb_le (lead_rel p) (trail_rel p))) in Hle.
  apply (proj1 (Z.eqb_eq _ _)) in Hheel_lead.
  apply (proj1 (Z.ltb_lt 0 (heel_trail p))) in Hheel_trail.
  apply (proj1 (Z.ltb_lt 0 (dt_ms p))) in Hdt.
  unfold moonwalk_step.
  repeat split.
  - exact Hphase_lead.
  - exact Hphase_trail.
  - exact Hmu_lead.
  - exact Hmu_trail.
  - exact Hanchor.
  - exact Hleadpos.
  - exact Htrailpos.
  - exact Hle.
  - unfold phase_height_ok. rewrite Hphase_lead. exact Hheel_lead.
  - unfold phase_height_ok. rewrite Hphase_trail. exact Hheel_trail.
  - unfold timing_ok. exact Hdt.
Qed.

Fixpoint alternatesb (f : Foot) (poses : list Pose) : bool :=
  match poses with
  | [] => true
  | p :: ps => foot_eqb p.(lead) f && alternatesb (other f) ps
  end.

Definition alternatingb (poses : list Pose) : bool :=
  alternatesb Left poses || alternatesb Right poses.

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

Lemma alternatingb_sound :
  forall poses, alternatingb poses = true -> alternating poses.
Proof.
  intros poses H.
  unfold alternatingb in H.
  apply orb_true_iff in H as [Hleft | Hright].
  - left. apply alternatesb_sound; exact Hleft.
  - right. apply alternatesb_sound; exact Hright.
Qed.

Definition all_stepsb (poses : list Pose) : bool :=
  forallb moonwalk_stepb poses.

Lemma all_stepsb_sound :
  forall poses, all_stepsb poses = true -> Forall moonwalk_step poses.
Proof.
  induction poses as [|p ps IH]; simpl; intros H.
  - constructor.
  - apply andb_true_iff in H as [Hstep Hrest].
    constructor.
    + apply moonwalk_stepb_sound; exact Hstep.
    + apply IH; exact Hrest.
Qed.

Definition valid_sequence (poses : list Pose) : Prop :=
  Forall moonwalk_step poses /\ alternating poses.

Definition validate_sequence (poses : list Pose) : bool :=
  all_stepsb poses && alternatingb poses.

Lemma validate_sequence_sound :
  forall poses, validate_sequence poses = true -> valid_sequence poses.
Proof.
  intros poses H.
  unfold validate_sequence, valid_sequence in H |- *.
  apply andb_true_iff in H as [Hsteps Halt].
  split.
  - apply all_stepsb_sound; exact Hsteps.
  - apply alternatingb_sound; exact Halt.
Qed.

(** Center-of-mass trajectory. *)
Fixpoint trajectory_from (x : Z) (ds : list Z) : list Z :=
  match ds with
  | [] => [x]
  | d :: ds' => x :: trajectory_from (x + d) ds'
  end.

Definition trajectory (poses : list Pose) : list Z :=
  trajectory_from 0 (map com_delta poses).

Fixpoint trajectory_decreasing (x : Z) (ds : list Z) : Prop :=
  match ds with
  | [] => True
  | d :: ds' => x + d < x /\ trajectory_decreasing (x + d) ds'
  end.

Definition trajectory_decreasing_poses (poses : list Pose) : Prop :=
  trajectory_decreasing 0 (map com_delta poses).

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

Lemma valid_sequence_trajectory_decreasing :
  forall poses,
    valid_sequence poses ->
    trajectory_decreasing_poses poses.
Proof.
  intros poses H.
  destruct H as [Hsteps _].
  apply trajectory_decreasing_from_deltas.
  apply net_backward_forall_deltas.
  induction Hsteps; constructor.
  - apply moonwalk_step_net_backward; exact H.
  - apply IHHsteps.
Qed.

(** Example: a minimal two-step moonwalk cycle. *)
Definition pose_left : Pose :=
  {| lead := Left;
     phase_lead := Flat;
     phase_trail := Toe;
     mu_lead := Low;
     mu_trail := High;
     com_delta := -3;
     lead_rel := 2;
     trail_rel := 3;
     heel_lead := 0;
     heel_trail := 1;
     dt_ms := 100 |}.

Definition pose_right : Pose :=
  {| lead := Right;
     phase_lead := Flat;
     phase_trail := Toe;
     mu_lead := Low;
     mu_trail := High;
     com_delta := -3;
     lead_rel := 2;
     trail_rel := 3;
     heel_lead := 0;
     heel_trail := 1;
     dt_ms := 100 |}.

Example validator_example :
  validate_sequence [pose_left; pose_right] = true.
Proof. reflexivity. Qed.

Require Extraction.
Extraction Language OCaml.
Extraction "moonwalk_validator.ml" validate_sequence.
