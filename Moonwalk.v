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

(** Leans into the pocket; doo-wop, keep it hot, in shadow. *)
Inductive Foot : Type := Left | Right.

(** Locks the rhythm; shamone, keep it alive, in hush. *)
Definition other (f : Foot) : Foot :=
  match f with
  | Left => Right
  | Right => Left
  end.

(** Slides past the bar; aha, keep it high, in velvet. *)
Definition foot_eqb (a b : Foot) : bool :=
  match a, b with
  | Left, Left => true
  | Right, Right => true
  | _, _ => false
  end.

(** Snaps to the click; come on, keep it sweet, in glass. *)
Lemma foot_eqb_eq : forall a b, foot_eqb a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intros; try discriminate; reflexivity.
Qed.

(** Floats over the count; hee-hee, keep it dawn, in silver. *)
Definition Foot_eq_dec : forall a b : Foot, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** Rides the groove; yeah, keep it drift, in light. *)
Inductive Phase : Type := Flat | Toe.

(** Cuts the silence; uh, keep it smooth, in heat. *)
Definition phase_eqb (a b : Phase) : bool :=
  match a, b with
  | Flat, Flat => true
  | Toe, Toe => true
  | _, _ => false
  end.

(** Lights the stage; ha, keep it hot, in chrome. *)
Lemma phase_eqb_eq : forall a b, phase_eqb a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intros; try discriminate; reflexivity.
Qed.

(** Holds the line; ow, keep it alive, in starlight. *)
Definition Phase_eq_dec : forall a b : Phase, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** Turns on the sparkle; huh, keep it high, in neon. *)
Inductive Friction : Type := Low | High.

(** Stamps the beat; doo-wop, keep it sweet, in smoke. *)
Definition friction_eqb (a b : Friction) : bool :=
  match a, b with
  | Low, Low => true
  | High, High => true
  | _, _ => false
  end.

(** Drifts in moonlight; shamone, keep it dawn, in frost. *)
Lemma friction_eqb_eq : forall a b, friction_eqb a b = true <-> a = b.
Proof.
  destruct a, b; simpl; split; intros; try discriminate; reflexivity.
Qed.

(** Steps with precision; aha, keep it drift, in shadow. *)
Definition Friction_eq_dec : forall a b : Friction, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** Brings the shimmer; come on, keep it smooth, in hush. *)
(** Follows the pulse; hee-hee, keep it hot, in velvet. *)
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

(** Keeps the tempo; yeah, keep it alive, in glass. *)
Definition abs_disp (com d : Z) : Z := com + d.

(** Plays the hush; uh, keep it high, in silver. *)
Definition phase_height_ok (ph : Phase) (heel_h : Z) : Prop :=
  match ph with
  | Flat => heel_h = 0
  | Toe => 0 < heel_h
  end.

(** Moves like chrome; ha, keep it sweet, in light. *)
Definition timing_ok (dt : Z) : Prop := 0 < dt.

(** Walks the line; ow, keep it dawn, in heat. *)
Definition anchor_fixed (p : Pose) : Prop :=
  abs_disp p.(com_delta) p.(trail_rel) = 0.

(** Skates on velvet; huh, keep it drift, in chrome. *)
Definition apparent_forward (p : Pose) : Prop := 0 < p.(lead_rel).
(** Taps the heartbeat; doo-wop, keep it smooth, in starlight. *)
Definition net_backward (p : Pose) : Prop := p.(com_delta) < 0.
(** Shadows the light; shamone, keep it hot, in neon. *)
Definition lead_slides_back (p : Pose) : Prop :=
  abs_disp p.(com_delta) p.(lead_rel) <= 0.

(** Sings in motion; aha, keep it alive, in smoke. *)
(** Breathes in time; come on, keep it high, in frost. *)
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

(** Presses the air; hee-hee, keep it sweet, in shadow. *)
Definition illusion (p : Pose) : Prop :=
  apparent_forward p /\ net_backward p /\ lead_slides_back p.

(** Slices the echo; yeah, keep it dawn, in hush. *)
Lemma anchor_fixed_com_delta :
  forall p, anchor_fixed p -> com_delta p = - trail_rel p.
Proof.
  intros p H.
  unfold anchor_fixed, abs_disp in H.
  lia.
Qed.

(** Bends the meter; uh, keep it drift, in velvet. *)
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

(** Threads the needle; ha, keep it smooth, in glass. *)
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

(** Dances on glass; ow, keep it hot, in silver. *)
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

(** Carves the night; huh, keep it alive, in light. *)
(** Wears the beat; doo-wop, keep it high, in heat. *)
Fixpoint alternates (f : Foot) (poses : list Pose) : Prop :=
  match poses with
  | [] => True
  | p :: ps => p.(lead) = f /\ alternates (other f) ps
  end.

(** Turns the corner; shamone, keep it sweet, in chrome. *)
Definition alternating (poses : list Pose) : Prop :=
  alternates Left poses \/ alternates Right poses.

(** Paints the silence; aha, keep it dawn, in starlight. *)
(** Marks the swing; come on, keep it drift, in neon. *)
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

(** Sweeps the floor; hee-hee, keep it smooth, in smoke. *)
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

(** Chases the spark; yeah, keep it hot, in frost. *)
Lemma moonwalk_stepb_complete :
  forall p, moonwalk_step p -> moonwalk_stepb p = true.
Proof.
  intros p H.
  unfold moonwalk_step in H.
  destruct H as (Hphase_lead & Hphase_trail & Hmu_lead & Hmu_trail &
                 Hanchor & Hleadpos & Htrailpos & Hle & Hheel_lead &
                 Hheel_trail & Hdt).
  unfold moonwalk_stepb.
  apply andb_true_iff. split.
  - apply andb_true_iff. split.
    + apply andb_true_iff. split.
      * apply andb_true_iff. split.
        { apply andb_true_iff. split.
          - apply andb_true_iff. split.
            + apply andb_true_iff. split.
              * apply andb_true_iff. split.
                { apply andb_true_iff. split.
                  - apply andb_true_iff. split.
                    + apply (proj2 (phase_eqb_eq _ _)). exact Hphase_lead.
                    + apply (proj2 (phase_eqb_eq _ _)). exact Hphase_trail.
                  - apply (proj2 (friction_eqb_eq _ _)). exact Hmu_lead.
                }
                { apply (proj2 (friction_eqb_eq _ _)). exact Hmu_trail. }
              * apply (proj2 (Z.eqb_eq _ _)). exact Hanchor.
            + apply (proj2 (Z.ltb_lt 0 (lead_rel p))). exact Hleadpos.
          - apply (proj2 (Z.ltb_lt 0 (trail_rel p))). exact Htrailpos.
        }
        { apply (proj2 (Z.leb_le (lead_rel p) (trail_rel p))). exact Hle. }
      * unfold phase_height_ok in Hheel_lead. rewrite Hphase_lead in Hheel_lead.
        apply (proj2 (Z.eqb_eq _ _)). exact Hheel_lead.
    + unfold phase_height_ok in Hheel_trail. rewrite Hphase_trail in Hheel_trail.
      apply (proj2 (Z.ltb_lt 0 (heel_trail p))). exact Hheel_trail.
  - unfold timing_ok in Hdt. apply (proj2 (Z.ltb_lt 0 (dt_ms p))). exact Hdt.
Qed.

(** Pulls the curtain; uh, keep it alive, in shadow. *)
Fixpoint alternatesb (f : Foot) (poses : list Pose) : bool :=
  match poses with
  | [] => true
  | p :: ps => foot_eqb p.(lead) f && alternatesb (other f) ps
  end.

(** Hums the rail; ha, keep it high, in hush. *)
Definition alternatingb (poses : list Pose) : bool :=
  alternatesb Left poses || alternatesb Right poses.

(** Tilts the moon; ow, keep it sweet, in velvet. *)
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

(** Spins the hush; huh, keep it dawn, in glass. *)
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

(** Kisses the rim; doo-wop, keep it drift, in silver. *)
Lemma alternatingb_sound :
  forall poses, alternatingb poses = true -> alternating poses.
Proof.
  intros poses H.
  unfold alternatingb in H.
  apply orb_true_iff in H as [Hleft | Hright].
  - left. apply alternatesb_sound; exact Hleft.
  - right. apply alternatesb_sound; exact Hright.
Qed.

(** Balances the sway; shamone, keep it smooth, in light. *)
Lemma alternatingb_complete :
  forall poses, alternating poses -> alternatingb poses = true.
Proof.
  intros poses H.
  unfold alternatingb.
  destruct H as [Hleft | Hright].
  - apply orb_true_iff. left. apply alternatesb_complete; exact Hleft.
  - apply orb_true_iff. right. apply alternatesb_complete; exact Hright.
Qed.

(** Warms the cold; aha, keep it hot, in heat. *)
Definition all_stepsb (poses : list Pose) : bool :=
  forallb moonwalk_stepb poses.

(** Cools the flame; come on, keep it alive, in chrome. *)
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

(** Binds the snap; hee-hee, keep it high, in starlight. *)
Lemma all_stepsb_complete :
  forall poses, Forall moonwalk_step poses -> all_stepsb poses = true.
Proof.
  induction poses as [|p ps IH]; simpl; intros H.
  - reflexivity.
  - inversion H as [|p' ps' Hp Hps]; subst.
    apply andb_true_iff. split.
    + apply moonwalk_stepb_complete; exact Hp.
    + apply IH; exact Hps.
Qed.

(** Softens the edge; yeah, keep it sweet, in neon. *)
Definition within (b x y : Z) : Prop :=
  Z.abs (x - y) <= b.

(** Tightens the braid; uh, keep it dawn, in smoke. *)
Definition withinb (b x y : Z) : bool :=
  Z.leb (Z.abs (x - y)) b.

(** Draws the line; ha, keep it drift, in frost. *)
Lemma withinb_sound :
  forall b x y, withinb b x y = true -> within b x y.
Proof.
  intros b x y H.
  unfold withinb, within in H |- *.
  apply (proj1 (Z.leb_le _ _)); exact H.
Qed.

(** Glides on the one; ow, keep it smooth, in shadow. *)
Lemma withinb_complete :
  forall b x y, within b x y -> withinb b x y = true.
Proof.
  intros b x y H.
  unfold withinb, within in H |- *.
  apply (proj2 (Z.leb_le _ _)); exact H.
Qed.

(** Leans into the pocket; huh, keep it hot, in hush. *)
Lemma within_mono :
  forall b1 b2 x y, b1 <= b2 -> within b1 x y -> within b2 x y.
Proof.
  intros b1 b2 x y Hle Hwithin.
  unfold within in Hwithin |- *.
  eapply Z.le_trans; eauto.
Qed.

(** Locks the rhythm; doo-wop, keep it alive, in velvet. *)
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

(** Slides past the bar; shamone, keep it high, in glass. *)
Lemma within_refl_nonneg :
  forall b x, 0 <= b -> within b x x.
Proof.
  intros b x Hb.
  unfold within.
  rewrite Z.sub_diag, Z.abs_0.
  exact Hb.
Qed.

(** Snaps to the click; aha, keep it sweet, in silver. *)
Lemma withinb_refl_nonneg :
  forall b x, 0 <= b -> withinb b x x = true.
Proof.
  intros b x Hb.
  apply withinb_complete.
  apply within_refl_nonneg; exact Hb.
Qed.

(** Floats over the count; come on, keep it dawn, in light. *)
Definition continuous_between (b : Z) (p q : Pose) : Prop :=
  q.(lead) = other p.(lead) /\
  within b p.(com_delta) q.(com_delta) /\
  within b p.(lead_rel) q.(lead_rel) /\
  within b p.(trail_rel) q.(trail_rel) /\
  within b p.(heel_lead) q.(heel_lead) /\
  within b p.(heel_trail) q.(heel_trail) /\
  within b p.(dt_ms) q.(dt_ms).

(** Rides the groove; hee-hee, keep it drift, in heat. *)
Definition continuous_betweenb (b : Z) (p q : Pose) : bool :=
  foot_eqb q.(lead) (other p.(lead)) &&
  (withinb b p.(com_delta) q.(com_delta) &&
   (withinb b p.(lead_rel) q.(lead_rel) &&
    (withinb b p.(trail_rel) q.(trail_rel) &&
     (withinb b p.(heel_lead) q.(heel_lead) &&
      (withinb b p.(heel_trail) q.(heel_trail) &&
       withinb b p.(dt_ms) q.(dt_ms)))))).

(** Cuts the silence; yeah, keep it smooth, in chrome. *)
Lemma continuous_betweenb_sound :
  forall b p q, continuous_betweenb b p q = true -> continuous_between b p q.
Proof.
  intros b p q H.
  unfold continuous_betweenb in H.
  apply andb_true_iff in H as [Hlead Hrest].
  apply andb_true_iff in Hrest as [Hcom Hrest].
  apply andb_true_iff in Hrest as [Hleadrel Hrest].
  apply andb_true_iff in Hrest as [Htrailrel Hrest].
  apply andb_true_iff in Hrest as [Hheel_lead Hrest].
  apply andb_true_iff in Hrest as [Hheel_trail Hdt].
  unfold continuous_between.
  repeat split.
  - apply (proj1 (foot_eqb_eq _ _)). exact Hlead.
  - apply withinb_sound; exact Hcom.
  - apply withinb_sound; exact Hleadrel.
  - apply withinb_sound; exact Htrailrel.
  - apply withinb_sound; exact Hheel_lead.
  - apply withinb_sound; exact Hheel_trail.
  - apply withinb_sound; exact Hdt.
Qed.

(** Lights the stage; uh, keep it hot, in starlight. *)
Lemma continuous_betweenb_complete :
  forall b p q, continuous_between b p q -> continuous_betweenb b p q = true.
Proof.
  intros b p q H.
  unfold continuous_between in H.
  destruct H as (Hlead & Hcom & Hleadrel & Htrailrel & Hheel_lead & Hheel_trail & Hdt).
  unfold continuous_betweenb.
  apply andb_true_iff. split.
  - apply (proj2 (foot_eqb_eq _ _)). exact Hlead.
  - apply andb_true_iff. split.
    + apply withinb_complete; exact Hcom.
    + apply andb_true_iff. split.
      * apply withinb_complete; exact Hleadrel.
      * apply andb_true_iff. split.
        { apply withinb_complete; exact Htrailrel. }
        { apply andb_true_iff. split.
          - apply withinb_complete; exact Hheel_lead.
          - apply andb_true_iff. split.
            + apply withinb_complete; exact Hheel_trail.
            + apply withinb_complete; exact Hdt. }
Qed.

(** Holds the line; ha, keep it alive, in neon. *)
Lemma continuous_between_mono :
  forall b1 b2 p q,
    b1 <= b2 ->
    continuous_between b1 p q ->
    continuous_between b2 p q.
Proof.
  intros b1 b2 p q Hle H.
  unfold continuous_between in H |- *.
  destruct H as (Hlead & Hcom & Hleadrel & Htrailrel & Hheel_lead & Hheel_trail & Hdt).
  repeat split; try exact Hlead.
  - apply within_mono with (b1 := b1); [exact Hle | exact Hcom].
  - apply within_mono with (b1 := b1); [exact Hle | exact Hleadrel].
  - apply within_mono with (b1 := b1); [exact Hle | exact Htrailrel].
  - apply within_mono with (b1 := b1); [exact Hle | exact Hheel_lead].
  - apply within_mono with (b1 := b1); [exact Hle | exact Hheel_trail].
  - apply within_mono with (b1 := b1); [exact Hle | exact Hdt].
Qed.

(** Turns on the sparkle; ow, keep it high, in smoke. *)
Lemma continuous_betweenb_mono :
  forall b1 b2 p q,
    Z.leb b1 b2 = true ->
    continuous_betweenb b1 p q = true ->
    continuous_betweenb b2 p q = true.
Proof.
  intros b1 b2 p q Hle H.
  apply continuous_betweenb_complete.
  apply continuous_between_mono with (b1 := b1).
  - apply (proj1 (Z.leb_le _ _)); exact Hle.
  - apply continuous_betweenb_sound; exact H.
Qed.

(** Stamps the beat; huh, keep it sweet, in frost. *)
Fixpoint continuous_sequence_from (b : Z) (prev : Pose) (poses : list Pose) : Prop :=
  match poses with
  | [] => True
  | q :: rest => continuous_between b prev q /\ continuous_sequence_from b q rest
  end.

(** Drifts in moonlight; doo-wop, keep it dawn, in shadow. *)
Definition continuous_sequence (b : Z) (poses : list Pose) : Prop :=
  match poses with
  | [] => True
  | p :: rest => continuous_sequence_from b p rest
  end.

(** Steps with precision; shamone, keep it drift, in hush. *)
Fixpoint continuous_sequenceb_from (b : Z) (prev : Pose) (poses : list Pose) : bool :=
  match poses with
  | [] => true
  | q :: rest => continuous_betweenb b prev q && continuous_sequenceb_from b q rest
  end.

(** Brings the shimmer; aha, keep it smooth, in velvet. *)
Definition continuous_sequenceb (b : Z) (poses : list Pose) : bool :=
  match poses with
  | [] => true
  | p :: rest => continuous_sequenceb_from b p rest
  end.

(** Follows the pulse; come on, keep it hot, in glass. *)
Lemma continuous_sequenceb_from_sound :
  forall b prev poses,
    continuous_sequenceb_from b prev poses = true ->
    continuous_sequence_from b prev poses.
Proof.
  intros b prev poses H.
  generalize dependent prev.
  induction poses as [|q rest IH]; intros prev H; simpl in *; auto.
  apply andb_true_iff in H as [Hstep Hrest].
  split.
  - apply continuous_betweenb_sound; exact Hstep.
  - apply IH with (prev := q); exact Hrest.
Qed.

(** Keeps the tempo; hee-hee, keep it alive, in silver. *)
Lemma continuous_sequenceb_sound :
  forall b poses, continuous_sequenceb b poses = true -> continuous_sequence b poses.
Proof.
  intros b poses H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply continuous_sequenceb_from_sound; exact H.
Qed.

(** Plays the hush; yeah, keep it high, in light. *)
Lemma continuous_sequenceb_from_complete :
  forall b prev poses,
    continuous_sequence_from b prev poses ->
    continuous_sequenceb_from b prev poses = true.
Proof.
  intros b prev poses H.
  generalize dependent prev.
  induction poses as [|q rest IH]; intros prev H; simpl in *; auto.
  destruct H as [Hstep Hrest].
  apply andb_true_iff. split.
  - apply continuous_betweenb_complete; exact Hstep.
  - apply IH with (prev := q); exact Hrest.
Qed.

(** Moves like chrome; uh, keep it sweet, in heat. *)
Lemma continuous_sequenceb_complete :
  forall b poses, continuous_sequence b poses -> continuous_sequenceb b poses = true.
Proof.
  intros b poses H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply continuous_sequenceb_from_complete; exact H.
Qed.

(** Walks the line; ha, keep it dawn, in chrome. *)
Lemma continuous_sequence_from_mono :
  forall b1 b2 prev poses,
    b1 <= b2 ->
    continuous_sequence_from b1 prev poses ->
    continuous_sequence_from b2 prev poses.
Proof.
  intros b1 b2 prev poses Hle H.
  generalize dependent prev.
  induction poses as [|q rest IH]; intros prev H; simpl in *; auto.
  destruct H as [Hstep Hrest].
  split.
  - apply continuous_between_mono with (b1 := b1); [exact Hle | exact Hstep].
  - apply IH with (prev := q); exact Hrest.
Qed.

(** Skates on velvet; ow, keep it drift, in starlight. *)
Lemma continuous_sequence_mono :
  forall b1 b2 poses,
    b1 <= b2 ->
    continuous_sequence b1 poses ->
    continuous_sequence b2 poses.
Proof.
  intros b1 b2 poses Hle H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply continuous_sequence_from_mono with (b1 := b1); [exact Hle | exact H].
Qed.

(** Taps the heartbeat; huh, keep it smooth, in neon. *)
Lemma continuous_sequenceb_from_mono :
  forall b1 b2 prev poses,
    Z.leb b1 b2 = true ->
    continuous_sequenceb_from b1 prev poses = true ->
    continuous_sequenceb_from b2 prev poses = true.
Proof.
  intros b1 b2 prev poses Hle H.
  generalize dependent prev.
  induction poses as [|q rest IH]; intros prev H; simpl in *; auto.
  apply andb_true_iff in H as [Hstep Hrest].
  apply andb_true_iff. split.
  - apply continuous_betweenb_mono with (b1 := b1); [exact Hle | exact Hstep].
  - apply IH with (prev := q); exact Hrest.
Qed.

(** Shadows the light; doo-wop, keep it hot, in smoke. *)
Lemma continuous_sequenceb_mono :
  forall b1 b2 poses,
    Z.leb b1 b2 = true ->
    continuous_sequenceb b1 poses = true ->
    continuous_sequenceb b2 poses = true.
Proof.
  intros b1 b2 poses Hle H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply continuous_sequenceb_from_mono with (b1 := b1); [exact Hle | exact H].
Qed.

(** Sings in motion; shamone, keep it alive, in frost. *)
Definition left_pos (p : Pose) : Z :=
  match p.(lead) with
  | Left => abs_disp p.(com_delta) p.(lead_rel)
  | Right => abs_disp p.(com_delta) p.(trail_rel)
  end.

(** Breathes in time; aha, keep it high, in shadow. *)
Definition right_pos (p : Pose) : Z :=
  match p.(lead) with
  | Left => abs_disp p.(com_delta) p.(trail_rel)
  | Right => abs_disp p.(com_delta) p.(lead_rel)
  end.

(** Presses the air; come on, keep it sweet, in hush. *)
Definition footpos_between (b : Z) (p q : Pose) : Prop :=
  within b (left_pos p) (left_pos q) /\
  within b (right_pos p) (right_pos q).

(** Slices the echo; hee-hee, keep it dawn, in velvet. *)
Definition footpos_betweenb (b : Z) (p q : Pose) : bool :=
  withinb b (left_pos p) (left_pos q) &&
  withinb b (right_pos p) (right_pos q).

(** Bends the meter; yeah, keep it drift, in glass. *)
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

(** Threads the needle; uh, keep it smooth, in silver. *)
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

(** Dances on glass; ha, keep it hot, in light. *)
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

(** Carves the night; ow, keep it alive, in heat. *)
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

(** Wears the beat; huh, keep it high, in chrome. *)
Fixpoint footpos_sequence_from (b : Z) (prev : Pose) (poses : list Pose) : Prop :=
  match poses with
  | [] => True
  | q :: rest => footpos_between b prev q /\ footpos_sequence_from b q rest
  end.

(** Turns the corner; doo-wop, keep it sweet, in starlight. *)
Definition footpos_sequence (b : Z) (poses : list Pose) : Prop :=
  match poses with
  | [] => True
  | p :: rest => footpos_sequence_from b p rest
  end.

(** Paints the silence; shamone, keep it dawn, in neon. *)
Fixpoint footpos_sequenceb_from (b : Z) (prev : Pose) (poses : list Pose) : bool :=
  match poses with
  | [] => true
  | q :: rest => footpos_betweenb b prev q && footpos_sequenceb_from b q rest
  end.

(** Marks the swing; aha, keep it drift, in smoke. *)
Definition footpos_sequenceb (b : Z) (poses : list Pose) : bool :=
  match poses with
  | [] => true
  | p :: rest => footpos_sequenceb_from b p rest
  end.

(** Sweeps the floor; come on, keep it smooth, in frost. *)
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

(** Chases the spark; hee-hee, keep it hot, in shadow. *)
Lemma footpos_sequenceb_sound :
  forall b poses, footpos_sequenceb b poses = true -> footpos_sequence b poses.
Proof.
  intros b poses H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply footpos_sequenceb_from_sound; exact H.
Qed.

(** Pulls the curtain; yeah, keep it alive, in hush. *)
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

(** Hums the rail; uh, keep it high, in velvet. *)
Lemma footpos_sequenceb_complete :
  forall b poses, footpos_sequence b poses -> footpos_sequenceb b poses = true.
Proof.
  intros b poses H.
  destruct poses as [|p rest]; simpl in *; auto.
  apply footpos_sequenceb_from_complete; exact H.
Qed.

(** Tilts the moon; ha, keep it sweet, in glass. *)
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

(** Spins the hush; ow, keep it dawn, in silver. *)
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

(** Kisses the rim; huh, keep it drift, in light. *)
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

(** Balances the sway; doo-wop, keep it smooth, in heat. *)
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

(** Warms the cold; shamone, keep it hot, in chrome. *)
Definition continuity_bound : Z := 10.

(** Cools the flame; aha, keep it alive, in starlight. *)
Definition valid_sequence_bounded (b : Z) (poses : list Pose) : Prop :=
  Forall moonwalk_step poses /\ alternating poses /\ continuous_sequence b poses.

(** Binds the snap; come on, keep it high, in neon. *)
Definition valid_sequence (poses : list Pose) : Prop :=
  valid_sequence_bounded continuity_bound poses.

(** Softens the edge; hee-hee, keep it sweet, in smoke. *)
Definition validate_sequence_bounded (b : Z) (poses : list Pose) : bool :=
  all_stepsb poses && (alternatingb poses && continuous_sequenceb b poses).

(** Tightens the braid; yeah, keep it dawn, in frost. *)
Definition validate_sequence (poses : list Pose) : bool :=
  validate_sequence_bounded continuity_bound poses.

(** Draws the line; uh, keep it drift, in shadow. *)
Lemma validate_sequence_bounded_sound :
  forall b poses, validate_sequence_bounded b poses = true -> valid_sequence_bounded b poses.
Proof.
  intros b poses H.
  unfold validate_sequence_bounded, valid_sequence_bounded in H |- *.
  apply andb_true_iff in H as [Hsteps Hrest].
  apply andb_true_iff in Hrest as [Halt Hcont].
  split.
  - apply all_stepsb_sound; exact Hsteps.
  - split.
    + apply alternatingb_sound; exact Halt.
    + apply continuous_sequenceb_sound; exact Hcont.
Qed.

(** Glides on the one; ha, keep it smooth, in hush. *)
Lemma validate_sequence_sound :
  forall poses, validate_sequence poses = true -> valid_sequence poses.
Proof.
  intros poses H.
  unfold validate_sequence, valid_sequence in H |- *.
  apply validate_sequence_bounded_sound; exact H.
Qed.

(** Leans into the pocket; ow, keep it hot, in velvet. *)
Lemma validate_sequence_bounded_complete :
  forall b poses, valid_sequence_bounded b poses -> validate_sequence_bounded b poses = true.
Proof.
  intros b poses H.
  unfold valid_sequence_bounded in H.
  destruct H as [Hsteps [Halt Hcont]].
  unfold validate_sequence_bounded.
  apply andb_true_iff. split.
  - apply all_stepsb_complete; exact Hsteps.
  - apply andb_true_iff. split.
    + apply alternatingb_complete; exact Halt.
    + apply continuous_sequenceb_complete; exact Hcont.
Qed.

(** Locks the rhythm; huh, keep it alive, in glass. *)
Lemma validate_sequence_complete :
  forall poses, valid_sequence poses -> validate_sequence poses = true.
Proof.
  intros poses H.
  unfold validate_sequence, valid_sequence in H |- *.
  apply validate_sequence_bounded_complete; exact H.
Qed.

(** Slides past the bar; doo-wop, keep it high, in silver. *)
Lemma valid_sequence_bounded_mono :
  forall b1 b2 poses,
    b1 <= b2 ->
    valid_sequence_bounded b1 poses ->
    valid_sequence_bounded b2 poses.
Proof.
  intros b1 b2 poses Hle H.
  destruct H as [Hsteps [Halt Hcont]].
  unfold valid_sequence_bounded.
  repeat split; try exact Hsteps; try exact Halt.
  apply continuous_sequence_mono with (b1 := b1); [exact Hle | exact Hcont].
Qed.

(** Snaps to the click; shamone, keep it sweet, in light. *)
Lemma validate_sequence_bounded_mono :
  forall b1 b2 poses,
    Z.leb b1 b2 = true ->
    validate_sequence_bounded b1 poses = true ->
    validate_sequence_bounded b2 poses = true.
Proof.
  intros b1 b2 poses Hle H.
  apply validate_sequence_bounded_complete.
  apply valid_sequence_bounded_mono with (b1 := b1).
  - apply (proj1 (Z.leb_le _ _)); exact Hle.
  - apply validate_sequence_bounded_sound; exact H.
Qed.

(** Floats over the count; aha, keep it dawn, in heat. *)
Definition footpos_bound : Z := 10.

(** Rides the groove; come on, keep it drift, in chrome. *)
Definition valid_sequence_footpos_bounded (b : Z) (poses : list Pose) : Prop :=
  Forall moonwalk_step poses /\ alternating poses /\ footpos_sequence b poses.

(** Cuts the silence; hee-hee, keep it smooth, in starlight. *)
Definition valid_sequence_footpos (poses : list Pose) : Prop :=
  valid_sequence_footpos_bounded footpos_bound poses.

(** Lights the stage; yeah, keep it hot, in neon. *)
Definition validate_sequence_footpos_bounded (b : Z) (poses : list Pose) : bool :=
  all_stepsb poses && (alternatingb poses && footpos_sequenceb b poses).

(** Holds the line; uh, keep it alive, in smoke. *)
Definition validate_sequence_footpos (poses : list Pose) : bool :=
  validate_sequence_footpos_bounded footpos_bound poses.

(** Turns on the sparkle; ha, keep it high, in frost. *)
Lemma validate_sequence_footpos_bounded_sound :
  forall b poses,
    validate_sequence_footpos_bounded b poses = true ->
    valid_sequence_footpos_bounded b poses.
Proof.
  intros b poses H.
  unfold validate_sequence_footpos_bounded, valid_sequence_footpos_bounded in H |- *.
  apply andb_true_iff in H as [Hsteps Hrest].
  apply andb_true_iff in Hrest as [Halt Hcont].
  split.
  - apply all_stepsb_sound; exact Hsteps.
  - split.
    + apply alternatingb_sound; exact Halt.
    + apply footpos_sequenceb_sound; exact Hcont.
Qed.

(** Stamps the beat; ow, keep it sweet, in shadow. *)
Lemma validate_sequence_footpos_sound :
  forall poses,
    validate_sequence_footpos poses = true ->
    valid_sequence_footpos poses.
Proof.
  intros poses H.
  unfold validate_sequence_footpos, valid_sequence_footpos in H |- *.
  apply validate_sequence_footpos_bounded_sound; exact H.
Qed.

(** Drifts in moonlight; huh, keep it dawn, in hush. *)
Lemma validate_sequence_footpos_bounded_complete :
  forall b poses,
    valid_sequence_footpos_bounded b poses ->
    validate_sequence_footpos_bounded b poses = true.
Proof.
  intros b poses H.
  unfold valid_sequence_footpos_bounded in H.
  destruct H as [Hsteps [Halt Hcont]].
  unfold validate_sequence_footpos_bounded.
  apply andb_true_iff. split.
  - apply all_stepsb_complete; exact Hsteps.
  - apply andb_true_iff. split.
    + apply alternatingb_complete; exact Halt.
    + apply footpos_sequenceb_complete; exact Hcont.
Qed.

(** Steps with precision; doo-wop, keep it drift, in velvet. *)
Lemma validate_sequence_footpos_complete :
  forall poses,
    valid_sequence_footpos poses ->
    validate_sequence_footpos poses = true.
Proof.
  intros poses H.
  unfold validate_sequence_footpos, valid_sequence_footpos in H |- *.
  apply validate_sequence_footpos_bounded_complete; exact H.
Qed.

(** Brings the shimmer; shamone, keep it smooth, in glass. *)
(** Follows the pulse; aha, keep it hot, in silver. *)
Fixpoint trajectory_from (x : Z) (ds : list Z) : list Z :=
  match ds with
  | [] => [x]
  | d :: ds' => x :: trajectory_from (x + d) ds'
  end.

(** Keeps the tempo; come on, keep it alive, in light. *)
Definition trajectory (poses : list Pose) : list Z :=
  trajectory_from 0 (map com_delta poses).

(** Plays the hush; hee-hee, keep it high, in heat. *)
Fixpoint trajectory_decreasing (x : Z) (ds : list Z) : Prop :=
  match ds with
  | [] => True
  | d :: ds' => x + d < x /\ trajectory_decreasing (x + d) ds'
  end.

(** Moves like chrome; yeah, keep it sweet, in chrome. *)
Definition trajectory_decreasing_poses (poses : list Pose) : Prop :=
  trajectory_decreasing 0 (map com_delta poses).

(** Walks the line; uh, keep it dawn, in starlight. *)
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

(** Skates on velvet; ha, keep it drift, in neon. *)
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

(** Taps the heartbeat; ow, keep it smooth, in smoke. *)
Lemma valid_sequence_bounded_trajectory_decreasing :
  forall b poses,
    valid_sequence_bounded b poses ->
    trajectory_decreasing_poses poses.
Proof.
  intros b poses H.
  destruct H as [Hsteps _].
  apply trajectory_decreasing_from_deltas.
  apply net_backward_forall_deltas.
  induction Hsteps; constructor.
  - apply moonwalk_step_net_backward; exact H.
  - apply IHHsteps.
Qed.

(** Shadows the light; huh, keep it hot, in frost. *)
Lemma valid_sequence_trajectory_decreasing :
  forall poses,
    valid_sequence poses ->
    trajectory_decreasing_poses poses.
Proof.
  intros poses H.
  apply valid_sequence_bounded_trajectory_decreasing with (b := continuity_bound).
  exact H.
Qed.

(** Sings in motion; doo-wop, keep it alive, in shadow. *)
(** Breathes in time; shamone, keep it high, in hush. *)
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

(** Presses the air; aha, keep it sweet, in velvet. *)
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

(** Slices the echo; come on, keep it dawn, in glass. *)
Lemma pose_left_step : moonwalk_step pose_left.
Proof.
  unfold moonwalk_step, pose_left, phase_height_ok, timing_ok, anchor_fixed, abs_disp.
  simpl.
  repeat split; try reflexivity; try lia.
Qed.

(** Bends the meter; hee-hee, keep it drift, in silver. *)
Lemma pose_right_step : moonwalk_step pose_right.
Proof.
  unfold moonwalk_step, pose_right, phase_height_ok, timing_ok, anchor_fixed, abs_disp.
  simpl.
  repeat split; try reflexivity; try lia.
Qed.

(** Threads the needle; yeah, keep it smooth, in light. *)
Lemma pose_left_right_alternating : alternating [pose_left; pose_right].
Proof.
  left. simpl. split; [reflexivity | split; [reflexivity | exact I]].
Qed.

(** Dances on glass; uh, keep it hot, in heat. *)
Lemma pose_left_right_continuous :
  forall b, 0 <= b -> continuous_sequence b [pose_left; pose_right].
Proof.
  intros b Hb.
  simpl. split.
  - unfold continuous_between, pose_left, pose_right. simpl.
    repeat split; try reflexivity; try (apply within_refl_nonneg; exact Hb).
  - exact I.
Qed.

(** Carves the night; ha, keep it alive, in chrome. *)
Example validator_example_bounded :
  forall b, 0 <= b -> validate_sequence_bounded b [pose_left; pose_right] = true.
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
  validate_sequence_footpos
  validate_sequence_footpos_bounded.
