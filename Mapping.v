From RelAcqProof Require Import Executions.
From RelAcqProof Require Import Events.   
From RelAcqProof Require Import Arm.
From RelAcqProof Require Import X86.
From hahn Require Import Hahn.  

(* *************************** Map from X86 to Arm ************************* *)
Definition map_label_x86_arm (lab_x86: LabelX86): LabelArm := 
match lab_x86 with
| W_x86 loc val => W_Rel loc val 
| R_x86 loc val => R_Acq_Pc loc val 
end.

Definition map_label_x86_arm_rmw (lab_x86: LabelX86): LabelArm := 
match lab_x86 with
| W_x86 loc val => W_Rel loc val 
| R_x86 loc val => R_Acq loc val 
end. 

Definition map_event_X86_Arm
    (execX86 : @Execution LabelX86 LabelClassX86)
    (e_x86   : @Event LabelX86 LabelClassX86)
    (e_arm   : @Event LabelArm LabelClassArm) : Prop :=
  match e_x86 with
  | EventInit uid lab =>
         (~(dom_rel (rmw execX86) e_x86)  /\ e_arm = EventInit uid (map_label_x86_arm lab))
      \/ ( (dom_rel (rmw execX86) e_x86)  /\ e_arm = EventInit uid (map_label_x86_arm_rmw lab))
  | EventThread uid tid lab =>
        (~(dom_rel (rmw execX86) e_x86) /\ e_arm = EventThread uid tid (map_label_x86_arm lab))
      \/ ((dom_rel (rmw execX86) e_x86) /\ e_arm = EventThread uid tid (map_label_x86_arm_rmw lab))
  end. 

Definition map_exec_X86_Arm (execX86:@Execution LabelX86 LabelClassX86):@Execution LabelArm LabelClassArm := {|
    events := fun e => exists x, events execX86 x /\ map_event_X86_Arm execX86 x e;
    po     := fun e1 e2 => exists x y, po execX86 x y  /\ map_event_X86_Arm execX86 x e1 /\ map_event_X86_Arm execX86 y e2;
    rf     := fun e1 e2 => exists x y, rf execX86 x y  /\ map_event_X86_Arm execX86 x e1 /\ map_event_X86_Arm execX86 y e2;
    mo     := fun e1 e2 => exists x y, mo execX86 x y  /\ map_event_X86_Arm execX86 x e1 /\ map_event_X86_Arm execX86 y e2; 
    rmw    := fun e1 e2 => exists x y, rmw execX86 x y /\ map_event_X86_Arm execX86 x e1 /\ map_event_X86_Arm execX86 y e2;  
|}. 

(* ************************** Map from Arm to X86 *************************** *)
Definition map_label_Arm_X86 (lab_Arm: LabelArm): LabelX86 := 
match lab_Arm with
| W_Rel loc val => W_x86 loc val  
| R_Acq_Pc loc val => R_x86 loc val
| R_Acq loc val => R_x86 loc val  
end. 

Definition map_event_Arm_X86 (event_Arm:@Event LabelArm LabelClassArm):@Event LabelX86 LabelClassX86 := 
match event_Arm with 
| EventInit uid lab => EventInit uid (map_label_Arm_X86 lab)
| EventThread uid tid lab => EventThread uid tid (map_label_Arm_X86 lab)
end. 

Definition map_exec_Arm_X86 (execArm:@Execution LabelArm LabelClassArm):@Execution LabelX86 LabelClassX86 := {|
    events := fun e => exists e', events execArm e' /\ e = map_event_Arm_X86 e';
    po     := fun e1 e2 => exists x y, po execArm x y /\ e1 = map_event_Arm_X86 x /\ e2 = map_event_Arm_X86 y;
    rf     := fun e1 e2 => exists x y, rf execArm x y /\ e1 = map_event_Arm_X86 x /\ e2 = map_event_Arm_X86 y;
    mo     := fun e1 e2 => exists x y, mo execArm x y /\ e1 = map_event_Arm_X86 x /\ e2 = map_event_Arm_X86 y; 
    rmw    := fun e1 e2 => exists x y, rmw execArm x y /\ e1 = map_event_Arm_X86 x /\ e2 = map_event_Arm_X86 y;  
|}. 
(* *************************** Mapping Lemmas ****************************** *)

Lemma mapping_preserves_writes_arm: forall (e:@Event LabelArm LabelClassArm), 
    (is_w (event_label e)) 
    <-> 
    let eX86 := (map_event_Arm_X86 e) in 
        (is_w (event_label eX86)).
Proof with eauto. 
    intros.
    split. 
    - intros.  
      -- simpl. destruct e eqn:E; subst; destruct lab eqn:E0; subst; simpl... 
    - intros.  
      -- destruct e eqn:E0; destruct lab eqn:E1; subst; simpl in H. all:try(simpl; eauto).
Qed. 


Lemma mapping_preserves_writes_x86: 
    forall (execX86 : @Execution LabelX86 LabelClassX86)
           (e    : @Event LabelX86 LabelClassX86)
           (eArm : @Event LabelArm LabelClassArm),
    map_event_X86_Arm execX86 e eArm ->
        is_w (event_label e) <-> is_w (event_label eArm).
Proof with eauto.
    intros execX86 e eArm Hmap.
    unfold map_event_X86_Arm in Hmap.
    destruct e; destruct lab;
    destruct Hmap as [[Hnot Heq] | [Hrmw Heq]];
    subst; simpl; split; intros H...
Qed. 

Lemma mapping_preserves_reads_arm: forall  (e:@Event LabelArm LabelClassArm), 
    (is_r (event_label e)) 
    <-> 
    let eX86 := (map_event_Arm_X86 e) in 
        (is_r (event_label eX86)).
Proof with eauto. 
    intros.
    split. 
    - intros.  
      -- simpl. destruct e eqn:E; subst; destruct lab eqn:E0; subst; simpl... 
    - intros.  
      -- destruct e eqn:E0; destruct lab eqn:E1; subst; simpl in H. all:try(simpl; eauto).
Qed. 


Lemma mapping_preserves_reads_x86: 
    forall (execX86 : @Execution LabelX86 LabelClassX86)
           (e    : @Event LabelX86 LabelClassX86)
           (eArm : @Event LabelArm LabelClassArm),
    map_event_X86_Arm execX86 e eArm -> 
        ((is_r (event_label e)) <-> (is_r (event_label eArm))). 
Proof with eauto. 
    intros execX86 e eArm Hmap. 
    unfold map_event_X86_Arm in Hmap. 
    destruct e; destruct lab;
    destruct Hmap as [[Hnot Heq] | [Hrmw Heq]]; 
    subst; simpl; split; intros H...    
Qed. 

Lemma mapping_preserves_location_arm: forall (e:Event),
    lab_loc (event_label e) = lab_loc (event_label (map_event_Arm_X86 e)).
Proof.
    intros.
    simpl.
    destruct e; destruct lab; simpl; reflexivity.
Qed. 

Lemma mapping_preserves_location_x86: 
    forall (execX86 : @Execution LabelX86 LabelClassX86)
           (e    : @Event LabelX86 LabelClassX86)
           (eArm : @Event LabelArm LabelClassArm),
    map_event_X86_Arm execX86 e eArm -> 
        lab_loc (event_label e) = lab_loc (event_label eArm).
Proof.
    intros execX86 e eArm Hmap. 
    unfold map_event_X86_Arm in Hmap. 
    destruct e; destruct lab;
    destruct Hmap as [[Hnot Heq] | [Hrmw Heq]]; 
    subst; simpl; split; intros H... 
Qed. 

Lemma mapping_preserves_value_arm: forall (e:Event),
    lab_val (event_label e) = lab_val (event_label (map_event_Arm_X86 e)).
Proof.
    intros.
    simpl.
    destruct e; destruct lab; simpl; reflexivity.
Qed.


Lemma mapping_preserves_value_x86: 
    forall (execX86 : @Execution LabelX86 LabelClassX86)
           (e    : @Event LabelX86 LabelClassX86)
           (eArm : @Event LabelArm LabelClassArm),
    map_event_X86_Arm execX86 e eArm -> 
        lab_val (event_label e) = lab_val (event_label eArm).
Proof.
    intros execX86 e eArm Hmap. 
    unfold map_event_X86_Arm in Hmap. 
    destruct e; destruct lab;
    destruct Hmap as [[Hnot Heq] | [Hrmw Heq]]; 
    subst; simpl; split; intros H... 
Qed. 

Lemma mapping_preserves_both_write_x86:
    forall (execX86 : @Execution LabelX86 LabelClassX86)
           (e1 e2   : @Event LabelX86 LabelClassX86)
           (e1Arm e2Arm : @Event LabelArm LabelClassArm),
    map_event_X86_Arm execX86 e1 e1Arm ->
    map_event_X86_Arm execX86 e2 e2Arm ->
    both_write e1Arm e2Arm <-> both_write e1 e2.
Proof with eauto.
    intros execX86 e1 e2 e1Arm e2Arm Hmap1 Hmap2.
    unfold both_write.
    rewrite <- (mapping_preserves_writes_x86 execX86 e1 e1Arm Hmap1).
    rewrite <- (mapping_preserves_writes_x86 execX86 e2 e2Arm Hmap2).
    split; eauto.
Qed.

Lemma mapping_preserves_both_write_arm:
    forall (e1 e2 : @Event LabelArm LabelClassArm),
    both_write (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) <-> both_write e1 e2.
Proof with eauto.
    intros e1 e2.
    unfold both_write.
    rewrite <- mapping_preserves_writes_arm.
    rewrite <- mapping_preserves_writes_arm.
    split; eauto.
Qed.

Lemma mapping_preserves_same_loc_x86:
    forall (execX86 : @Execution LabelX86 LabelClassX86)
           (e1 e2   : @Event LabelX86 LabelClassX86)
           (e1Arm e2Arm : @Event LabelArm LabelClassArm),
    map_event_X86_Arm execX86 e1 e1Arm ->
    map_event_X86_Arm execX86 e2 e2Arm ->
    same_loc e1Arm e2Arm <-> same_loc e1 e2.
Proof with eauto.
    intros execX86 e1 e2 e1Arm e2Arm Hmap1 Hmap2.
    unfold same_loc.
    rewrite <- (mapping_preserves_location_x86 execX86 e1 e1Arm Hmap1).
    rewrite <- (mapping_preserves_location_x86 execX86 e2 e2Arm Hmap2).
    split; eauto.
Qed.

Lemma mapping_preserves_same_loc_arm:
    forall (e1 e2 : @Event LabelArm LabelClassArm),
    same_loc (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) <-> same_loc e1 e2.
Proof with eauto.
    intros e1 e2.
    unfold same_loc.
    rewrite <- mapping_preserves_location_arm.
    rewrite <- mapping_preserves_location_arm.
    split; eauto.
Qed.

Lemma mapping_preserves_same_val_x86:
    forall (execX86 : @Execution LabelX86 LabelClassX86)
           (e1 e2   : @Event LabelX86 LabelClassX86)
           (e1Arm e2Arm : @Event LabelArm LabelClassArm),
    map_event_X86_Arm execX86 e1 e1Arm ->
    map_event_X86_Arm execX86 e2 e2Arm ->
    same_val e1Arm e2Arm <-> same_val e1 e2.
Proof with eauto.
    intros execX86 e1 e2 e1Arm e2Arm Hmap1 Hmap2.
    unfold same_val.
    rewrite <- (mapping_preserves_value_x86 execX86 e1 e1Arm Hmap1).
    rewrite <- (mapping_preserves_value_x86 execX86 e2 e2Arm Hmap2).
    split; eauto.
Qed.

Lemma mapping_preserves_same_val_arm:
    forall (e1 e2 : @Event LabelArm LabelClassArm),
    same_val (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) <-> same_val e1 e2.
Proof with eauto.
    intros e1 e2.
    unfold same_val.
    rewrite <- mapping_preserves_value_arm.
    rewrite <- mapping_preserves_value_arm.
    split; eauto.
Qed.

Lemma map_label_x86_arm_injective:
  forall l l0,
  map_label_x86_arm l = map_label_x86_arm l0 ->
  l = l0.
Proof with eauto. 
    intros. 
    destruct l, l0; simpl in H. 
    all:try(inversion H; injection H; intros; subst; reflexivity). 
Qed.

Lemma map_label_x86_arm_rmw_injective:
  forall l l0,
  map_label_x86_arm_rmw l = map_label_x86_arm_rmw l0 ->
  l = l0.
Proof with eauto. 
    intros. 
    destruct l, l0; simpl in H. 
    all:try(inversion H; injection H; intros; subst; reflexivity). 
Qed.

Lemma mapping_preserves_events_arm:
    forall execArm e,
        events execArm e -> events (map_exec_Arm_X86 execArm) (map_event_Arm_X86 e). 
Proof with eauto.
    intros. simpl. exists e... 
Qed.


Lemma mapping_preserves_po: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    (po execArm) e1 e2 -> (po (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).  
Proof with eauto. 
    intros. simpl. exists e1, e2... 
Qed. 

Lemma mapping_preserves_mo_arm: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    (mo execArm) e1 e2 -> (mo (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).  
Proof with eauto. 
    intros.  unfold mo. simpl. exists e1, e2...
Qed.

Lemma mapping_preserves_mo_x86: forall(execX86:@Execution LabelX86 LabelClassX86) (e1X86 e2X86:Event), 
    (mo execX86) e1X86 e2X86 -> exists e1Arm e2Arm, map_event_X86_Arm execX86 e1X86 e1Arm /\ map_event_X86_Arm execX86 e2X86 e2Arm /\ (mo (map_exec_X86_Arm execX86)) (e1Arm) (e2Arm).  
Proof with eauto. 
    intros execX86 e1X86 e2X86 Hmo.
    unfold map_event_X86_Arm.
    destruct (classic (dom_rel (rmw execX86) e1X86)) as [Hrmw1 | Hnot1];
    destruct (classic (dom_rel (rmw execX86) e2X86)) as [Hrmw2 | Hnot2];
    destruct e1X86; destruct e2X86; destruct lab; destruct lab0.   
    all: eexists; eexists; repeat split.
    all: try (right; split; eauto; fail).
    all: try (left;  split; eauto; fail).
    all: try (right; split; eauto; fail).
    all: try (left;  split; eauto; fail).
    all: simpl; do 2 eexists; repeat split...
    all: try (right; split; eauto; fail).
    all: try (left;  split; eauto; fail).
Qed. 

Lemma mapping_preserves_rf: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    (rf execArm) e1 e2 -> (rf (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).  
Proof with eauto. 
    intros. simpl. exists e1, e2...  
Qed. 

Lemma mapping_preserves_rmw: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    (rmw execArm) e1 e2 -> (rmw (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).  
Proof with eauto. 
    intros.  unfold mo. simpl. exists e1, e2... 
Qed. 

Lemma mapping_preserves_fr: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    (fr execArm) e1 e2 -> (fr (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).  
Proof with eauto. 
    intros. unfold fr in H; unfold fr; unfold HahnRelationsBasic.seq in H; destruct H as [z [H0 H1]];
    unfold Relation_Operators.transp in H0; unfold HahnRelationsBasic.seq; unfold Relation_Operators.transp.
    - exists (map_event_Arm_X86 z). split. 
        -- apply mapping_preserves_rf...   
        -- apply mapping_preserves_mo_arm... 
Qed.

Lemma mapping_preserves_both_write_equal_arm: forall (e0 e1:Event),
    both_write e0 e1 -> e0 = e1 <-> (map_event_Arm_X86 e0) = (map_event_Arm_X86 e1).   
Proof with eauto.  
    intros.  destruct e0, e1; destruct lab, lab0; unfold both_write in H; destruct H; simpl in H; inversion H;
    inversion H0; simpl; split; intros; inversion H1; eauto.     
Qed. 

Lemma mapping_preserves_both_write_different_arm: forall (e0 e1:Event),
    both_write e0 e1 -> e0 <> e1 -> (map_event_Arm_X86 e0) <> (map_event_Arm_X86 e1).   
Proof with eauto.  
    intros. destruct e0, e1; destruct lab, lab0; remember H as H'; unfold both_write in H; destruct H.  all:try(simpl in H; eauto;fail); 
    unfold not in *;  intros; apply H0; apply <- mapping_preserves_both_write_equal_arm; eauto.     
Qed.

Lemma map_event_Arm_X86_preserves_uid:
    forall (e : @Event LabelArm LabelClassArm),
    event_uid (map_event_Arm_X86 e) = event_uid e.
Proof with eauto.
    intros e. destruct e; destruct lab; simpl...
Qed.

Lemma map_event_Arm_X86_injective:
    forall (execArm : @Execution LabelArm LabelClassArm)
           (e1 e2 : @Event LabelArm LabelClassArm),
    uid_unique execArm ->
    events execArm e1 ->
    events execArm e2 ->
    map_event_Arm_X86 e1 = map_event_Arm_X86 e2 -> e1 = e2.
Proof with eauto.
    intros execArm e1 e2 Huniq He1 He2 Heq. 
    apply Huniq...
    rewrite <- map_event_Arm_X86_preserves_uid. 
    rewrite <- map_event_Arm_X86_preserves_uid. 
    rewrite Heq...
Qed.

Lemma map_event_X86_Arm_preserves_uid:
    forall (execX86 : @Execution LabelX86 LabelClassX86)
           (e : @Event LabelX86 LabelClassX86)
           (eArm : @Event LabelArm LabelClassArm),
    map_event_X86_Arm execX86 e eArm ->
    event_uid eArm = event_uid e.
Proof with eauto.
    intros execX86 e eArm Hmap.
    unfold map_event_X86_Arm in Hmap.
    destruct e; destruct lab;
    destruct Hmap as [[_ Heq] | [_ Heq]];
    subst; simpl...
Qed.

Lemma map_event_X86_Arm_injective:
    forall (execX86 : @Execution LabelX86 LabelClassX86)
           (e1 e2 : @Event LabelX86 LabelClassX86)
           (eArm : @Event LabelArm LabelClassArm),
    uid_unique execX86 ->
    events execX86 e1 ->
    events execX86 e2 ->
    map_event_X86_Arm execX86 e1 eArm ->
    map_event_X86_Arm execX86 e2 eArm ->
    e1 = e2.
Proof with eauto.
    intros execX86 e1 e2 eArm Huniq He1 He2 Hmap1 Hmap2.
    apply Huniq...
    rewrite <- (map_event_X86_Arm_preserves_uid execX86 e1 eArm Hmap1).
    rewrite <- (map_event_X86_Arm_preserves_uid execX86 e2 eArm Hmap2)...
Qed.

Lemma map_exec_Arm_X86_preserves_uid_unique:
    forall (execArm : @Execution LabelArm LabelClassArm),
    uid_unique execArm -> uid_unique (map_exec_Arm_X86 execArm).
Proof with eauto.
    intros execArm Huniq.
    unfold uid_unique in *.
    intros e1 e2 He1 He2 Huid.
    simpl in He1, He2.
    destruct He1 as [x [Hx Heq1]].
    destruct He2 as [y [Hy Heq2]].
    subst.
    repeat rewrite map_event_Arm_X86_preserves_uid in Huid.
    specialize (Huniq x y Hx Hy Huid)...
    subst...
Qed.

Lemma map_exec_Arm_X86_preserves_well_formed_po:
    forall (execArm : @Execution LabelArm LabelClassArm),
    well_formed_po execArm -> well_formed_po (map_exec_Arm_X86 execArm).
Proof with eauto.
    intros execArm Hwf_po.
    unfold well_formed_po in *.
    destruct Hwf_po as [Hpo_events Hpo_connected].
    split.
    - (* po relates only events in the execution *)
      intros e1 e2 Hpo.
      simpl in Hpo.
      destruct Hpo as [x [y [Hpo [Heqx Heqy]]]]; subst.
      destruct (Hpo_events x y Hpo) as [Hevx Hevy].
      split.
      + simpl. exists x. split...
      + simpl. exists y. split...
    - (* every event is connected to at least one other via po *)
      intros e.
      split.
      + intros He.
        simpl in He.
        destruct He as [x [Hevx Heqx]]; subst.
        apply Hpo_connected in Hevx.
        destruct Hevx as [e0 [Hev0 Hpo]].
        exists (map_event_Arm_X86 e0).
        split.
        * simpl. exists e0. split...
        * destruct Hpo as [Hpo | Hpo].
          -- left.  simpl. exists x, e0. split...
          -- right. simpl. exists e0, x. split...
      + intros [e' [He' Hpo]].
        simpl in He', Hpo.
        destruct He' as [x [Hevx Heqx]]; subst.
        destruct Hpo as [Hpo | Hpo].
        * destruct Hpo as [x1 [y1 [Hpo [Heq1 Heq2]]]]; subst.
          destruct (Hpo_events x1 y1 Hpo) as [Hevx1 Hevy1].
          simpl. exists x1. split...
        * destruct Hpo as [x1 [y1 [Hpo [Heq1 Heq2]]]]; subst.
          destruct (Hpo_events x1 y1 Hpo) as [Hevx1 Hevy1].
          simpl. exists y1. split...
Qed.

Lemma map_exec_Arm_X86_preserves_well_formed_mo:
    forall (execArm : @Execution LabelArm LabelClassArm),
    well_formed_mo execArm -> well_formed_mo (map_exec_Arm_X86 execArm).
Proof with eauto.
    intros execArm Hwf_mo.
    unfold well_formed_mo in *.
    intros e1X86 e2X86 Hmo.
    simpl in Hmo. 
    destruct Hmo as [x [y [Hmo [Heq1 Heq2]]]]; subst. 
    destruct (Hwf_mo x y Hmo) as [Hev1 [Hev2 [Hbw [Hsl Hneq]]]].  
    split; [| split; [| split; [| split]]].
    - apply mapping_preserves_events_arm...
    - apply mapping_preserves_events_arm...    
    - apply mapping_preserves_both_write_arm...
    - apply mapping_preserves_same_loc_arm...
    - apply mapping_preserves_both_write_different_arm...
Qed.

Lemma map_exec_Arm_X86_preserves_well_formed_rf:
    forall (execArm : @Execution LabelArm LabelClassArm),
    uid_unique execArm ->
    well_formed_rf execArm -> well_formed_rf (map_exec_Arm_X86 execArm).
Proof with eauto. 
    intros execArm Huniq Hwf_rf. 
    unfold well_formed_rf in *. 
    intros w r Hrf.
    simpl in Hrf.
    destruct Hrf as [x [y [Hrf [Heqx Heqy]]]]; subst.
    destruct (Hwf_rf x y Hrf) as [Hew [Her [Hiw [Hir [Hsl [Hsv Huniq']]]]]].
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    - (* events w *)
      simpl. exists x. split...
    - (* events r *)
      simpl. exists y. split...
    - (* is_w *)
      apply mapping_preserves_writes_arm...
    - (* is_r *)
      apply mapping_preserves_reads_arm...
    - (* same_loc *)
      apply mapping_preserves_same_loc_arm...
    - (* same_val *)
      apply mapping_preserves_same_val_arm...
    - (* uniqueness *)
      intros w0 Hw0 Hrf0.
      simpl in Hrf0.
      destruct Hrf0 as [x0 [y0 [Hrf0 [Heqx0 Heqy0]]]]; subst.
      destruct (Hwf_rf x0 y0 Hrf0) as [Hew0 [Her0 _]].
      apply (map_event_Arm_X86_injective execArm y y0 Huniq Her) in Heqy0...
      subst.
      assert (Hx0x : x0 = x).
      { apply Huniq'.
        - apply mapping_preserves_writes_arm in Hw0...
        - exact Hrf0. }
      subst...
Qed.

Lemma po_in_events_l : forall (execArm : @Execution LabelArm LabelClassArm) x y,
    well_formed_po execArm -> po execArm x y ->  events execArm x.
Proof with eauto.
    intros. unfold well_formed_po in *. destruct H as [H1 H2]. apply H1 in H0. destruct H0 as [H0 _]...
Qed.

Lemma po_in_events_r : forall (execArm : @Execution LabelArm LabelClassArm) x y,
    well_formed_po execArm -> po execArm x y -> events execArm y.
Proof with eauto.
    intros. unfold well_formed_po in *. destruct H as [H1 H2]. apply H1 in H0. destruct H0 as [_ H0]...
Qed.  

Lemma mapping_preserves_poimm: 
    forall (execArm : @Execution LabelArm LabelClassArm) 
           (e1 e2 : @Event LabelArm LabelClassArm),
    uid_unique execArm ->
    well_formed_po execArm -> 
    poimm execArm e1 e2 -> 
    poimm (map_exec_Arm_X86 execArm) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).
Proof with eauto.
    intros execArm e1 e2 Huniq Hwf_po [Hpo Hnot].
    unfold poimm. split.
    - apply mapping_preserves_po...
    - intros [e3 [Hpo1 Hpo2]]. 
      apply Hnot. 
      simpl in Hpo1, Hpo2. 
      destruct Hpo1 as [x [y [Hpo1 [Heqx Heqy]]]]. 
      destruct Hpo2 as [x' [y' [Hpo2 [Heqx' Heqy']]]]. 
      subst. 
      assert (Heq : map_event_Arm_X86 y = map_event_Arm_X86 x') by congruence. 
      assert (Hevx  : events execArm x)  by (eapply po_in_events_l;  eauto). 
      assert (Hevy  : events execArm y)  by (eapply po_in_events_r; eauto).
      assert (Hevx' : events execArm x') by (eapply po_in_events_l; eauto).
      assert (Hevy' : events execArm y') by (eapply po_in_events_r; eauto). 
      apply (map_event_Arm_X86_injective execArm y x' Huniq Hevy Hevx') in Heq. 
      assert (He1x : x = e1).
      { apply (map_event_Arm_X86_injective execArm x e1 Huniq Hevx).
        - eapply po_in_events_l; eauto.
        - congruence. }
      assert (He2y' : y' = e2).
      { apply (map_event_Arm_X86_injective execArm y' e2 Huniq Hevy').
        - eapply po_in_events_r; eauto.
        - congruence. }
      subst...
Qed.

Lemma map_exec_Arm_X86_preserves_well_formed_rmw:
    forall (execArm : @Execution LabelArm LabelClassArm),
        uid_unique execArm ->
            well_formed_po execArm ->
                well_formed_rmw execArm -> 
                    well_formed_rmw (map_exec_Arm_X86 execArm).
Proof with eauto. 
    unfold well_formed_rmw in *. intros. simpl in H2. 
    destruct H2 as [x [y [H2 [H5 H6]]]]. apply H1 in H2. 
    destruct H2 as [H7 [H8 [H9 [H10 [H11 H12]]]]]. 
    split; [| split; [| split; [| split; [| split]]]];
    subst. 
    apply mapping_preserves_events_arm...   
    apply mapping_preserves_events_arm... 
    rewrite <- mapping_preserves_reads_arm... 
    rewrite <- mapping_preserves_writes_arm...   
    apply mapping_preserves_poimm...
    apply mapping_preserves_same_loc_arm...
Qed.

Lemma mapping_preserves_well_formedness: forall (execArm:@Execution LabelArm LabelClassArm), 
    well_formed execArm -> well_formed (map_exec_Arm_X86 execArm).
Proof with eauto. 
    intros execArm Hwf.
    unfold well_formed in *. 
    destruct Hwf as [H0 [H1 [H2 [H3 H4]]]]. 
    split; [| split; [| split; [| split]]]. 
    apply map_exec_Arm_X86_preserves_uid_unique... 
    apply map_exec_Arm_X86_preserves_well_formed_po...  
    apply map_exec_Arm_X86_preserves_well_formed_mo... 
    apply map_exec_Arm_X86_preserves_well_formed_rf...
    apply map_exec_Arm_X86_preserves_well_formed_rmw... 
Qed.

Lemma mapping_preserves_behaviour: forall (execArm:@Execution LabelArm LabelClassArm) (l:Location) (v:Value), 
    well_formed execArm -> (behaviour (execArm) (l, v) <-> behaviour (map_exec_Arm_X86 execArm) (l, v)).  
Proof with eauto.
    intros execArm l v Hwf.  
    unfold behaviour. 
    split. 
    - intros. destruct H as [e]. destruct H as [H1 [H2 [H3 [H4 H5]]]]. 
      exists (map_event_Arm_X86 e). repeat split.
      -- simpl. exists e. split... 
      -- assert (H6: events execArm e /\ is_w (event_label e)). { eauto. } 
         rewrite mapping_preserves_writes_arm in H6. destruct H6 as [_ H6]...
      -- rewrite <- mapping_preserves_location_arm. apply H3.
      -- rewrite <- mapping_preserves_value_arm. apply H4.
      -- unfold not. intros. unfold not in H5. 
         apply H5. destruct H. simpl in H.  destruct H as [x0 [y0 [H6 [H7 H8]]]].   
         exists y0. subst.  unfold well_formed in Hwf. destruct Hwf as [Huid [Hpo [Hmo [_ _]]]];
         apply (map_event_Arm_X86_injective execArm) in H7; subst... 
         unfold well_formed_mo in *. apply Hmo in H6. destruct H6 as [Hevx0 [Hevy0 _]]...  
    - intros. destruct H as [e]. destruct H as [H1 [H2 [H3 [H4 H5]]]].
      simpl in H1. destruct H1 as [x [H6 H7]].    
      exists (x). repeat split... subst... rewrite mapping_preserves_writes_arm... 
      rewrite H7 in H3. rewrite <- mapping_preserves_location_arm in H3... 
      rewrite H7 in H4. rewrite <- mapping_preserves_value_arm in H4... 
      unfold not in *. intros. apply H5. destruct H. subst. apply mapping_preserves_mo_arm in H.
      eexists...   
Qed. 

Lemma mapping_preserves_atomicity: forall (execArm:@Execution LabelArm LabelClassArm), 
    well_formed execArm -> atomicity_axiom execArm -> atomicity_axiom (map_exec_Arm_X86 execArm). 
Proof with eauto. 
    intros execArm Hwf Hatom. unfold atomicity_axiom in Hatom. unfold atomicity_axiom. 
    unfold not in Hatom. unfold not. intros HatomX86. apply Hatom. 
    destruct HatomX86 as [x [y [Hevx [Hevy [Hrmwxy Hfrmoxy]]]]]. 
    simpl in Hevx. simpl in Hevy. destruct Hevx as [x0 [Hx0ev Hx0x]].   
    destruct Hevy as [y0 [Hy0ev Hy0y]]. subst. exists x0, y0. split; 
    [|split; [| split]]; eauto. simpl in Hrmwxy. 
    destruct Hrmwxy as [x1 [y1 [Hrmwx [Hmapx Hmapy]]]]. unfold well_formed in Hwf.
    destruct Hwf as [Huid [Hpo [Hmo [Hrf Hrmw]]]].   
    - unfold well_formed_rmw in Hrmw. specialize (Hrmw x1 y1). apply Hrmw in Hrmwx as Hrmw'.
      destruct Hrmw' as [Hevx1 [Hevy1 _]]. 
      apply (map_event_Arm_X86_injective execArm) in Hmapx...   
      apply (map_event_Arm_X86_injective execArm) in Hmapy... subst... 
    - unfold HahnRelationsBasic.seq in Hfrmoxy. unfold HahnRelationsBasic.seq. 
      destruct Hfrmoxy as [z [Hfrz Hmoz]]. simpl in Hfrz, Hmoz. 
      destruct Hmoz as [x1 [y1 [Hmox1y1 [Hzmap Hy1map]]]]. unfold well_formed in Hwf.
      destruct Hwf as [Huid [Hpo [Hmo [Hrf Hrmw]]]]. unfold well_formed_mo in Hmo.  
      apply Hmo in Hmox1y1 as Hmo'. destruct Hmo' as [Hevx1 [Hevy1 _]]. 
      unfold well_formed_rf in Hrf. exists x1. subst. 
      split; apply (map_event_Arm_X86_injective execArm) in Hy1map; subst... 
      unfold fr. unfold fr in Hfrz. unfold seq. unfold seq in Hfrz. unfold transp. 
      unfold transp in Hfrz. destruct Hfrz as [z [Hrfx86 Hmox86]]. simpl in Hrfx86. 
      simpl in Hmox86. destruct Hrfx86 as [x2 [y2 [Hrfarm [Hzmap Hx0map]]]].
      apply Hrf in Hrfarm as Hrf'. destruct Hrf' as [Hevx2 [Hevy2 _]]. 
      destruct Hmox86 as [x3 [y3 [Hmoarm [Hzmap0 Hx1map]]]]. exists x2. subst.
      apply Hmo in Hmoarm as Hmo'. destruct Hmo' as [Hevx3 [Hevy3 _]].   
      apply (map_event_Arm_X86_injective execArm) in Hzmap0;     
      apply (map_event_Arm_X86_injective execArm) in Hx1map;
      apply (map_event_Arm_X86_injective execArm) in Hx0map; 
      subst... 
Qed. 

(*
(* Unset Printing Notations. *)
Lemma reads_arent_writes: forall (e: @Event LabelArm LabelClassArm), 
    is_r (event_label e) <-> ~(is_w (event_label e)).
Proof with eauto.
    intros. split; destruct e; destruct lab; simpl...
Qed.

Lemma mapping_preserves_ordered_before: forall (execArm:Execution) (e0 e1:Event), 
    well_formed execArm -> ob (execArm) e0 e1 -> hb_x86 (map_exec_Arm_X86 execArm) (map_event_Arm_X86 e0) (map_event_Arm_X86 e1).  
Proof with eauto. 
    intros. 
    unfold ob in H0.  
    unfold well_formed in H. 
    destruct H as [_ [_ H7]].  
    unfold hb_x86.
    induction H0.
    - left. destruct H as [[[[H0| H1]| H2] | H3] | H4]. 
        -- unfold aob in H0. destruct H0 as [H0 | H1].
           --- left. left. left. right. unfold well_formed_rmw in H7. 
               specialize (H7 x y). apply H7 in H0 as H8. destruct H8 as [H9 [H10 [H11 H12]]]. 
               unfold implid_x86. left. unfold seq. exists (map_event_Arm_X86 y). split. 
               ---- unfold poimm  in H11. destruct H11 as [H11 _]. rewrite mapping_preserves_po in H11...
               ---- right. unfold codom_rel. simpl. unfold eqv_rel. split... exists (map_event_Arm_X86 x), (x), (y)...  
           --- left. left. left. left. right. unfold implid_x86. right. unfold seq. exists (map_event_Arm_X86 x). split.
               ---- right. unfold seq in H1. destruct H1 as [z [H0 H1]]. destruct H1 as [z0 [H1 H2]]. unfold eqv_rel in H0. 
                    destruct H0 as [H0 H3]. subst. unfold eqv_rel. split... unfold codom_rel in *. destruct H3. 
                    exists (map_event_Arm_X86 x).  rewrite mapping_preserves_rmw in *... 
               ---- unfold seq in H1.  destruct H1 as [z [H0 H1]]. destruct H1 as [z0 [H1 H2]]. 
                    unfold lrs in *. unfold eqv_rel in H0. destruct H0 as [H0 H3]. subst. unfold R in H2. unfold eqv_rel in H2.
                    destruct H2 as [H2 H4]. subst. unfold minus_rel in H1. unfold seq in H1. destruct H1 as [x [H8 [H9 H10]]]. 
                    unfold W in H8. unfold eqv_rel in H8. destruct H8 as [H11 _]. subst. unfold poloc in H9.  destruct H9 as [_ H9].
                    rewrite mapping_preserves_po in H9...
        -- left. left. left. left.
           unfold bob_arm in H1. unfold seq in H1. destruct H1 as [[z [[Heq Hr] Hpo]] | [z [Hpo [Heq Hw]]]].
           --- rewrite <- Heq in Hpo. 
               unfold ppo_x86. unfold minus_rel. split.
               ---- rewrite <- mapping_preserves_po...
               ---- rewrite <- mapping_preserves_writes_arm.
                    unfold not. intros. destruct H as [Hw _]. 
                    rewrite reads_arent_writes in Hr. contradiction.
           --- rewrite Heq in Hpo. unfold ppo_x86. unfold minus_rel. split.
               ---- rewrite <- mapping_preserves_po...
               ---- rewrite <- mapping_preserves_writes_arm.
                    unfold not. intros. destruct H as [_ Hr]. rewrite <- Heq in Hr. 
                    apply mapping_preserves_reads_arm in Hr.
                    rewrite reads_arent_writes in Hr. contradiction.
        -- left. left. right. 
           unfold external in *. destruct H2. split. 
           --- apply mapping_preserves_rf...
           --- unfold map_event_Arm_X86. destruct x, y; simpl...
        -- right.
           unfold external in H3. destruct H3 as [H _].
           rewrite <- mapping_preserves_mo...
        -- left. right.
           unfold external in H4. destruct H4 as [H _].
           rewrite <- mapping_preserves_fr...
    - eapply t_trans...
Qed.
 *)

