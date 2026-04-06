From RelAcqProof Require Import Executions.
From RelAcqProof Require Import Events.
From RelAcqProof Require Import Arm.
From RelAcqProof Require Import X86.
From hahn Require Import Hahn.  

(* ********************************************************* Map from X86 to Arm ******************************************************** *)
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
         (~(dom_rel (rmw execX86) e_x86) /\ e_arm = EventInit uid (map_label_x86_arm lab))
      \/ ( (dom_rel (rmw execX86) e_x86) /\ e_arm = EventInit uid (map_label_x86_arm_rmw lab))
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

(* *********************************************************** Map from Arm to X86 ******************************************************** *)
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

(* ************************************************************ General Mapping Lemmas ************************************************************ *)

Lemma map_label_x86_arm_inverse:
    forall (lab : LabelX86),
    map_label_Arm_X86 (map_label_x86_arm lab) = lab.
Proof with eauto.
    intros lab. destruct lab; simpl...
Qed.

Lemma map_event_Arm_X86_preserves_same_thread:
    forall (e1 e2 : @Event LabelArm LabelClassArm),
    same_thread e1 e2 <-> same_thread (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).
Proof with eauto.
    split; intros H; destruct e1, e2; destruct lab,lab0; simpl in *...  
Qed.

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

Lemma mapping_preserves_reads_arm: forall  (e:@Event LabelArm LabelClassArm), 
    (is_r (event_label e)) 
    <-> 
    let eX86 := (map_event_Arm_X86 e) in 
        (is_r (event_label eX86)).
Proof with eauto. 
    split; intros. simpl. destruct e eqn:E; subst; destruct lab eqn:E0; subst; simpl... 
    destruct e eqn:E0; destruct lab eqn:E1; subst; simpl in H. all:try(simpl; eauto).
Qed. 

Lemma mapping_preserves_location_arm: forall (e:Event),
    lab_loc (event_label e) = lab_loc (event_label (map_event_Arm_X86 e)).
Proof.
    intros. simpl. destruct e, lab; simpl; reflexivity.
Qed. 

Lemma mapping_preserves_value_arm: forall (e:Event),
    lab_val (event_label e) = lab_val (event_label (map_event_Arm_X86 e)).
Proof.
    intros. simpl. destruct e, lab; simpl; reflexivity.
Qed.

Lemma mapping_preserves_both_write_arm:
    forall (e1 e2 : @Event LabelArm LabelClassArm),
    both_write (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) <-> both_write e1 e2.
Proof with eauto.
    intros e1 e2. unfold both_write.
    rewrite <- mapping_preserves_writes_arm.
    rewrite <- mapping_preserves_writes_arm.
    split; eauto.
Qed.

Lemma mapping_preserves_same_loc_arm:
    forall (e1 e2 : @Event LabelArm LabelClassArm),
    same_loc (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) <-> same_loc e1 e2.
Proof with eauto.
    intros e1 e2. unfold same_loc.
    rewrite <- mapping_preserves_location_arm.
    rewrite <- mapping_preserves_location_arm.
    split; eauto.
Qed.

Lemma mapping_preserves_same_val_arm:
    forall (e1 e2 : @Event LabelArm LabelClassArm),
    same_val (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) <-> same_val e1 e2.
Proof with eauto.
    intros e1 e2. unfold same_val.
    rewrite <- mapping_preserves_value_arm.
    rewrite <- mapping_preserves_value_arm.
    split; eauto.
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

Lemma mapping_preserves_rf: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    (rf execArm) e1 e2 -> (rf (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).  
Proof with eauto. 
    intros. simpl. exists e1, e2...  
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

(******************************************************************* Mapping Preserves Well-Formedness ****************************************************************)
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
    destruct Hwf_po as [Hpo_events [Hpo_connected Hpo_seq]].
    split; [| split]. 
    - intros e1 e2 Hpo. 
      simpl in Hpo.
      destruct Hpo as [x [y [Hpo [Heqx Heqy]]]]; subst.
      destruct (Hpo_events x y Hpo) as [Hevx Hevy].
      split.
      -- simpl. exists x. split... 
      -- simpl. exists y. split...
    - intros e.
      split.
      -- intros He.
        simpl in He.
        destruct He as [x [Hevx Heqx]]; subst.
        apply Hpo_connected in Hevx.
        destruct Hevx as [e0 [Hev0 Hpo]].
        exists (map_event_Arm_X86 e0).
        split.
        --- simpl. exists e0. split...
        --- destruct Hpo as [Hpo | Hpo].
          ---- left.  simpl. exists x, e0. split...
          ---- right. simpl. exists e0, x. split...
      -- intros [e' [He' Hpo]].
        simpl in He', Hpo.
        destruct He' as [x [Hevx Heqx]]; subst.
        destruct Hpo as [Hpo | Hpo].
        --- destruct Hpo as [x1 [y1 [Hpo [Heq1 Heq2]]]]; subst.
            destruct (Hpo_events x1 y1 Hpo) as [Hevx1 Hevy1].
            simpl. exists x1. split...
        --- destruct Hpo as [x1 [y1 [Hpo [Heq1 Heq2]]]]; subst.
            destruct (Hpo_events x1 y1 Hpo) as [Hevx1 Hevy1].
            simpl. exists y1. split...
    - intros e1 e2.
      split.
      -- intros Hpo.
         simpl in Hpo.
         destruct Hpo as [x [y [Hpo [Heqx Heqy]]]]; subst.
         apply Hpo_seq in Hpo.
         destruct x; destruct y; simpl in *...
      -- intros Hseq.
         destruct e1 as [uid1 lab1 | uid1 tid1 lab1];
         destruct e2 as [uid2 lab2 | uid2 tid2 lab2];
         simpl in Hseq; try contradiction. 
         --- simpl.
             exists (EventInit uid1 (map_label_x86_arm lab1)),
                 (EventThread uid2 tid2 (map_label_x86_arm lab2)).
             repeat split...
             apply Hpo_seq. simpl... simpl... rewrite map_label_x86_arm_inverse...    
             simpl... simpl... rewrite map_label_x86_arm_inverse... 
        --- destruct Hseq as [Htid Hlt]; subst.
            assert (Hpo : po execArm 
              (EventThread uid1 tid2 (map_label_x86_arm lab1))
              (EventThread uid2 tid2 (map_label_x86_arm lab2))).
            { apply Hpo_seq. simpl... }
            simpl.
            exists (EventThread uid1 tid2 (map_label_x86_arm lab1)),
                 (EventThread uid2 tid2 (map_label_x86_arm lab2)).
            split... simpl... simpl... rewrite map_label_x86_arm_inverse...
            split... simpl... simpl... rewrite map_label_x86_arm_inverse... 
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
    intros w r Hrf. simpl in Hrf.
    destruct Hrf as [x [y [Hrf [Heqx Heqy]]]]; subst.
    destruct (Hwf_rf x y Hrf) as [Hew [Her [Hiw [Hir [Hsl [Hsv Huniq']]]]]].
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    - simpl. exists x. split...
    - simpl. exists y. split...
    - apply mapping_preserves_writes_arm...
    - apply mapping_preserves_reads_arm...
    - apply mapping_preserves_same_loc_arm...
    - apply mapping_preserves_same_val_arm...
    - intros w0 Hw0 Hrf0.
      simpl in Hrf0.
      destruct Hrf0 as [x0 [y0 [Hrf0 [Heqx0 Heqy0]]]]; subst.
      destruct (Hwf_rf x0 y0 Hrf0) as [Hew0 [Her0 _]].
      apply (map_event_Arm_X86_injective execArm y y0 Huniq Her) in Heqy0...
      subst.
      assert (Hx0x : x0 = x).
      { apply Huniq'. apply mapping_preserves_writes_arm in Hw0... eauto.  }
      subst...
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
    - intros [e3 [Hpo1 Hpo2]]. apply Hnot. 
      simpl in Hpo1, Hpo2. 
      destruct Hpo1 as [x [y [Hpo1 [Heqx Heqy]]]]. 
      destruct Hpo2 as [x' [y' [Hpo2 [Heqx' Heqy']]]]. 
      subst. 
      assert (Heq : map_event_Arm_X86 y = map_event_Arm_X86 x') by congruence. 
      assert (Hevx  : events execArm x)  by (eapply po_in_events_l; eauto). 
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

(***************************************************************************** Mapping Preserves Coherency  *******************************************************************************)
Lemma inv_mapping_preserves_rf: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    well_formed execArm -> events execArm e1 -> events execArm e2 ->
    (rf (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) -> (rf execArm) e1 e2.
Proof with eauto. 
    intros execArm e1 e2 Hwf Hev1 Hev2 H. 
    destruct Hwf as [Huniq [_ [_ [Hwfrf _]]]].
    simpl in H.
    destruct H. destruct H as [y].
    destruct H as [Hpo [Heq1 Heq2]].
    specialize (Hwfrf x y).
    pose proof Hpo as Hevs.
    apply Hwfrf in Hevs.
    destruct Hevs as [Hevx [Hevy _]].
    apply (map_event_Arm_X86_injective execArm) in Heq1...
    apply (map_event_Arm_X86_injective execArm) in Heq2...
    subst...
Qed. 

Lemma inv_mapping_preserves_po: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    well_formed execArm -> events execArm e1 -> events execArm e2 ->
    (po (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) -> (po execArm) e1 e2.
Proof with eauto. 
    intros execArm e1 e2 Hwf Hev1 Hev2 H. 
    destruct Hwf as [Huniq [Hwfpo _]].
    simpl in H.
    destruct H. destruct H as [y].
    destruct H as [Hpo [Heq1 Heq2]].
    destruct Hwfpo as [Hwfpo _].
    specialize (Hwfpo x y).
    pose proof Hpo as Hevs.
    apply Hwfpo in Hevs.
    destruct Hevs as [Hevx Hevy].
    apply (map_event_Arm_X86_injective execArm) in Heq1...
    apply (map_event_Arm_X86_injective execArm) in Heq2...
    subst...
Qed. 

Lemma inv_mapping_preserves_loc: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    well_formed execArm -> events execArm e1 -> events execArm e2 ->
        same_loc (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) -> same_loc e1 e2.
Proof with eauto. 
    intros.
    unfold same_loc in *.
    repeat rewrite mapping_preserves_location_arm...
Qed.

Lemma inv_mapping_preserves_poloc: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    well_formed execArm -> events execArm e1 -> events execArm e2 ->
    (poloc (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) -> (poloc execArm) e1 e2.
Proof with eauto. 
    intros execArm e1 e2 Hwf Hev1 Hev2 H.
    unfold poloc in *. 
    destruct H as [Hloc Hpo].
    apply inv_mapping_preserves_po in Hpo...
    apply (inv_mapping_preserves_loc execArm) in Hloc...
Qed. 

Lemma inv_mapping_preserves_mo: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    well_formed execArm -> events execArm e1 -> events execArm e2 ->
    (mo (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) -> (mo execArm) e1 e2.
Proof with eauto. 
    intros execArm e1 e2 Hwf Hev1 Hev2 H. 
    destruct Hwf as [Huniq [_ [Hwfmo _]]].
    simpl in H.
    destruct H. destruct H as [y].
    destruct H as [Hpo [Heq1 Heq2]].
    specialize (Hwfmo x y).
    pose proof Hpo as Hevs.
    apply Hwfmo in Hevs.
    destruct Hevs as [Hevx [Hevy _]].
    apply (map_event_Arm_X86_injective execArm) in Heq1...
    apply (map_event_Arm_X86_injective execArm) in Heq2...
    subst...
Qed. 

Lemma inv_mapping_preserves_fr: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    well_formed execArm -> events execArm e1 -> events execArm e2 ->
    (fr (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) -> (fr execArm) e1 e2.
Proof with eauto. 
    intros execArm e1 e2 Hwf Hev1 Hev2 H. 
    pose proof Hwf as Hwfx86.
    apply (mapping_preserves_well_formedness) in Hwfx86.
    unfold fr in *.
    unfold seq in *.
    unfold transp in *.
    destruct H as [x [Hrf Hmo]].
    destruct Hwfx86 as [_ [_ [_ [Hwfrfx86 _]]]].
    pose proof Hwf as Hwf'.
    destruct Hwf' as [Huniq [_ [Hwfmo [Hwfrf _]]]].
    specialize (Hwfrfx86 x (map_event_Arm_X86 e1)).
    pose proof Hrf as Hrf'.
    apply Hwfrfx86 in Hrf'.
    destruct Hrf' as [Hxev _].
    destruct Hxev as [x_arm [Hevxarm Heqx]].
    exists x_arm.
    subst.
    split.
    - apply inv_mapping_preserves_rf...
    - apply inv_mapping_preserves_mo...
Qed.

Lemma mapping_preserves_coherence_chain: 
    forall (execArm:@Execution LabelArm LabelClassArm) (e1 e2: Event),
        let execX86 := map_exec_Arm_X86 execArm in
        well_formed execArm ->
            well_formed (map_exec_Arm_X86 execArm) ->
                events execArm e1 -> 
                    events execArm e2 ->
                        (poloc execX86 ∪ rf execX86 ∪ mo execX86 ∪ fr execX86)⁺ (map_event_Arm_X86 e1) (map_event_Arm_X86 e2) ->
                            (poloc execArm ∪ rf execArm ∪ mo execArm ∪ fr execArm)⁺ e1 e2. 
Proof with eauto. 
    intros execArm e1 e2 execX86 HwfArm HwfX86 Hev1 Hev2 Hcohx86.
    assert (Hgen : forall (a b : @Event LabelArm LabelClassArm),
        events execArm a -> events execArm b ->
        (poloc execX86 ∪ rf execX86 ∪ mo execX86 ∪ fr execX86)⁺ (map_event_Arm_X86 a) (map_event_Arm_X86 b) ->
            (poloc execArm ∪ rf execArm ∪ mo execArm ∪ fr execArm)⁺ a b). 
    2: { apply Hgen... } 
    intros a b Heva Hevb Hcohx86Prime.
    remember (map_event_Arm_X86 a) as x eqn:Heqx.
    remember (map_event_Arm_X86 b) as y eqn:Heqy.
    revert a b Heva Hevb Heqx Heqy.
    induction Hcohx86Prime as [x y Hbase | x z y Hhb1 IH1 Hhb2 IH2]. 
    - intros a b Heva Hevb Heqx Heqy. subst.
        destruct Hbase as [[[Hpoloc | Hrf] | Hmo] | Hfr].     
        -- left. repeat left. apply inv_mapping_preserves_poloc in Hpoloc... 
        -- left. left. left. right. apply inv_mapping_preserves_rf in Hrf... 
        -- left. left. right. apply inv_mapping_preserves_mo in Hmo... 
        -- left. right. apply inv_mapping_preserves_fr in Hfr...  
    - intros a b Heva Hevb Heqx Heqy. subst. 
      assert (Hevz : events (map_exec_Arm_X86 execArm) z). 
      { destruct (coherence_implies_events (map_exec_Arm_X86 execArm) (map_event_Arm_X86 a) z HwfX86 Hhb1) as [_ Hev]... }
      simpl in Hevz. destruct Hevz as [ez [Hevez Heqez]]. 
      unfold ob. eapply t_trans with ez. apply IH1... apply IH2...
Qed. 

Lemma mapping_preserves_coherence: forall (execArm: @Execution LabelArm LabelClassArm), 
    well_formed execArm -> coherence_axiom execArm -> coherence_axiom (map_exec_Arm_X86 execArm). 
Proof with eauto.
    intros execArm HwfArm Hco.
    pose proof HwfArm as HwfX86.
    apply mapping_preserves_well_formedness in HwfX86.
    unfold coherence_axiom in *.
    unfold acyclic in *.
    unfold irreflexive in *. 
    intros e_x86 H_x86. 
    pose proof H_x86 as H_x86'. 
    pose proof HwfX86 as HwfX86''. 
    apply coherence_implies_events in H_x86' as [Hevx86 _]...  
    simpl in Hevx86. 
    destruct Hevx86 as [e_arm [HevArm HeMap]].
    specialize Hco with e_arm.
    apply Hco. apply mapping_preserves_coherence_chain...  
    subst... 
Qed.

(*************************************************************************************** Mapping Preserves Atomicity *************************************************************************)
Lemma mapping_preserves_atomicity: forall (execArm:@Execution LabelArm LabelClassArm), 
    well_formed execArm -> atomicity_axiom execArm -> atomicity_axiom (map_exec_Arm_X86 execArm). 
Proof with eauto. 
    intros execArm Hwf Hatom. unfold atomicity_axiom in Hatom. unfold atomicity_axiom. 
    unfold not in Hatom. unfold not. intros HatomX86. apply Hatom. 
    destruct HatomX86 as [x [y [Hevx [Hevy [Hrmwxy Hfrmoxy]]]]]. 
    simpl in Hevx. simpl in Hevy. destruct Hevx as [x0 [Hx0ev Hx0x]].  
    pose proof Hwf as Hwf'. destruct Hwf' as [Huid [Hpo [Hmo [Hrf Hrmw]]]].   
    destruct Hevy as [y0 [Hy0ev Hy0y]]. subst. exists x0, y0. split; 
    [|split; [| split]]; eauto. simpl in Hrmwxy. 
    destruct Hrmwxy as [x1 [y1 [Hrmwx [Hmapx Hmapy]]]]. unfold well_formed in Hwf. 
    - specialize (Hrmw x1 y1). apply Hrmw in Hrmwx as Hrmw'. destruct Hrmw' as [Hevx1 [Hevy1 _]]. 
      apply (map_event_Arm_X86_injective execArm) in Hmapx, Hmapy... subst...  
    - unfold seq in Hfrmoxy. unfold seq. 
      destruct Hfrmoxy as [z [Hfrz Hmoz]]. simpl in Hfrz, Hmoz. 
      destruct Hmoz as [x1 [y1 [Hmox1y1 [Hzmap Hy1map]]]].
      pose proof (well_formed_mo_events _ _ Hwf Hmox1y1) as [Hevx1 Hevy1]. 
      exists x1. subst. split; apply (map_event_Arm_X86_injective execArm) in Hy1map; subst... 
      unfold fr in *. unfold seq in *. unfold transp in *. 
      destruct Hfrz as [z [Hrfx86 Hmox86]]. simpl in Hrfx86, Hmox86.
      destruct Hrfx86  as [x2 [y2 [Hrfx2y2 [Hx2map Hy2map]]]].  
      pose proof (well_formed_rf_events _ _ Hwf Hrfx2y2) as [Hevx2 Hevy2]. 
      destruct Hmox86 as [x3 [y3 [Hmoarm [Hzmap0 Hx1map]]]]. exists x2. subst. 
      pose proof (well_formed_mo_events _ _ Hwf Hmoarm) as [Hevx3 Hevy3].  
      apply (map_event_Arm_X86_injective execArm) in Hzmap0, Hx1map, Hy2map; subst...    
Qed. 

(*************************************************************************************** Mapping Preserves Ordered Before *************************************************************************)
(* Fr internal against the direction of the po violates Coherency. *)
Lemma fri_x86_against_po_false: forall (execArm: Execution) (e0 e1: Event),
    arm_consistent execArm 
        -> (internal fr (map_exec_Arm_X86 execArm)) e0 e1
            -> po (map_exec_Arm_X86 execArm) e1 e0 
                -> False.  
Proof with eauto. 
    intros. unfold internal in *. destruct H0 as [Hfr HsameThread]. 
    simpl in H1. destruct H1 as [x0 [y0 [HpoArm [He1map He0map]]]]. 
    unfold fr in Hfr. unfold seq in *. unfold transp in *. 
    destruct Hfr as [z [HrfX86 HmoX86]]. simpl in HrfX86. 
    simpl in HmoX86. destruct HmoX86 as [x1 [y1 [Hmo [Hx1map Hy1map]]]].
    destruct HrfX86 as [x2 [y2 [Hrf [Hx2map Hy2map]]]]. destruct H as [HwfArm [_ [HatomArm [HcohArm _]]]].
    pose proof HwfArm as Hwf'. destruct Hwf' as [Huid _]. subst. 
    pose proof (well_formed_po_events _ _ HwfArm HpoArm) as [Hevx0 Hevy0]. 
    pose proof (well_formed_mo_events _ _ HwfArm Hmo) as [Hevx1 Hevy1]. 
    pose proof (well_formed_mo_same_loc _ _ HwfArm Hmo) as Hsmelocmo. 
    pose proof (well_formed_rf_events _ _ HwfArm Hrf) as [Hevx2 Hevy2]. 
    pose proof (well_formed_rf_same_loc _ _ HwfArm Hrf) as Hsmelocrf. subst. 
    apply (map_event_Arm_X86_injective execArm) in Hx1map, He1map, He0map... 
    subst. unfold coherence_axiom in *. unfold acyclic in *. unfold irreflexive in *.
    apply same_loc_sym in Hsmelocrf. apply (same_loc_trans Hsmelocrf) in Hsmelocmo.  
    assert (Hsmelocx0y0: same_loc x0 y0). { apply same_loc_sym. eauto. }
    assert (Hpoloc: poloc execArm x0 y0). {unfold poloc. split... }
    assert (Hrfinv: (rf execArm)⁻¹  y0 x1). { unfold transp... } 
    assert (Hfr: (fr execArm) y0 x0). { unfold fr. unfold seq. exists x1. split... }
    apply (HcohArm x0). eapply t_trans. apply t_step. repeat left... apply t_step. right... 
Qed. 

(* Mo internal against the direction of po violates Coherency. *)
Lemma moi_x86_against_po_false: forall (execArm:Execution) (e0 e1:Event),
    arm_consistent execArm 
        -> (internal mo (map_exec_Arm_X86 execArm)) e0 e1
            -> po (map_exec_Arm_X86 execArm) e1 e0 
                -> False.  
Proof with eauto. 
    intros. unfold internal in *. destruct H0 as [Hmo HsameThread]. 
    simpl in H1. destruct H1 as [x0 [y0 [HpoArm [He1map He0map]]]]. 
    simpl in Hmo. destruct Hmo as [x1 [y1 [Hmo [Hx1map Hy1map]]]].
    unfold arm_consistent in *. 
    destruct H as [HwfArm [_ [HatomArm [HcohArm _]]]]. pose proof HwfArm as Hwf'. 
    destruct Hwf' as [Huid _]. 
    pose proof (well_formed_po_events _ _ HwfArm HpoArm) as [Hevx0 Hevy0]. 
    pose proof (well_formed_mo_events _ _ HwfArm Hmo) as [Hevx1 Hevy1]. 
    pose proof (well_formed_mo_same_loc _ _ HwfArm Hmo) as Hsmelocmo.  subst.   
    apply (map_event_Arm_X86_injective execArm) in He1map, He0map...
    subst. unfold coherence_axiom in *. unfold acyclic in *. unfold irreflexive in *. 
    assert (Hsmelocx0y0: same_loc x0 y0). { apply same_loc_sym... }
    assert (Hpoloc: poloc execArm x0 y0). { unfold poloc. split... }
    apply (HcohArm x0). eapply t_trans. apply t_step. repeat left... apply t_step. left. right...
Qed. 


Lemma ppo_x86_maps_to_bob_arm : 
    forall (execArm : @Execution LabelArm LabelClassArm)
           (e0 e1 : @Event LabelArm LabelClassArm),
        arm_consistent execArm -> 
            well_formed (map_exec_Arm_X86 execArm) ->
                (events execArm) e0 ->
                    (events execArm) e1 -> 
                        ppo_x86 (map_exec_Arm_X86 execArm) 
                            (map_event_Arm_X86 e0) (map_event_Arm_X86 e1) ->
                                    bob_arm execArm e0 e1.
Proof with eauto.  
   intros execArm e0 e1 HarmCons HwfX86 Heve0 Heve1 Hppo.
   destruct HarmCons as [Hwf _].
   pose proof Hwf as Hwf'. destruct Hwf' as [Huid _].   
   unfold ppo_x86 in *. unfold minus_rel in *. 
   destruct Hppo as [Hpo Hnot]. simpl in Hpo. 
   destruct Hpo as  [x0 [y0 [Hpo [Hx0map Hy0map]]]].
   apply not_w_r_implies_other_cases_x86 in Hnot. 
   unfold bob_arm.
   pose proof (well_formed_po_events _ _ Hwf Hpo) as [Hevx0 Hevy0].
   apply (map_event_Arm_X86_injective execArm) in Hx0map, Hy0map...
   repeat rewrite <- mapping_preserves_writes_arm in Hnot. 
   repeat rewrite <- mapping_preserves_reads_arm in Hnot. 
   subst. destruct Hnot as [[_ Hww] | [[Hrr _] | [Hr _]]]. 
   left. left. right. unfold seq. exists y0; repeat split...
   all:try(repeat left; unfold seq; exists x0; repeat split; eauto).
Qed.

Lemma implid_x86_maps_to_bob_arm : 
    forall (execArm : @Execution LabelArm LabelClassArm)
           (e0 e1 : @Event LabelArm LabelClassArm),
        arm_consistent execArm -> 
            well_formed (map_exec_Arm_X86 execArm) ->
                (events execArm) e0 ->
                    (events execArm) e1 -> 
                        implid_x86 (map_exec_Arm_X86 execArm) 
                            (map_event_Arm_X86 e0) (map_event_Arm_X86 e1) ->
                                    bob_arm execArm e0 e1.
Proof with eauto.  
   intros execArm e0 e1 HarmCons HwfX86 Heve0 Heve1 Himp. 
   destruct HarmCons as [Hwf [Hamo _]]. 
   pose proof Hwf as Hwf'.
   destruct Hwf' as [Huid _].   
   unfold implid_x86, bob_arm in *.  
   destruct Himp as [[z [Hpo Hrmw]] | [z [Hrmw Hpo]]];
   unfold seq, eqv_rel, dom_rel, codom_rel in *; 
   simpl in Hpo, Hrmw;  
   destruct Hrmw as [[Hzmap [w [x0 [y0 [Hrmw [Hmapx0 Hmapy0]]]]] ] | [Hzmap [w [x0 [y0 [Hrmw [Hmapx0 Hmapy0]]]]]]];  
   destruct Hpo as [x [y [Hpo [Hmape0 Hmapz]]]]; 
   pose proof (well_formed_po_events _ _ Hwf Hpo) as [Hevx Hevy]; 
   pose proof (well_formed_rmw_events _ _ Hwf Hrmw) as [Hevx0 Hevy0];
   pose proof (well_formed_rmw_po _ _ Hwf Hrmw) as HpoRmw; subst. 
    (* po;rmw => po;amo *)
    --  apply (map_event_Arm_X86_injective execArm) in Hzmap, Hmape0, Hmapx0... 
        subst. left. right. exists x0. repeat split... 
        exists y0. apply arm_consistent_amo_is_rmw...
    (* po;[codom(rmw)] => po;W *) 
    --  apply well_formed_codom_rmw_write in Hrmw...   
        apply (map_event_Arm_X86_injective execArm) in Hzmap, Hmape0, Hmapy0...
        subst. left. left. right. exists y0.  repeat split...
    (* [dom(rmw)];po => R;po *)
    --  apply (map_event_Arm_X86_injective execArm) in Hmapz, Hmape0, Hmapx0... 
        apply well_formed_dom_rmw_read in Hrmw...  
        subst. left. left. left. exists x. repeat split...
    (* rmw;po => amo;po*) 
    --  apply (map_event_Arm_X86_injective execArm) in Hmapz, Hmape0, Hmapy0... 
        subst. right. exists x.  repeat split... 
        exists x0.  apply arm_consistent_amo_is_rmw... 
Qed.

Lemma rfe_x86_maps_to_rfe_arm : 
    forall (execArm : @Execution LabelArm LabelClassArm)
           (e0 e1 : @Event LabelArm LabelClassArm),
        arm_consistent execArm -> 
            well_formed (map_exec_Arm_X86 execArm) ->
                (events execArm) e0 ->
                    (events execArm) e1 -> 
                       external rf (map_exec_Arm_X86 execArm) 
                            (map_event_Arm_X86 e0) (map_event_Arm_X86 e1) ->
                                   external rf execArm e0 e1. 
Proof with eauto.  
    intros execArm e0 e1 [Hwf _] HwfX86 Heve0 Heve1 [HrfX86 Hnotst].
    rewrite <- map_event_Arm_X86_preserves_same_thread in Hnotst. 
    simpl in HrfX86. destruct HrfX86 as [x [y [Hrf [Hmape0x Hmape1y]]]].
    pose proof Hrf as Hrf'. pose proof Hwf as Hwf'. destruct Hwf' as [Huid _]. 
    apply well_formed_rf_events in Hrf' as [Hevx Hevy]... 
    apply (map_event_Arm_X86_injective execArm) in Hmape0x, Hmape1y... 
    subst. split...   
Qed.

Lemma moe_x86_maps_to_moe_arm : 
    forall (execArm : @Execution LabelArm LabelClassArm)
           (e0 e1 : @Event LabelArm LabelClassArm),
        arm_consistent execArm -> 
            well_formed (map_exec_Arm_X86 execArm) ->
                (events execArm) e0 ->
                    (events execArm) e1 -> 
                       external mo (map_exec_Arm_X86 execArm) 
                            (map_event_Arm_X86 e0) (map_event_Arm_X86 e1) ->
                                   external mo execArm e0 e1. 
Proof with eauto.  
    intros execArm e0 e1 [Hwf _] HwfX86 Heve0 Heve1 [HmoX86 Hnotst].
    rewrite <- map_event_Arm_X86_preserves_same_thread in Hnotst.  
    simpl in HmoX86. destruct HmoX86 as [x [y [Hmo [Hmape0x Hmape1y]]]].
    pose proof Hmo as Hmo'. pose proof Hwf as Hwf'. destruct Hwf' as [Huid _]. 
    apply well_formed_mo_events in Hmo' as [Hevx Hevy]... 
    apply (map_event_Arm_X86_injective execArm) in Hmape0x, Hmape1y... 
    subst. split...   
Qed.

Lemma fre_x86_maps_to_fre_arm : 
    forall (execArm : @Execution LabelArm LabelClassArm)
           (e0 e1 : @Event LabelArm LabelClassArm),
        arm_consistent execArm -> 
            well_formed (map_exec_Arm_X86 execArm) ->
                (events execArm) e0 ->
                    (events execArm) e1 -> 
                       external fr (map_exec_Arm_X86 execArm) 
                            (map_event_Arm_X86 e0) (map_event_Arm_X86 e1) ->
                                   external fr execArm e0 e1. 
Proof with eauto.  
    intros execArm e0 e1 [Hwf _] HwfX86 Heve0 Heve1 [[w [HrfX86 HmoX86]] Hnotst].
    unfold transp in *. 
    rewrite <- map_event_Arm_X86_preserves_same_thread in Hnotst.  
    simpl in HrfX86. destruct HrfX86 as [x [y [Hrf [Hmape0x Hmape1y]]]].
    simpl in HmoX86. destruct HmoX86 as [x1 [y1 [Hmo [Hmape0x1 Hmape1y1]]]]. 
    pose proof Hrf as Hrf'. pose proof Hmo as Hmo'.  
    pose proof Hwf as Hwf'. destruct Hwf' as [Huid _]. 
    subst. apply well_formed_rf_events in Hrf' as [Hevx Hevy]...
    apply well_formed_mo_events in Hmo' as [Hevx1 Hevy1]...
    apply (map_event_Arm_X86_injective execArm) in Hmape0x1, Hmape1y1, Hmape1y...  
    subst... split... unfold fr, seq, transp. exists x1. split...     
Qed.

Lemma fri_x86_maps_to_bob_arm : 
    forall (execArm : @Execution LabelArm LabelClassArm) 
           (e0 e1 : @Event LabelArm LabelClassArm),
        arm_consistent execArm -> 
            well_formed (map_exec_Arm_X86 execArm) ->
                (events execArm) e0 ->
                    (events execArm) e1 -> 
                       internal fr (map_exec_Arm_X86 execArm) 
                            (map_event_Arm_X86 e0) (map_event_Arm_X86 e1) ->
                                   bob_arm execArm e0 e1. 
Proof with eauto.  
    intros execArm e0 e1 HarmCons HwfX86 Heve0 Heve1 [HfrX86 Hst].
    pose proof HarmCons as HarmCons'. destruct HarmCons' as [Hwf _ ].

    (* We're required to consider two possibilities for the direction of the fr edge. 
       In the same direction as and in the opposite direction of the po edge. *) 
    assert (Hpodis: po (map_exec_Arm_X86 execArm) (map_event_Arm_X86 e0) (map_event_Arm_X86 e1) 
                \/  po (map_exec_Arm_X86 execArm) (map_event_Arm_X86 e1) (map_event_Arm_X86 e0)). 
    { apply fr_same_thread_implies_po in HfrX86...  } 
    pose proof HfrX86 as HfrX86'. destruct HfrX86 as [w [HrfX86 HmoX86]]. 
    pose proof Hwf as Hwf'. destruct Hwf' as [Huid _]. unfold transp in *. simpl in Hpodis, HrfX86, HmoX86. 
    destruct HrfX86 as [x0 [y0 [Hrf [Hmapwx0 Hmape0y0]]]]. 
    destruct HmoX86 as [x1 [y1 [Hmo [Hmapwx1 Hmape1y1]]]].
    pose proof Hmo as Hmo'. 
    apply well_formed_mo_events in Hmo' as [Hevx1 Hevy1]...
    apply well_formed_rf_events in Hrf as [Hevx0 Hevy0]...  subst. 
    apply (map_event_Arm_X86_injective execArm) in Hmapwx1, Hmape1y1, Hmape0y0...   
    destruct Hpodis as [[x2 [y2 [Hpo [Hmape0x2 Hmape1y2]]]] | Hcontra]. 

    (* fr in the direction of po maps to po;W ... *)
    - pose proof Hpo as Hpo'.
      apply well_formed_mo_write_r in Hmo...   
      apply well_formed_po_events in Hpo' as [Hevx2 Hevy2]... subst. 
      apply (map_event_Arm_X86_injective execArm) in Hmape0x2, Hmape1y2... subst. 
      left. left. right. unfold seq. exists y2. split... unfold W. unfold eqv_rel. 
      split...
    
    (* fr in the opposite direction of po violates Coherence and hence contradicts the Arm Consistency axiom. *)
    - apply fri_x86_against_po_false in Hcontra... exfalso... unfold internal. split... 
Qed. 

Lemma moi_x86_maps_to_bob_arm : 
    forall (execArm : @Execution LabelArm LabelClassArm)
           (e0 e1 : @Event LabelArm LabelClassArm),
        arm_consistent execArm -> 
            well_formed (map_exec_Arm_X86 execArm) ->
                (events execArm) e0 ->
                    (events execArm) e1 -> 
                       internal mo (map_exec_Arm_X86 execArm) 
                            (map_event_Arm_X86 e0) (map_event_Arm_X86 e1) ->
                                   bob_arm execArm e0 e1. 
Proof with eauto.  
    intros execArm e0 e1 HarmCons HwfX86 Heve0 Heve1 [HmoX86 Hst]. 
    pose proof HarmCons as HarmCons'. destruct HarmCons' as [Hwf _ ].

    (* We're required to consider two possibilities for the direction of the mo edge. 
       In the same direction as and in the opposite direction of the po edge. *) 
    assert (Hpodis: po (map_exec_Arm_X86 execArm) (map_event_Arm_X86 e0) (map_event_Arm_X86 e1) 
                \/  po (map_exec_Arm_X86 execArm) (map_event_Arm_X86 e1) (map_event_Arm_X86 e0)). 
    { apply mo_same_thread_implies_po in HmoX86...  } 
    pose proof HmoX86 as HmoX86'. pose proof Hwf as Hwf'. 
    destruct Hwf' as [Huid _]. unfold transp in *. simpl in Hpodis, HmoX86. 
    destruct HmoX86 as [x1 [y1 [Hmo [Hmapwx1 Hmape1y1]]]].
    pose proof Hmo as Hmo'. 
    apply well_formed_mo_events in Hmo' as [Hevx1 Hevy1]... subst. 
    apply (map_event_Arm_X86_injective execArm) in Hmapwx1, Hmape1y1...  subst.  
    destruct Hpodis as [[x2 [y2 [Hpo [Hmape0x2 Hmape1y2]]]] | Hcontra].
    (* mo in the direction of po maps to po;W ... *)
    - pose proof Hpo as Hpo'. apply well_formed_mo_write_r in Hmo...   
      apply well_formed_po_events in Hpo' as [Hevx2 Hevy2]... subst. 
      apply (map_event_Arm_X86_injective execArm) in Hmape0x2, Hmape1y2... subst. 
      left. left. right. unfold seq. exists y2. split... unfold W. unfold eqv_rel. 
      split...
    (* mo in the opposite direction of po violates Coherence and hence contradicts the Arm Consistency axiom. *) 
    - apply moi_x86_against_po_false in Hcontra... exfalso... unfold internal. split... 
Qed. 

Lemma hb_x86_mapped_implies_ob_arm :
    forall (execArm : @Execution LabelArm LabelClassArm)
           (e0 e1 : @Event LabelArm LabelClassArm),
        arm_consistent execArm -> 
            well_formed (map_exec_Arm_X86 execArm) ->
                (events execArm) e0 ->
                    (events execArm) e1 -> 
                        hb_x86 (map_exec_Arm_X86 execArm) 
                            (map_event_Arm_X86 e0) (map_event_Arm_X86 e1) ->
                                    ob execArm e0 e1. 
Proof with eauto. 
    intros execArm e0 e1 Harmcons HwfX86 Hev0 Hev1 HhbX86.
    (* This assertion and subsequent remember and revert, is here because 
       Rocq seems to lose context when performing induction directly on HhbX86... *)
    assert (Hgen : forall (a b : @Event LabelArm LabelClassArm),
        events execArm a -> events execArm b ->
            hb_x86 (map_exec_Arm_X86 execArm) (map_event_Arm_X86 a) (map_event_Arm_X86 b) 
                -> ob execArm a b). 
    2: { apply Hgen... } 
    intros a b Heva Hevb Hhb.
    unfold hb_x86 in Hhb.
    remember (map_event_Arm_X86 a) as x eqn:Heqx.
    remember (map_event_Arm_X86 b) as y eqn:Heqy.
    revert a b Heva Hevb Heqx Heqy.
    
    (* Begin induction... *)
    induction Hhb as [x y Hbase | x z y Hhb1 IH1 Hhb2 IH2].
    (* Base Cases *) 
    - intros a b Heva Hevb Heqx Heqy.
      destruct Hbase as [[[[Hppo|Himp]|Herf]|Hfr]|Hmo].
      (* Case for ppox86 *) 
      -- subst. left. left. left. left. right. apply ppo_x86_maps_to_bob_arm...       
      (* Case for implidx86 *)
      -- subst. left. left. left. left. right. apply implid_x86_maps_to_bob_arm... 
      (* Case for rfe *)
      -- subst. left. left. left. right. apply rfe_x86_maps_to_rfe_arm...  
      (* Case for fr *)
      -- destruct (same_thread_dec_x86 x y).
         (* There are two cases, fri and fre. The case for fre is trivial as it maps directly to fre in arm.
            The case for fri is more complex (see lemma fri_x86_maps_to_bob_arm). The following case for 
            mo is similar. *) 
         --- subst. left. left. left. left. right. apply fri_x86_maps_to_bob_arm... split...  
         --- subst. left. right. apply fre_x86_maps_to_fre_arm... split...        
      (* Case for mo *)
      -- destruct (same_thread_dec_x86 x y). 
         --- subst. left. left. left. left. right. apply moi_x86_maps_to_bob_arm... split...  
         --- subst. left. left. right. apply moe_x86_maps_to_moe_arm... split...  
         
    (* Inductive Case ... *)
    - intros a b Heva Hevb Heqx Heqy. subst.  
      assert (Hevz : events (map_exec_Arm_X86 execArm) z). 
      { destruct (hb_x86_in_events (map_exec_Arm_X86 execArm) (map_event_Arm_X86 a) z HwfX86) as [_ Hev]... }
      simpl in Hevz. destruct Hevz as [ez [Hevez Heqez]]. 
      unfold ob. eapply t_trans with ez. apply IH1... apply IH2...
Qed. 

Lemma mapping_preserves_ordered_before: forall (execArm:@Execution LabelArm LabelClassArm), 
    arm_consistent execArm -> ordered_before_axiom_arm execArm -> ordered_before_axiom_x86 (map_exec_Arm_X86 execArm). 
Proof with eauto.  
    intros execArm HarmCons HobAxArm.
    pose proof HarmCons as HarmConsCopy.
    destruct HarmConsCopy as [HwfArm _].
    (* Ordered Before X86 is defined as irreflexsive hb, 
       irreflexsivity: (reflexsive ...) -> False. 
       intros in this case unfolds the definition and 
       introduces the reflexivity hypothesis and makes
       False the goal. *)
    intros x HhbX86.
    (* We will prove False by first proving that every hbX86 chain 
       corresponds to a bob_arm chain. Since we have a hypothesis that states   
       (reflexsive bob_arm ...) -> False, and a hypothesis stating 
       (reflexsive hb_x86 ...), we can use said lemma to derive False 
       as is required. *)

    (* The lemma proving that every hbX86 chain corresponds to a bob_arm chain. 
       relies on well_formedness. *) 
    assert (HwfX86: well_formed (map_exec_Arm_X86 execArm)).  
    { apply (mapping_preserves_well_formedness execArm HwfArm). } 

    (* The lemma proving that every hbX86 chain corresponds to a bob_arm chain. 
       relies on the assumption that both ends of the chain reside in the 
       execution.*)
    assert (Hevx : events (map_exec_Arm_X86 execArm) x). 
    { destruct (hb_x86_in_events (map_exec_Arm_X86 execArm) x x HwfX86) as [_ Hev]... } 
    
    (* By definition of our mapping, "events (map_exec_Arm_X86 execArm) x -> exists e, events execArm e" *)
    simpl in Hevx. destruct Hevx as [e [Heve Hmapx]].
    (* We specialise the "reflexsive bob_arm" lemma with "e" and use the 
       hbx86 -> bob_arm lemma to conclude False *)
    apply (HobAxArm e). subst. apply hb_x86_mapped_implies_ob_arm...    
Qed.

(*************************************************************************************** Mapping Preserves Behaviour *****************************************************************************)
Lemma mapping_preserves_behaviour: forall (execArm:@Execution LabelArm LabelClassArm) (l:Location) (v:Value), 
    well_formed execArm -> (behaviour (execArm) (l, v) <-> behaviour (map_exec_Arm_X86 execArm) (l, v)).  
Proof with eauto.
    (* Our proof follows from the argument that mo edges are preserved by the mapping scheme and 
       hence behaviour is preserved. *)
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

(*************************************************************************************** Semantic Preservation *****************************************************************************)
Theorem semantic_preservation_x86_arm_release_acquire: 
    forall (execArm: @Execution LabelArm LabelClassArm), 
        arm_consistent execArm -> 
            exists execX86, (x86_consistent execX86) 
            /\ (forall (l:Location) (v:Value), behaviour (execArm) (l, v) <-> behaviour (execX86) (l, v)). 
Proof with eauto. 
    intros execArm HarmCons. exists (map_exec_Arm_X86 execArm). 
    assert (HarmConsCopy: arm_consistent execArm). { eauto. } 
    unfold arm_consistent in *.  destruct HarmCons as [Hwf [Hamo [Hatom [Hcoh Hob]]]].
    split.
    - unfold x86_consistent. split; [| split;[| split] ]. 
      apply mapping_preserves_well_formedness...
      apply mapping_preserves_atomicity... 
      apply mapping_preserves_coherence...  
      apply mapping_preserves_ordered_before... 
    - intros. apply mapping_preserves_behaviour...  
Qed. 