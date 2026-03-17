From RelAcqProof Require Import Executions.
From RelAcqProof Require Import Events.   
From RelAcqProof Require Import Label. 
From RelAcqProof Require Import LabelArm.
From RelAcqProof Require Import LabelX86. 
From Coq Require Import Logic.FunctionalExtensionality. 
From Coq Require Import Logic.PropExtensionality. 

(* *************************** Map from X86 to Arm ************************* *)
Definition map_label_X86_Arm (lab_X86: LabelX86): LabelArm := 
match lab_X86 with
| W_x86 loc val => W_Rel loc val 
| R_x86 loc val => R_Acq_Pc loc val 
end. 

Definition map_event_X86_Arm (event_X86:@Event LabelX86 LabelClassX86):@Event LabelArm LabelClassArm := 
match  event_X86 with 
| EventInit uid lab => EventInit uid (map_label_X86_Arm lab)
| EventThread uid tid lab => EventThread uid tid (map_label_X86_Arm lab)
end. 

Definition map_exec_X86_Arm (execX86:@Execution LabelX86 LabelClassX86):@Execution LabelArm LabelClassArm := {|
    events := fun e => exists e', events execX86 e' /\ e = map_event_X86_Arm e';
    po     := fun e1 e2 => exists x y, po execX86 x y /\ e1 = map_event_X86_Arm x /\ e2 = map_event_X86_Arm y;
    rf     := fun e1 e2 => exists x y, rf execX86 x y /\ e1 = map_event_X86_Arm x /\ e2 = map_event_X86_Arm y;
    mo     := fun e1 e2 => exists x y, mo execX86 x y /\ e1 = map_event_X86_Arm x /\ e2 = map_event_X86_Arm y; 
    rmw    := fun e1 e2 => exists x y, rmw execX86 x y /\ e1 = map_event_X86_Arm x /\ e2 = map_event_X86_Arm y;  
|}. 

(* ************************** Map from Arm to X86 *************************** *)
Definition map_label_Arm_X86 (lab_Arm: LabelArm): LabelX86 := 
match lab_Arm with
| W_Rel loc val => W_x86 loc val  
| R_Acq_Pc loc val => R_x86 loc val   
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


Lemma mapping_preserves_writes_x86: forall (e:@Event LabelX86 LabelClassX86), 
    (is_w (event_label e)) 
    <-> 
    let eArm := (map_event_X86_Arm e) in 
        (is_w (event_label eArm)).
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
    intros.
    split. 
    - intros.  
      -- simpl. destruct e eqn:E; subst; destruct lab eqn:E0; subst; simpl... 
    - intros.  
      -- destruct e eqn:E0; destruct lab eqn:E1; subst; simpl in H. all:try(simpl; eauto).
Qed. 


Lemma mapping_preserves_reads_x86: forall (e:@Event LabelX86 LabelClassX86), 
    (is_r (event_label e)) 
    <-> 
    let eArm := (map_event_X86_Arm e) in 
        (is_r (event_label eArm)).
Proof with eauto. 
    intros.
    split. 
    - intros.  
      -- simpl. destruct e eqn:E; subst; destruct lab eqn:E0; subst; simpl... 
    - intros.  
      -- destruct e eqn:E0; destruct lab eqn:E1; subst; simpl in H. all:try(simpl; eauto).
Qed.

Lemma mapping_preserves_location_arm: forall (e:Event),
    lab_loc (event_label e) = lab_loc (event_label (map_event_Arm_X86 e)).
Proof.
    intros.
    simpl.
    destruct e; destruct lab; simpl; reflexivity.
Qed. 

Lemma mapping_preserves_location_x86: forall (e:Event),
    lab_loc (event_label e) = lab_loc (event_label (map_event_X86_Arm e)).
Proof.
    intros.
    simpl.
    destruct e; destruct lab; simpl; reflexivity.
Qed. 

Lemma mapping_preserves_value_arm: forall (e:Event),
    lab_val (event_label e) = lab_val (event_label (map_event_Arm_X86 e)).
Proof.
    intros.
    simpl.
    destruct e; destruct lab; simpl; reflexivity.
Qed.


Lemma mapping_preserves_value_x86: forall (e:Event),
    lab_val (event_label e) = lab_val (event_label (map_event_X86_Arm e)).
Proof.
    intros.
    simpl.
    destruct e; destruct lab; simpl; reflexivity.
Qed. 

Lemma mapping_preserves_both_write: forall (e1 e2:Event), 
    both_write (map_event_X86_Arm e1) (map_event_X86_Arm e2) <-> both_write e1 e2.
Proof with eauto. 
    intros. unfold both_write. repeat rewrite mapping_preserves_writes_x86. simpl. split. 
    - eauto. 
    - eauto. 
Qed.

Lemma mapping_preserves_same_loc_x86: forall (e1 e2:Event), 
    same_loc (map_event_X86_Arm e1) (map_event_X86_Arm e2) <-> same_loc e1 e2. 
Proof with eauto. 
    intros. unfold same_loc. repeat rewrite mapping_preserves_location_x86. split. 
    all:(eauto). 
Qed.

Lemma mapping_preserves_same_val_x86: forall (e1 e2:Event), 
    same_val (map_event_X86_Arm e1) (map_event_X86_Arm e2) <-> same_val e1 e2. 
Proof with eauto. 
    intros. unfold same_val. repeat  rewrite mapping_preserves_value_x86. split. 
    all:(eauto).  
Qed. 

Lemma map_label_Arm_X86_injective:
  forall l l0,
  map_label_Arm_X86 l = map_label_Arm_X86 l0 ->
  l = l0.
Proof with eauto. 
    intros. 
    destruct l, l0; simpl in H. 
    all:try(inversion H; injection H; intros; subst; reflexivity). 
Qed.

Lemma map_label_X86_Arm_injective:
  forall l l0,
  map_label_X86_Arm l = map_label_X86_Arm l0 ->
  l = l0.
Proof with eauto. 
    intros. 
    destruct l, l0; simpl in H. 
    all:try(inversion H; injection H; intros; subst; reflexivity). 
Qed.

Lemma map_event_Arm_X86_injective :
  forall e e0,
  map_event_Arm_X86 e = map_event_Arm_X86 e0 <->
  e = e0. 
Proof. 
    intros. split; intros.  
    simpl in H. unfold map_event_Arm_X86 in H. destruct e, e0.
    all:try(inversion H).   
    all:try(injection H; intros; subst; apply map_label_Arm_X86_injective in H0; rewrite H0; eauto). 
    eauto.    
Qed.

Lemma map_event_X86_Arm_injective :
  forall e e0,
  map_event_X86_Arm e = map_event_X86_Arm e0 <->
  e = e0. 
Proof. 
    intros. split; intros. 
    simpl in H. unfold map_event_X86_Arm in H. destruct e, e0.
    all:try(inversion H).   
    all:try(injection H; intros; subst; apply map_label_X86_Arm_injective in H0; rewrite H0; eauto).
    eauto.  
Qed.  

Lemma map_event_Arm_X86_inverse:
  forall e,
  map_event_Arm_X86 (map_event_X86_Arm e) = e. 
Proof with eauto. 
    intros. destruct e; destruct lab; simpl; reflexivity.     
Qed. 

Lemma map_event_X86_Arm_inverse:
  forall e,
    map_event_X86_Arm (map_event_Arm_X86 e) = e. 
Proof.
    intros. destruct e; destruct lab; simpl; reflexivity.
Qed.

Lemma mapping_preserves_events_arm:
    forall execArm e,
        events execArm e <-> events (map_exec_Arm_X86 execArm) (map_event_Arm_X86 e). 
Proof with eauto.
    intros. split; intros.
    - simpl. exists e... 
    - simpl in H. destruct H  as [e0 [H0 H1]]. rewrite map_event_Arm_X86_injective in H1. 
      subst...
Qed.            

Lemma mapping_preserves_po: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    (po execArm) e1 e2 <-> (po (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).  
Proof with eauto. 
    intros. 
    split. 
    - intros. unfold mo. simpl. exists e1, e2... 
    - intros. destruct H  as [e3 [e4]] eqn:E. subst. unfold mo in a. simpl in a. destruct a as [e5 [e6]]. 
      apply map_event_Arm_X86_injective in e6. apply map_event_Arm_X86_injective in H. subst...  
Qed.

Lemma mapping_preserves_mo: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    (mo execArm) e1 e2 <-> (mo (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).  
Proof with eauto. 
    intros. 
    split. 
    - intros. unfold mo. simpl. exists e1, e2... 
    - intros. destruct H  as [e3 [e4]] eqn:E. subst. unfold mo in a. simpl in a. destruct a as [e5 [e6]]. 
      apply map_event_Arm_X86_injective in e6. apply map_event_Arm_X86_injective in H. subst...  
Qed.

Lemma mapping_preserves_rf: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    (rf execArm) e1 e2 <-> (rf (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).  
Proof with eauto. 
    intros. 
    split. 
    - intros. unfold mo. simpl. exists e1, e2... 
    - intros. destruct H  as [e3 [e4]] eqn:E. subst. unfold mo in a. simpl in a. destruct a as [e5 [e6]]. 
      apply map_event_Arm_X86_injective in e6. apply map_event_Arm_X86_injective in H. subst...  
Qed.

Lemma mapping_preserves_rmw: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    (rmw execArm) e1 e2 <-> (rmw (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).  
Proof with eauto. 
    intros. 
    split. 
    - intros. unfold mo. simpl. exists e1, e2... 
    - intros. destruct H  as [e3 [e4]] eqn:E. subst. unfold mo in a. simpl in a. destruct a as [e5 [e6]]. 
      apply map_event_Arm_X86_injective in e6. apply map_event_Arm_X86_injective in H. subst...  
Qed. 

Lemma mapping_preserves_fr: forall(execArm:@Execution LabelArm LabelClassArm) (e1 e2:Event), 
    (fr execArm) e1 e2 <-> (fr (map_exec_Arm_X86 execArm)) (map_event_Arm_X86 e1) (map_event_Arm_X86 e2).  
Proof with eauto. 
    intros. 
    split; intros; unfold fr in H; unfold fr; unfold HahnRelationsBasic.seq in H; destruct H as [z [H0 H1]];
    unfold Relation_Operators.transp in H0; unfold HahnRelationsBasic.seq; unfold Relation_Operators.transp.
    - exists (map_event_Arm_X86 z). split. 
        -- rewrite <- mapping_preserves_rf...
        -- rewrite <- mapping_preserves_mo... 
    - exists (map_event_X86_Arm z). split.  
        -- rewrite mapping_preserves_rf. rewrite map_event_Arm_X86_inverse...   
        -- rewrite mapping_preserves_mo. rewrite map_event_Arm_X86_inverse...
Qed. 

Lemma mapping_preserves_well_formedness: forall (execArm:@Execution LabelArm LabelClassArm), 
    well_formed execArm -> well_formed (map_exec_Arm_X86 execArm).
Proof with eauto. 
intros. 
unfold well_formed in H.
unfold well_formed. destruct H as [H0 [H1 H2]]. 
assert (He: forall e1, e1 = map_event_Arm_X86 (map_event_X86_Arm e1)). 
{ intros. rewrite map_event_Arm_X86_inverse...  }
split. 
- unfold well_formed_mo in H0. unfold well_formed_mo. 
  intros. 
  replace e1 with (map_event_Arm_X86 (map_event_X86_Arm e1)) in H. 
  replace e2 with (map_event_Arm_X86 (map_event_X86_Arm e2)) in H. 
  rewrite <- mapping_preserves_mo in H.  apply H0 in H. 
  destruct H as [H3 [H4 H5]]. rewrite mapping_preserves_both_write in H3. 
  rewrite mapping_preserves_same_loc_x86 in H4. unfold not in H5. split... split...  
  unfold not. intros.  apply H5. apply (map_event_X86_Arm_injective e1 e2)... 
  all:eauto.   
- split. 
  -- unfold well_formed_rf. unfold well_formed_rf in H1. intros.
     replace w with (map_event_Arm_X86 (map_event_X86_Arm w)) in H.
     replace r with (map_event_Arm_X86 (map_event_X86_Arm r)) in H.
     rewrite <- mapping_preserves_rf in H. apply H1 in H. 
     destruct H as [H3 [H4 [H5 [H6 H7]]]]. rewrite <- mapping_preserves_writes_x86 in H3.
     rewrite <- mapping_preserves_reads_x86 in H4. rewrite mapping_preserves_same_loc_x86 in H5. 
     rewrite mapping_preserves_same_val_x86 in H6. repeat split... all:try(eauto). 
     --- intros. specialize (H7 (map_event_X86_Arm w0)). rewrite map_event_X86_Arm_injective in H7. 
         apply H7. rewrite mapping_preserves_writes_x86 in H... rewrite mapping_preserves_rf. 
         rewrite map_event_Arm_X86_inverse.  rewrite map_event_Arm_X86_inverse... 
  -- unfold well_formed_rmw. unfold well_formed_rmw in H2. intros. 
     replace w with (map_event_Arm_X86 (map_event_X86_Arm w)) in H. 
     replace r with (map_event_Arm_X86 (map_event_X86_Arm r)) in H. 
     all:try(eauto). rewrite <- mapping_preserves_rmw in H. apply H2 in H.
     destruct H as [H3 [H4 [H5 H6]]]. rewrite <- mapping_preserves_reads_x86 in H3. 
     rewrite <- mapping_preserves_writes_x86 in H4. rewrite mapping_preserves_same_loc_x86 in H6. 
     unfold poimm in H5. rewrite mapping_preserves_po in H5. rewrite map_event_Arm_X86_inverse in H5. 
     rewrite map_event_Arm_X86_inverse in H5. destruct H5 as [H7 H8]. repeat split. all:try(eauto). 
     unfold not. intros. unfold not in H8. apply H8. replace r with (map_event_Arm_X86 (map_event_X86_Arm r)) in H. 
     replace w with (map_event_Arm_X86 (map_event_X86_Arm w)) in H. destruct H. replace x with (map_event_Arm_X86 (map_event_X86_Arm x)) in H.  
     repeat rewrite <- mapping_preserves_po in H. exists (map_event_X86_Arm x). all:eauto.
Qed. 

Lemma mapping_preserves_atomicity: forall (execArm:@Execution LabelArm LabelClassArm), 
    atomicity_axiom execArm -> atomicity_axiom (map_exec_Arm_X86 execArm). 
Proof with eauto. 
    intros. unfold atomicity_axiom in H. unfold atomicity_axiom. unfold not in H. unfold not. intros. apply H.
    destruct H0 as [x [y [H0 [H1 [H2 H3]]]]].  
    exists (map_event_X86_Arm x),  (map_event_X86_Arm y). 
    rewrite mapping_preserves_events_arm. rewrite mapping_preserves_events_arm.
    rewrite mapping_preserves_rmw. repeat split.   
    all:try(repeat rewrite map_event_Arm_X86_inverse; eauto). 
    unfold HahnRelationsBasic.seq in H3. unfold HahnRelationsBasic.seq. destruct H3 as [z [H3 H4]].  
    exists (map_event_X86_Arm z). split. 
    rewrite mapping_preserves_fr. repeat rewrite map_event_Arm_X86_inverse...    
    rewrite mapping_preserves_mo. repeat rewrite map_event_Arm_X86_inverse...
Qed.  



Lemma mapping_preserves_behaviour: forall (execArm:@Execution LabelArm LabelClassArm) (l:Location) (v:Value), 
    Behaviour (execArm) (l, v) <-> Behaviour (map_exec_Arm_X86 execArm) (l, v).  
Proof with eauto.
    intros. 
    unfold Behaviour. 
    split. 
    - intros. destruct H as [e]. destruct H as [H1 [H2 [H3 [H4 H5]]]]. 
      exists (map_event_Arm_X86 e). repeat split.
      -- simpl. exists e. split... 
      -- assert (H6: events execArm e /\ is_w (event_label e)). { eauto. } 
         rewrite mapping_preserves_writes_arm in H6. destruct H6 as [_ H6]...
      -- rewrite <- mapping_preserves_location_arm. apply H3.
      -- rewrite <- mapping_preserves_value_arm. apply H4.
      -- unfold not. intros. unfold not in H5. 
         apply H5. destruct H. exists (map_event_X86_Arm x).  
         apply mapping_preserves_mo. rewrite map_event_Arm_X86_inverse...
    - intros. destruct H as [e]. destruct H as [H1 [H2 [H3 [H4 H5]]]].
      exists (map_event_X86_Arm e). repeat split.
      -- simpl in H1. destruct H1.  destruct H.  rewrite H0. 
         rewrite map_event_X86_Arm_inverse...
      -- destruct e; destruct lab; simpl...
      -- simpl. destruct e; destruct lab; simpl...
      -- simpl. destruct e; destruct lab; simpl...
      -- unfold not. unfold not in H5. intros [e0 H6]. apply H5.
         exists (map_event_Arm_X86 e0). simpl. simpl in H1. destruct H1. destruct H.
         exists x, e0. repeat split. 
         --- rewrite H0 in H6. rewrite map_event_X86_Arm_inverse in H6...
         --- eauto.
Qed.
