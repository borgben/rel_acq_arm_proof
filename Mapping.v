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
Lemma map_label_Arm_X86_injective:
  forall l l0,
  map_label_Arm_X86 l = map_label_Arm_X86 l0 ->
  l = l0.
Proof with eauto. 
    intros. 
    destruct l, l0; simpl in H. 
    all:try(inversion H; injection H; intros; subst; reflexivity). 
Qed.  

Lemma map_event_Arm_X86_injective :
  forall e e0,
  map_event_Arm_X86 e = map_event_Arm_X86 e0 ->
  e = e0. 
Proof. 
    intros. simpl in H. unfold map_event_Arm_X86 in H. destruct e, e0.
    all:try(inversion H).   
    all:try(injection H; intros; subst; apply map_label_Arm_X86_injective in H0; rewrite H0; eauto).  
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

Lemma mapping_preserves_writes: forall (execArm:@Execution LabelArm LabelClassArm) (e:@Event LabelArm LabelClassArm), 
    ((events execArm) e) /\ (is_w (event_label e)) 
    <-> 
    let eX86 := (map_event_Arm_X86 e) in 
        ((events (map_exec_Arm_X86 execArm)) eX86) /\ (is_w (event_label eX86)).
Proof with eauto. 
    intros.
    split. 
    - intros. destruct H as [H0 H1]. split. 
      -- simpl. exists e... 
      -- simpl. destruct e eqn:E; subst; destruct lab eqn:E0; subst; simpl... 
    - intros. split. destruct H as [H0 H1]. 
      -- simpl in H0. destruct H0 as [e0]. destruct H as [H2 H3]. apply map_event_Arm_X86_injective in H3. subst... 
      -- destruct H as [H1 H2]. destruct e eqn:E0; destruct lab eqn:E1; subst; simpl in H2. all:try(simpl; eauto). 
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

Lemma mapping_preserves_location: forall (e:Event),
    lab_loc (event_label e) = lab_loc (event_label (map_event_Arm_X86 e)).
Proof.
    intros.
    simpl.
    destruct e; destruct lab; simpl; reflexivity.
Qed.

Lemma mapping_preserves_value: forall (e:Event),
    lab_val (event_label e) = lab_val (event_label (map_event_Arm_X86 e)).
Proof.
    intros.
    simpl.
    destruct e; destruct lab; simpl; reflexivity.
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
         rewrite mapping_preserves_writes in H6. destruct H6 as [_ H6]...
      -- rewrite <- mapping_preserves_location. apply H3.
      -- rewrite <- mapping_preserves_value. apply H4.
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
