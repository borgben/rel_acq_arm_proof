From RelAcqProof Require Import Events. 
From RelAcqProof Require Import Executions. 
Require Import Arith.
From hahn Require Import Hahn.

Inductive LabelArm := 
| W_Rel (loc:Location) (val:Value)
| R_Acq_Pc (loc:Location) (val:Value)
| R_Acq (loc:Location) (val:Value). 

(* Instance LabelClassArm: LabelClass LabelArm.  *)
Instance LabelClassArm: LabelClass LabelArm := {
    lab_loc l := match l with
                | W_Rel loc _    => loc 
                | R_Acq_Pc loc _ => loc
                | R_Acq  loc _   => loc
                end;
      
    lab_val l := match l with
                | W_Rel _ val    => val 
                | R_Acq_Pc _ val => val
                | R_Acq _ val    => val   
                end;

    is_r l := match l with
                | W_Rel _ _    => False 
                | R_Acq_Pc _ _ => True
                | R_Acq _ _    => True
                end;

    is_w l := match l with
                | W_Rel _ _    => True 
                | R_Acq_Pc _ _ => False
                | R_Acq _ _    => False 
                end;

    is_w_not_is_r l := match l with
                       | W_Rel _ _    => fun _ H => H
                       | R_Acq_Pc _ _ => fun H _ => H
                       | R_Acq _ _    => fun H _ => H
                       end;

    is_r_not_is_w l := match l with
                       | W_Rel _ _    => fun H _ => H
                       | R_Acq_Pc _ _ => fun _ H => H
                       | R_Acq _ _    => fun _ H => H
                       end;
}. 

Definition is_ra l := match l with 
                        | W_Rel _ _    => False 
                        | R_Acq_Pc _ _ => False 
                        | R_Acq _ _    => True
                      end.

(* ARM axiom *)
(* bob = ((R_acq_pc ; po) ∪ (po ; W_rel)) *)
(* intervening-write(rel) = rel ; W ; rel *)
(* lrs = W ; poloc / intervening-write(poloc) ; R *)
(* aob = rmw ∪ (W ∩ codomain(rmw) ; lrs ; R) *)
(* ob = (bob ∪ aob U rfe ∪ moe ∪ fre)+ *)

Definition R: relation Event := ⦗fun r => is_r (event_label r)⦘.
Definition W: relation Event := ⦗fun w => is_w (event_label w)⦘.
Definition RA: relation Event := ⦗fun r => is_ra (event_label r)⦘. 

Definition amo (exec:Execution): relation Event  := 
    fun e1 e2 => ((rmw exec) e1 e2) /\ is_ra (event_label e1).    

Definition bob_arm (exec: Execution): relation Event := 
    (R ⨾ (po exec)) 
    ∪ ((po exec) ⨾ W) 
    ∪ ((po exec) ⨾ ⦗dom_rel (amo exec)⦘) 
    ∪ (⦗codom_rel (amo exec)⦘ ⨾ (po exec)). 

Definition intervening_write (rel: relation Event): relation Event :=
    rel ⨾ W ⨾ rel.

Definition lrs (exec: Execution): relation Event := 
    W ⨾ ((poloc exec) \ ((intervening_write (poloc exec)) ⨾ R)).

Definition aob (exec: Execution): relation Event :=
    (rmw exec) ∪ (⦗codom_rel (rmw exec)⦘ ⨾ (lrs exec) ⨾ R). 

Definition ob (exec: Execution): relation Event := 
    ((aob exec) ∪ (bob_arm exec) ∪ (external rf exec) ∪ (external mo exec) ∪ (external fr exec))⁺.

Definition ordered_before_axiom_arm (exec: Execution): Prop := 
    irreflexive (ob exec).

Definition arm_consistent (exec: Execution): Prop := 
    well_formed exec /\ (amo exec) ≡ (rmw exec) /\ atomicity_axiom exec /\ coherence_axiom exec /\ ordered_before_axiom_arm exec.

Lemma same_thread_dec_arm:
    forall (e1 e2 : @Event LabelArm LabelClassArm),
    {same_thread e1 e2} + {~ same_thread e1 e2}.
Proof with eauto.
    intros e1 e2.
    destruct e1; destruct e2; simpl.
    - right...
    - right...
    - right...
    - destruct (Nat.eq_dec tid tid0).
      + left...
      + right...
Qed.

Lemma arm_consistent_amo_is_rmw: 
    forall (execArm: @Execution LabelArm LabelClassArm) (e0 e1: @Event LabelArm LabelClassArm),
        (amo execArm) ≡ (rmw execArm) -> (rmw execArm) e0 e1 -> (amo execArm) e0 e1.
Proof with eauto. 
    intros.
    unfold same_relation in *. destruct H as [Hamo Hrmw]. 
    unfold inclusion in *...      
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