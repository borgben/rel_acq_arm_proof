From RelAcqProof Require Import Events. 
From RelAcqProof Require Import Executions. 
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
}. 


(* ARM axiom *)
(* bob = ((R_acq_pc ; po) ∪ (po ; W_rel)) *)
(* intervening-write(rel) = rel ; W ; rel *)
(* lrs = W ; poloc / intervening-write(poloc) ; R *)
(* aob = rmw ∪ (W ∩ codomain(rmw) ; lrs ; R) *)
(* ob = (bob ∪ aob U rfe ∪ moe ∪ fre)+ *)

Definition R: relation Event := ⦗fun r => is_r (event_label r)⦘.
Definition W: relation Event := ⦗fun w => is_w (event_label w)⦘.

Definition bob_arm (exec: Execution): relation Event := 
    (R ⨾ (po exec)) ∪ ((po exec) ⨾ W) ∪ ((po exec) ⨾ ⦗dom_rel (rmw exec)⦘) ∪ (⦗codom_rel (rmw exec)⦘ ⨾ (po exec)). 

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
    well_formed exec /\ atomicity_axiom exec /\ coherence_axiom exec /\ ordered_before_axiom_arm exec. 