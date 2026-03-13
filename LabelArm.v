(* ob = (bob ∪ rfe ∪ moe ∪ fre)+ *)
(* bob = ((R_acq_pc ; po) ∪ (po ; W_rel))*)

(* ob is irreflexive *)

From RelAcqProof Require Import Label. 

Inductive LabelArm := 
| W_Rel (loc:Location) (val:Value)
| R_Acq_Pc (loc:Location) (val:Value). 

(* Instance LabelClassArm: LabelClass LabelArm.  *)
Instance LabelClassArm: LabelClass LabelArm := {
    lab_loc l := match l with
                | W_Rel loc _ => loc 
                | R_Acq_Pc loc _ => loc 
                end;
      
    lab_val l := match l with
                | W_Rel _ val => val 
                | R_Acq_Pc _ val => val 
                end;

    is_r l := match l with
                | W_Rel _ _ => False 
                | R_Acq_Pc _ _ => True 
                end;

    is_w l := match l with
                | W_Rel _ _ => True 
                | R_Acq_Pc _ _ => False 
                end;
}. 