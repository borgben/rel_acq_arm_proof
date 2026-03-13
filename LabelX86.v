From RelAcqProof Require Import Label. 
From hahn Require Import Hahn.

Inductive LabelX86 := 
| W_x86 (loc:Location) (val:Value)
| R_x86 (loc:Location) (val:Value). 

(* Instance LabelClassArm: LabelClass LabelArm.  *)
Instance LabelClassX86: LabelClass LabelX86 := {
    lab_loc l := match l with
                | W_x86 loc _ => loc 
                | R_x86 loc _ => loc 
                end;
      
    lab_val l := match l with
                | W_x86 _ val => val 
                | R_x86 _ val => val 
                end;

    is_r l := match l with
                | W_x86 _ _ => False  
                | R_x86 _ _ => True 
                end;

    is_w l := match l with
                | W_x86 _ _ => True  
                | R_x86 _ _ => False
                end;
}. 


(* lob =  *)