From RelAcqProof Require Import Executions.
From RelAcqProof Require Import Events.   
From RelAcqProof Require Import Label. 
From RelAcqProof Require Import LabelArm.
From RelAcqProof Require Import LabelX86. 

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

Definition map_exec_X86_Arm (execX86:@Execution LabelX86 LabelClassX86):@Execution LabelArm LabelClassArm := . 