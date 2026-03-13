From hahn Require Import Hahn. 
From RelAcqProof Require Import Label. 
Set Implicit Arguments. 
Definition UID := nat. 
Definition TID := nat. 

(* Events all have the same structure, we might however wish to instantiate 
   Events for different architectures with different labels. *)
Inductive Event {Label:Type} `{LabelProof:LabelClass Label} : Type := 
    | EventInit (uid:UID) (lab:Label) 
    (* | EventSkip : UniqueId -> ThreadId -> Event Label *)
    | EventThread (uid:UID) (tid:TID) (lab:Label).

Definition same_thread (Label:Type) `{Label:LabelClass Label} (e1 e2:Event): Prop := 
  match e1, e2 with 
  | EventThread _ tid _, EventThread _ tid' _ =>  tid = tid'  
  | _, _ => False  
  end. 

Definition event_label {Label:Type} `{Label:LabelClass Label} (e :Event)  :=
  match e with
  | EventInit _ lab => lab
  | EventThread _ _ lab => lab
  end.

Definition seq_before(Label:Type) `{Label:LabelClass Label} (e1 e2:Event):Prop := 
  match e1, e2 with 
  | _, EventInit _ _ => False 
  | EventInit _ _, EventThread _ _ _  => True 
  | EventThread uid tid _, EventThread uid' tid' _ => tid = tid' /\  uid < uid'
  end. 

Definition same_loc (Label:Type) `{Label:LabelClass Label} (e1 e2:Event): Prop :=  
  lab_loc (event_label e1) = lab_loc (event_label e2).
  
Definition same_val (Label:Type) `{Label:LabelClass Label} (e1 e2:Event): Prop := 
  lab_val (event_label e1) = lab_val (event_label e2). 

Definition both_write {Label: Type} {LabelProof: LabelClass Label} (e1 e2:Event): Prop := 
  is_w (event_label e1) /\ is_w (event_label e2). 
    