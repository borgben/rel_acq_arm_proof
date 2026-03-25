From hahn Require Import Hahn. 
Set Implicit Arguments. 

Definition UID := nat. 
Definition TID := nat. 
Definition Location := nat.
Definition Value := nat.

Class LabelClass (L : Type): Type := {
  lab_loc : L -> Location;
  lab_val : L -> Value; 
  is_r : L -> Prop;
  is_w : L -> Prop;
  is_w_not_is_r : forall l, is_w l -> ~ is_r l;
  is_r_not_is_w : forall l, is_r l -> ~ is_w l;
}. 

(* Events all have the same structure, we might however wish to instantiate 
   Events for different architectures with different labels. *)
Inductive Event {Label:Type} `{LabelProof:LabelClass Label} : Type := 
    | EventInit (uid:UID) (lab:Label) 
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

Definition event_uid {Label:Type} `{Label:LabelClass Label} (e :Event)  :=
  match e with
  | EventInit uid _ => uid 
  | EventThread uid _ _ => uid 
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

Lemma same_loc_trans:
    forall {Label: Type} {LabelProof: LabelClass Label}
           (e1 e2 e3 : @Event Label LabelProof),
    same_loc e1 e2 -> same_loc e2 e3 -> same_loc e1 e3.
Proof with eauto.
    intros Label LabelProof e1 e2 e3 H12 H23.
    unfold same_loc in *.
    rewrite H12...
Qed.

Lemma same_loc_sym:
    forall {Label: Type} {LabelProof: LabelClass Label}
           (e1 e2 : @Event Label LabelProof),
    same_loc e1 e2 -> same_loc e2 e1.
Proof with eauto.
    intros Label LabelProof e1 e2 H.
    unfold same_loc in *...
Qed. 