Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators. 
Require Import Coq.Init.Nat.

Definition Location := nat.
Definition Value    := nat.
Definition UniqueId := nat.
Definition ThreadId := nat.


Inductive Tag : Type :=
| tmov : Tag
| trmw : Tag.

Definition UniquePred {A} (P : A -> Prop) :=
  forall x y, P x -> P y -> x = y.

Record LabelClass (Label : Type) := {
  labs_r : Label -> Prop;
  labs_w : Label -> Prop;
  labs_f : Label -> Prop;

  (* Mutual Exclusivity of Labels, an event is exclusively either a Read, Write or Fence. *)
  labs_xopt :
    forall l,
      (labs_r l \/ labs_w l \/ labs_f l) /\
      ~ (labs_r l /\ labs_w l) /\
      ~ (labs_r l /\ labs_f l) /\
      ~ (labs_w l /\ labs_f l);

  labs_r_unique : UniquePred labs_r;
  labs_w_unique : UniquePred labs_w;
  labs_f_unique : UniquePred labs_f;

  lab_r_tag :
    forall lab:Label, labs_r lab -> Tag;

  lab_w_tag :
    forall lab:Label, labs_w lab -> Tag;

  lab_r_loc :
    forall lab:Label, labs_r lab -> Location;

  lab_r_val :
    forall lab:Label, labs_r lab -> Value;

  lab_w_loc :
    forall lab:Label, labs_w lab -> Location;

  lab_w_val :
    forall lab:Label, labs_w lab -> Value;

  lab_eq_dec :
    forall x y : Label, {x = y} + {x <> y}
}.

(* Events all have the same structure, we might however wish to instantiate 
   Events for different architectures with different labels. *)
Inductive Event (Label:Type) {LabelProof : LabelClass Label}: Type := 
    | EventInit : UniqueId -> Location -> Value -> Event Label
    | EventSkip : UniqueId -> ThreadId -> Event Label
    | EventThread : UniqueId -> ThreadId -> Label -> Event Label. 