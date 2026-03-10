Definition Location := nat.
Definition Value := nat.

Class LabelClass (L : Type):Type := {
  lab_loc : L -> Location;
  lab_val : L -> Value; 
  is_r : L -> Prop;
  is_w : L -> Prop;
}. 