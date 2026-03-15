From hahn Require Import Hahn.
From RelAcqProof Require Import Label. 
From RelAcqProof Require Import Events.  
Set Implicit Arguments.

Record Execution {Label : Type} `{LabelProof: LabelClass Label} := {
    (* Set of Events in the Execution Graph *)
    events: Event -> Prop; 

    (* The primitive relations *)
    (* po - relation over events in the same thread.*)
    po: relation Event;

    (* rf -  "reads from" write events read from read events.*)
    rf: relation Event;

    (* co - "coherence order" relates writes to the same location. *)
    mo: relation Event;

    (* Derived Relation*)
    rmw: relation Event; 
}. 
 
(* Internal Relation *)
(* We are stating that an internal relation (intra-thread) formally means that 
   Given some binary relation R over the given Execution, the internal version of said relation 
   consists of elements in R which are also elements of program order (po). *)
Definition internal {Label : Type} {LabelProof : LabelClass Label}
           (R : Execution -> Event  -> Event -> Prop) (exec : Execution): relation Event :=
        fun e1 e2 =>
            R exec e1 e2 /\ same_thread e1 e2.

(* External Relation *)
(* Literally the opposite of internal. *)
Definition external {Label : Type} {LabelProof : LabelClass Label} 
            (R : Execution  -> Event -> Event -> Prop) (exec : Execution): relation Event :=
        fun e1 e2 => 
            R exec e1 e2 /\ ~(same_thread e1 e2). 


(* From Read Relation *)
Definition fr {Label : Type} {LabelProof : LabelClass Label} (exec : Execution): relation Event  := (((rf exec)⁻¹)  ⨾  (mo exec)).  

(* PoLoc *)
Definition poloc {Label: Type} {LabelProof: LabelClass Label} (exec:Execution): relation Event  := 
    fun e1 e2 => (same_loc e1 e2) /\ ((po exec) e1 e2).  

(* PoImm *)
Definition poimm {Label: Type} {LabelProof: LabelClass Label} (exec:Execution) : relation Event  := 
    fun e1 e2 =>  ((po exec) e1 e2) /\ ~(exists e3, ((po exec) e1 e3) /\ ((po exec) e3 e2)).

(* Expresses that an mo relation can only exist between two independent writes on the same location. *)
Definition well_formed_mo {Label: Type} {LabelProof: LabelClass Label} (exec:Execution): Prop := 
    forall (e1 e2:Event), (mo exec) e1 e2 -> both_write e1 e2 /\ same_loc e1 e2 /\ e1 <> e2. 

(* Expresses that an rf relation can only exist between a write and a read on the same location, 
   with the same value, and that a read can only be from a single write *)
Definition well_formed_rf {Label: Type} {LabelProof: LabelClass Label} (exec:Execution): Prop := 
    forall (w r:Event), (rf exec) w r -> is_w (event_label w) /\ is_r (event_label r)
                                         /\ same_loc w r 
                                         /\ same_val w r 
                                         /\ forall (w0:Event), is_w (event_label w0) -> (rf exec) w0 r -> w0 = w.   

(* Expresses that a read modify write relation can only exist between immediate reads and writes on the same location. *)
Definition well_formed_rmw {Label: Type} {LabelProof: LabelClass Label} (exec:Execution): Prop := 
    forall (r w:Event), (rmw exec) r w -> is_r (event_label r) /\ is_w (event_label w)
                                          /\ (poimm exec) r w
                                          /\ same_loc r w. 

(* Predicate to express well-formedness on an execution graph. *)
Definition well_formed {Label: Type} {LabelProof: LabelClass Label} (exec:Execution): Prop := 
    well_formed_mo exec /\ well_formed_rf exec /\ well_formed_rmw exec. 

(* Define atomicity and coherence axioms because they are generic across the two itegrations *)
Definition atomicity_axiom {Label: Type} {LabelProof : LabelClass Label} (e: Execution): Prop :=
    ~(exists (x y: Event), (events e) x /\ (events e) y  (* x and y are from the execution *)
                           /\ (rmw e) x y                (* x and y are in rmw *)
                           /\ ((fr e) ⨾ (mo e)) x y).     (* x and y are in rmw *)

Definition coherence_axiom {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): Prop :=
    acyclic ((poloc exec) ∪ (rf exec) ∪ (mo exec) ∪ (fr exec)).





(* atomic ops (in domain or codomain of rmw) act as a barrier between them and what happens before or after *)
Definition implid_x86 {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): relation Event :=
    let atomic := ⦗dom_rel (rmw exec)⦘ ∪ ⦗codom_rel (rmw exec)⦘ in
        ((po exec) ⨾ atomic) ∪ (atomic ⨾ (po exec)).

(* TSO enforces everything but W -> R to be ordered *)
(* is the last case even needed, considering we're esentially doing set difference? *)
Definition ppo_x86 {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): relation Event :=
    (po exec) \ (fun w r => is_w (event_label w) /\ is_r (event_label r) /\ ((po exec) r w)). 

(* happens before is defined by the union of several relations *)
Definition hb_x86 {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): relation Event :=
    (ppo_x86 exec) ∪ (implid_x86 exec) ∪ (external rf exec) ∪ (fr exec) ∪ (mo exec).

(* x86 Axiom: the transitive closure of happens before must be irreflexive (cycles cause it to be reflexive) *)
Definition ordered_before_axiom_x86 {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): Prop :=
    irreflexive ((hb_x86 exec)⁺).





(* ARM axiom *)
(* bob = ((R_acq_pc ; po) ∪ (po ; W_rel)) *)
Definition bob_arm {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): relation Event :=
    let R := ⦗fun r => is_r (event_label r)⦘ in 
    let W := ⦗fun w => is_w (event_label w)⦘ in
    (R ⨾ (po exec)) ∪ ((po exec) ⨾ W).

(* ob = (bob ∪ rfe ∪ moe ∪ fre)+ *)
Definition ordered_before_axiom_arm {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): Prop :=
    irreflexive (((bob_arm exec) ∪ (external rf exec) ∪ (external mo exec) ∪ (external fr exec))⁺).




Definition Behaviour {Label: Type} {LabelProof: LabelClass Label} (X : Execution) : Location * Value -> Prop :=
  fun '(l,v) =>
    exists e,
      X.(events) e /\
      is_w (event_label e) /\
      lab_loc (event_label e) = l /\
      lab_val (event_label e) = v /\
      ~(exists (e': Event), (X.(mo) e e')). 