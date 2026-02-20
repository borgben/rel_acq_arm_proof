Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Init.Nat. 
Require Import Events.
Require Import Coq.Program.Basics. 

Record Execution (Label : Type) {LabelProof: LabelClass Label} := {
    (* Set of Events in the Execution Graph *)
    events: @Event Label LabelProof -> Prop; 

    (* The primitive relations *)

    (* po - relation over events in the same thread.*)
    po: @Event Label LabelProof ->  @Event Label LabelProof -> Prop;
    
    (* rf -  "reads from" write events read from read events.*)
    rf: @Event Label LabelProof ->  @Event Label LabelProof -> Prop;

    (* co - "coherence order" relates writes to the same location. *)
    co: @Event Label LabelProof ->  @Event Label LabelProof -> Prop;

    (* Derived Relation*)
    rmw: @Event Label LabelProof ->  @Event Label LabelProof -> Prop; 
}.  
 
(* Internal Relation *)
(* We are stating that an internal relation (intra-thread) formally means that 
   Given some binary relation R over the given Execution, the internal version of said relation 
   consists of elements in R which are also elements of program order (po). *)
Definition internal {Label : Type} {LabelProof : LabelClass Label}
           (R : Execution Label -> Event Label -> Event Label -> Prop)
           (ex : Execution Label)
    : Event Label -> Event Label -> Prop :=
        fun e1 e2 =>
            R ex e1 e2 /\ (@po Label LabelProof ex) e1 e2.

(* External Relation *)
(* Literally the opposite of internal. *)
Definition external {Label : Type} {LabelProof : LabelClass Label}
           (R : Execution Label -> Event Label -> Event Label -> Prop)
           (ex : Execution Label)
    : Event Label -> Event Label -> Prop :=
        fun e1 e2 => 
            R ex e1 e2 /\ ~((@po Label LabelProof ex) e1 e2). 


(* From Read Relation *)
Definition fr {Label : Type} {LabelProof : LabelClass Label}
           (ex : Execution Label)
    : Event Label -> Event Label -> Prop :=
        fun e1 e2 => ((flip (@rf Label LabelProof ex)) e1 e2) ⨾ (@co Label LabelProof ex). 

