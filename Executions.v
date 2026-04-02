From hahn Require Import Hahn.
From RelAcqProof Require Import Events.
Require Import Arith. 
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

Definition uid_unique {Label: Type} {LabelProof: LabelClass Label} (exec : Execution) : Prop :=
    forall e1 e2, events exec e1 -> events exec e2 -> 
        event_uid e1 = event_uid e2 -> e1 = e2. 

Definition well_formed_po {Label: Type} {LabelProof: LabelClass Label} (exec:Execution): Prop :=
    (forall e1 e2, po exec e1 e2 -> events exec e1 /\ events exec e2) 
    /\ 
    (forall (e:Event), (events exec) e <-> exists (e0:Event), ((events exec) e0) /\ ((po exec) e e0 \/ (po exec) e0 e))
    /\ 
    (forall e1 e2, po exec e1 e2 <-> seq_before e1 e2).  

(* Expresses that an mo relation can only exist between two independent writes on the same location. *)
Definition well_formed_mo {Label: Type} {LabelProof: LabelClass Label} (exec:Execution): Prop := 
    forall (e1 e2:Event), (mo exec) e1 e2 -> (events exec) e1 /\ (events exec) e2 /\ both_write e1 e2 /\ same_loc e1 e2 /\ e1 <> e2. 

(* Expresses that an rf relation can only exist between a write and a read on the same location, 
   with the same value, uid < uid'and that a read can only be from a single write *)
Definition well_formed_rf {Label: Type} {LabelProof: LabelClass Label} (exec:Execution): Prop := 
    forall (w r:Event),  (rf exec) w r -> (events exec) w /\ (events exec) r 
                                          /\ is_w (event_label w) 
                                          /\ is_r (event_label r)
                                          /\ same_loc w r 
                                          /\ same_val w r 
                                          /\ forall (w0:Event), is_w (event_label w0) -> (rf exec) w0 r -> w0 = w.   

(* Expresses that a read modify write relation can only exist between immediate reads and writes on the same location. *)
Definition well_formed_rmw {Label: Type} {LabelProof: LabelClass Label} (exec:Execution): Prop := 
    forall (r w:Event), (rmw exec) r w -> (events exec) r /\ (events exec) w
                                          /\ is_r (event_label r) 
                                          /\ is_w (event_label w)
                                          /\ (poimm exec) r w
                                          /\ same_loc r w. 

(* Predicate to express well-formedness on an execution graph. *)
Definition well_formed {Label: Type} {LabelProof: LabelClass Label} (exec:Execution): Prop := 
    uid_unique exec /\ well_formed_po exec /\ well_formed_mo exec /\ well_formed_rf exec /\ well_formed_rmw exec. 

(* Define atomicity and coherence axioms because they are generic across the two itegrations *)
Definition atomicity_axiom {Label: Type} {LabelProof : LabelClass Label} (e: Execution): Prop :=
    ~(exists (x y: Event), (events e) x /\ (events e) y  (* x and y are from the execution *)
                           /\ (rmw e) x y                (* x and y are in rmw *)
                           /\ ((fr e) ⨾ (mo e)) x y).     (* x and y are in rmw *)

Definition coherence_axiom {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): Prop :=
    acyclic ((poloc exec) ∪ (rf exec) ∪ (mo exec) ∪ (fr exec)).
    
Definition behaviour {Label: Type} {LabelProof: LabelClass Label} (X : Execution) : Location * Value -> Prop :=
  fun '(l,v) =>
    exists e,
      X.(events) e /\
      is_w (event_label e) /\
      lab_loc (event_label e) = l /\
      lab_val (event_label e) = v /\
      ~(exists (e': Event), (X.(mo) e e')).


Lemma well_formed_po_events: 
    forall {Label: Type} {LabelProof : LabelClass Label} (exec: @Execution Label LabelProof)
           (x y : @Event Label LabelProof),
    well_formed exec ->
        po exec x y ->
            events exec x /\ events exec y.
Proof with eauto. 
    intros Label LabelProof exec x y Hwf Hpo. 
    destruct Hwf as [Huid [[HpoWf _] _]]. eauto.
Qed.   

Lemma well_formed_rf_events: 
    forall {Label: Type} {LabelProof : LabelClass Label} (exec: @Execution Label LabelProof)
           (x y : @Event Label LabelProof),
    well_formed exec ->
        rf exec x y ->
            events exec x /\ events exec y.
Proof with eauto. 
    intros Label LabelProof exec x y Hwf Hrf. 
    destruct Hwf as [_ [_ [_ [HrfWf  _]]]]. 
    apply HrfWf in Hrf. destruct Hrf as [Hevx [Hevy _]]...  
Qed.

Lemma well_formed_rf_same_loc: 
    forall {Label: Type} {LabelProof : LabelClass Label} (exec: @Execution Label LabelProof)
           (x y : @Event Label LabelProof),
    well_formed exec ->
        rf exec x y ->
            same_loc x y. 
Proof with eauto. 
    intros Label LabelProof exec x y Hwf Hrf. 
    destruct Hwf as [_ [_ [ _ [HrfWf _]]]].  
    apply HrfWf in Hrf. destruct Hrf as [_ [_ [_ [_ [Hsmeloc _]]]]]...
Qed. 

Lemma well_formed_mo_write_r: 
    forall {Label: Type} {LabelProof : LabelClass Label} (exec: @Execution Label LabelProof)
           (x y : @Event Label LabelProof),
    well_formed exec ->
        mo exec x y ->
            is_w (event_label y). 
Proof with eauto. 
    intros Label LabelProof exec x y Hwf Hmo.  
    destruct Hwf as [_ [_ [HmoWf _]]]. 
    apply HmoWf in Hmo. destruct Hmo as [_ [_ [[_ Hwy] _]]]...  
Qed.

Lemma well_formed_mo_events: 
    forall {Label: Type} {LabelProof : LabelClass Label} (exec: @Execution Label LabelProof)
           (x y : @Event Label LabelProof),
    well_formed exec ->
        mo exec x y ->
            events exec x /\ events exec y.
Proof with eauto. 
    intros Label LabelProof exec x y Hwf Hmo.  
    destruct Hwf as [_ [_ [HmoWf _]]]. 
    apply HmoWf in Hmo. destruct Hmo as [Hevx [Hevy _]]...  
Qed.

Lemma well_formed_mo_same_loc: 
    forall {Label: Type} {LabelProof : LabelClass Label} (exec: @Execution Label LabelProof)
           (x y : @Event Label LabelProof),
    well_formed exec ->
        mo exec x y ->
            same_loc x y. 
Proof with eauto. 
    intros Label LabelProof exec x y Hwf Hmo. 
    destruct Hwf as [_ [_ [HmoWf _]]]. 
    apply HmoWf in Hmo. destruct Hmo as [_ [_ [_ [Hsmeloc _]]]]...
Qed. 

Lemma well_formed_rmw_events: 
    forall {Label: Type} {LabelProof : LabelClass Label} (exec: @Execution Label LabelProof)
           (x y : @Event Label LabelProof),
    well_formed exec ->
        rmw exec x y ->
            events exec x /\ events exec y.
Proof with eauto. 
    intros Label LabelProof exec x y Hwf Hrmw. 
    destruct Hwf as [Huid [_ [_ [_ HrmwWf]]]]. 
    apply HrmwWf in Hrmw. destruct Hrmw as [Hevx [Hevy _]]... 
Qed.   

Lemma well_formed_codom_rmw_write: 
    forall {Label: Type} {LabelProof : LabelClass Label} (exec: @Execution Label LabelProof)
           (x y : @Event Label LabelProof),
    well_formed exec ->
        rmw exec x y ->
            is_w (event_label y). 
Proof with eauto. 
    intros Label LabelProof exec x y Hwf Hrmw. 
    destruct Hwf as [Huid [_ [_ [_ HrmwWf]]]].
    unfold well_formed_rmw in HrmwWf.  
    apply HrmwWf in Hrmw. destruct Hrmw as [Hevx [Hevy [_ [Hw _]]]]... 
Qed.   

Lemma well_formed_dom_rmw_read: 
    forall {Label: Type} {LabelProof : LabelClass Label} (exec: @Execution Label LabelProof)
           (x y : @Event Label LabelProof),
    well_formed exec ->
        rmw exec x y ->
            is_r (event_label x). 
Proof with eauto. 
    intros Label LabelProof exec x y Hwf Hrmw. 
    destruct Hwf as [Huid [_ [_ [_ HrmwWf]]]].
    unfold well_formed_rmw in HrmwWf.  
    apply HrmwWf in Hrmw. destruct Hrmw as [Hevx [Hevy [Hr _]]]... 
Qed. 

Lemma well_formed_rmw_po: 
    forall {Label: Type} {LabelProof : LabelClass Label} (exec: @Execution Label LabelProof)
           (x y : @Event Label LabelProof),
    well_formed exec ->
        rmw exec x y ->
            po exec x y.  
Proof with eauto. 
    intros Label LabelProof exec x y Hwf Hrmw. 
    destruct Hwf as [Huid [_ [_ [_ HrmwWf]]]].
    unfold well_formed_rmw in HrmwWf.  
    apply HrmwWf in Hrmw. destruct Hrmw as [Hevx [Hevy [_ [_ [ [Hpo _] _]]]]]... 
Qed. 

Lemma fr_same_thread_implies_po:
    forall {Label: Type} {LabelProof : LabelClass Label} (exec: @Execution Label LabelProof)
           (x y : @Event Label LabelProof),
    well_formed exec ->
    fr exec x y ->
    same_thread x y ->
    po exec x y \/ po exec y x.
Proof with eauto.
    intros Label LabelProof exec x y Hwf  Hfr Hst.
    unfold well_formed in Hwf. 
    destruct Hwf as [Huniq [Hwf_po [Hwf_mo [Hwf_rf _]]]].
    unfold well_formed_po in *. 
    destruct Hwf_po as [Hpo_events [Hpo_connected Hpo_seq]]. 
    destruct x as [uid1 lab1 | uid1 tid1 lab1 ];
    destruct y as [uid2 lab2 | uid2 tid2 lab2 ]; 
    simpl in Hst; try contradiction. 
    destruct (lt_eq_lt_dec uid1 uid2) as [[Hlt | Heq] | Hgt]. 
    - left. apply Hpo_seq. simpl...
    - subst. exfalso.
      unfold fr in Hfr.
      destruct Hfr as [w [Hrf Hmo]].
      unfold transp in *. 
      destruct (Hwf_rf w (EventThread uid2 tid2 lab1) Hrf) as [_ [Hevr _]].
      destruct (Hwf_mo w (EventThread uid2 tid2 lab2) Hmo) as [_ [Hevw _]].
      assert (Heq : EventThread uid2 tid2 lab1 = EventThread uid2 tid2 lab2).
      { apply Huniq... }
      inversion Heq; subst. 
      destruct (Hwf_mo w (EventThread uid2 tid2 lab2) Hmo) as [_ [_ [_ [_ Hneq]]]].
      destruct (Hwf_rf w (EventThread uid2 tid2 lab2) Hrf) as [Hevw' [_ [Hiw [Hir _]]]].
      destruct (Hwf_mo w (EventThread uid2 tid2 lab2) Hmo) as [_ [_ [Hbw _]]].
      unfold both_write in Hbw. destruct Hbw as [_ Hiw2].
      simpl in Hir, Hiw2. exact (is_w_not_is_r _ Hiw2 Hir).    
    - right. apply Hpo_seq. simpl...
Qed.

Lemma mo_same_thread_implies_po:
    forall {Label: Type} {LabelProof : LabelClass Label} (exec: @Execution Label LabelProof)
           (x y : @Event Label LabelProof),
    well_formed exec ->
    mo exec x y ->
    same_thread x y ->
    po exec x y \/ po exec y x.
Proof with eauto.
    intros Label LabelProof exec x y Hwf Hmo Hst.
    unfold well_formed in Hwf. 
    destruct Hwf as [Huniq [Hwf_po [Hwf_mo [Hwf_rf _]]]].
    unfold well_formed_po in *. 
    destruct Hwf_po as [Hpo_events [Hpo_connected Hpo_seq]]. 
    destruct x as [uid1 lab1 | uid1 tid1 lab1 ];
    destruct y as [uid2 lab2 | uid2 tid2 lab2 ]; 
    simpl in Hst; try contradiction. 
    destruct (lt_eq_lt_dec uid1 uid2) as [[Hlt | Heq] | Hgt]. 
    - left. apply Hpo_seq. simpl...
    - subst. exfalso.
      destruct (Hwf_mo (EventThread uid2 tid2 lab1) (EventThread uid2 tid2 lab2) Hmo) 
        as [Hevx [Hevy [_ [_ Hneq]]]].
      assert (Heq : EventThread uid2 tid2 lab1 = EventThread uid2 tid2 lab2).
      { apply Huniq... }
      apply Hneq. exact Heq.
    - right. apply Hpo_seq. simpl...
Qed. 