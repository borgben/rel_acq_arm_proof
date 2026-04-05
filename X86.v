From RelAcqProof Require Import Events. 
From RelAcqProof Require Import Executions. 
Require Import Arith.
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

    is_w_not_is_r l := match l with
                       | W_x86 _ _    => fun _ H => H
                       | R_x86 _ _    => fun H _ => H
                       end;

    is_r_not_is_w l := match l with
                       | W_x86 _ _    => fun H _ => H
                       | R_x86 _ _    => fun _ H => H
                       end;
}.

(* atomic ops (in domain or codomain of rmw) act as a barrier between them and what happens before or after *)
Definition implid_x86 {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): relation Event :=
    let atomic := ⦗dom_rel (rmw exec)⦘ ∪ ⦗codom_rel (rmw exec)⦘ in
        ((po exec) ⨾ atomic) ∪ (atomic ⨾ (po exec)).

(* TSO enforces everything but W -> R to be ordered *)
(* is the last case even needed, considering we're esentially doing set difference? *)
Definition ppo_x86 {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): relation Event :=
    (po exec) \ (fun w r => is_w (event_label w) /\ is_r (event_label r)). 

(* happens before is defined by the union of several relations *)
Definition hb_x86 {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): relation Event :=
    ((ppo_x86 exec) ∪ (implid_x86 exec) ∪ (external rf exec) ∪ (fr exec) ∪ (mo exec))⁺. 

(* x86 Axiom: the transitive closure of happens before must be irreflexive (cycles cause it to be reflexive) *)
Definition ordered_before_axiom_x86 {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): Prop :=
    irreflexive (hb_x86 exec).  

Definition x86_consistent  {Label: Type} {LabelProof : LabelClass Label} (exec: Execution): Prop := 
    well_formed exec /\ atomicity_axiom exec /\ coherence_axiom exec /\ ordered_before_axiom_x86 exec.

Lemma same_thread_dec_x86:
    forall (e1 e2 : @Event LabelX86 LabelClassX86),
    {same_thread e1 e2} + {~ same_thread e1 e2}.
Proof with eauto.
    intros e1 e2.
    destruct e1; destruct e2; simpl.
    - right...
    - right...
    - right...
    - destruct (Nat.eq_dec tid tid0).
      left...
      right...
Qed. 

Lemma not_w_r_implies_other_cases_x86:
    forall (x y : @Event LabelX86 LabelClassX86),
    ~ (is_w (event_label x) /\ is_r (event_label y)) ->
        (is_w (event_label x) /\ is_w (event_label y)) 
        \/ (is_r (event_label x) /\ is_r (event_label y)) 
        \/ (is_r (event_label x) /\ is_w (event_label y)).
Proof with eauto.
    intros x y Hnot.
    destruct x as [uid1 lab1 | uid1 tid1 lab1] eqn:X;   
    destruct lab1 as [loc1 val1 | loc1 val1] eqn:L1; 
    destruct y as [uid2 lab2 | uid2 tid2 lab2] eqn:Y; 
    destruct lab2 as [loc2 val2 | loc2 val2] eqn:L2;
    simpl in *; eauto.     
Qed.

Lemma fr_in_events: 
    forall (exec : @Execution LabelX86 LabelClassX86) e1 e2,
    well_formed exec ->
    (fr exec) e1 e2 -> events exec e1 /\ events exec e2.
Proof with eauto. 
    intros exec e1 e2 Hwf Hfr. unfold fr in *. 
    unfold seq in *. unfold transp in *. 
    destruct Hfr as [z [Hrf Hmo]]. 
    destruct Hwf as  [Huid [Hpowf [Hmowf [Hrfwf Hrmwwf]]]].
    unfold well_formed_mo in *. unfold well_formed_rf in *. 
    apply Hmowf in Hmo. apply Hrfwf in Hrf. destruct Hrf as [_ [Heve1 _]]. 
    destruct Hmo as [_ [Heve2 _]]. split... 
Qed.

Lemma ppo_x86_in_events :
    forall (exec : @Execution LabelX86 LabelClassX86) e1 e2,
    well_formed exec ->
    ppo_x86 exec e1 e2 -> events exec e1 /\ events exec e2.
Proof with eauto.
    intros exec e1 e2 Hwf Hppo.
    unfold ppo_x86 in Hppo.
    destruct Hppo as [Hpo _].
    unfold well_formed in *. 
    destruct Hwf as [_ [HpoWf _]].
    unfold well_formed_po in *. 
    destruct HpoWf as [HpoEv _].
    apply HpoEv in Hpo...  
Qed.

Lemma implid_x86_in_events :
    forall (exec : @Execution LabelX86 LabelClassX86) e1 e2,
    well_formed exec ->
    implid_x86 exec e1 e2 -> events exec e1 /\ events exec e2.
Proof with eauto.
    intros exec e1 e2 Hwf Himp.
    unfold implid_x86 in Himp.
    unfold well_formed in Hwf. 
    destruct Hwf as [Huid [Hpowf [Hmowf [Hrfwf Hrmwwf]]]].  
    destruct Himp as [Himp | Himp].
    - destruct Himp as [z [Hpo Hatom]].
      unfold dom_rel, codom_rel in Hatom.
      unfold well_formed_po in *. 
      destruct Hpowf as [Hpowf _]. apply Hpowf in Hpo.   
      destruct Hatom as [[w [y Hrmw]] | [w [y Hrmw]]];  
      subst...  
    - destruct Himp as [z [Hatom Hpo]].
      unfold dom_rel, codom_rel in Hatom.
      unfold well_formed_po in *. 
      destruct Hpowf as [Hpowf _]. apply Hpowf in Hpo.      
      destruct Hatom as [[w Hrmw] | [w Hrmw]]; 
      subst...  
Qed.

Lemma hb_x86_in_events :
    forall (exec : @Execution LabelX86 LabelClassX86) e1 e2,
    well_formed exec ->
        hb_x86 exec e1 e2 -> 
            events exec e1 /\ events exec e2.
Proof with eauto.
    intros exec e1 e2 Hwf Hhb.
    unfold hb_x86 in Hhb.
    assert (Hwfcopy: well_formed exec)...  
    unfold well_formed in Hwfcopy. 
    destruct Hwfcopy as [Huid [Hpowf [Hmowf [Hrfwf Hrmwwf]]]].  
    induction Hhb as [e1 e2 Hbase | e1 e3 e2 _ IH1 _ IH2]. 
    - destruct Hbase as [[[[Hppo | Himp]| Hrf ]| Hfr ]| Hmo].     
      -- eapply ppo_x86_in_events... 
      -- eapply implid_x86_in_events... 
      -- unfold external in *. destruct Hrf as [Hrf _]. 
         unfold well_formed_rf in *. apply Hrfwf in Hrf.
         destruct Hrf as [Hev1 [Hev2 _]]. split...          
      -- apply fr_in_events...    
      -- unfold well_formed_mo in *. apply Hmowf in Hmo. 
         destruct Hmo as [Hev1 [Hev2 _]]. split... 
    - destruct IH1 as [He1 _].
      destruct IH2 as [_ He2].
      split...
Qed. 

Lemma coherence_implies_events:
    forall (exec : @Execution LabelX86 LabelClassX86) e1 e2,
    well_formed exec ->
        (poloc exec ∪ rf exec ∪ mo exec ∪ fr exec)⁺ e1 e2 ->
            events exec e1 /\ events exec e2.
Proof with eauto.
    intros exec e1 e2 Hwf Hc.
    induction Hc.
    - destruct H as [[[Hpoloc | Hrf] | Hmo] | Hfr].
      -- destruct Hpoloc as [_ Hpo].
         apply well_formed_po_events...
      -- apply well_formed_rf_events...
      -- apply well_formed_mo_events... 
      -- apply well_formed_fr_events...
    - destruct IHHc1 as [Hx _]...
      destruct IHHc2 as [_ Hz]...
Qed. 