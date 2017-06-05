Require Import Bool Arith List Omega ListSet.
Require Import Recdef Morphisms.
Require Import Program.Tactics.
Require Import Relation_Operators.
Require FMapList.
Require FMapFacts.
Require Import Classical.
Require Import Coq.Classes.RelationClasses.
Require Import OrderedType OrderedTypeEx DecidableType.
Require Import Sorting.Permutation.
Import ListNotations.
Require Import OrderedType.
Require Import Ensembles.

Section State.

  Definition tid : Type := nat.
  Definition all_tid := 0. (* XXX probably needs to change *)

  Definition thread_history_state : Type := tid -> nat.
  Definition thread_commute_state : Type := tid -> nat. (* 0 or 1 *)
  Definition refstate : Type := nat.
  Inductive state := State : refstate -> thread_history_state -> thread_commute_state -> state.

End State.

Section Histories.

  Inductive action : Type :=
| ActInv (tid : tid) : action
| ActResp (tid : tid) : action
| Continue (tid: tid) : action
| Emulate (tid: tid) : action
| Commute (tid: tid) : action.

  Definition thread_of_action (a: action) :=
    match a with 
      | ActInv t | ActResp t | Continue t
      | Emulate t | Commute t => t
    end.
  Definition action_eq (a1 a2: action) :=
    match a1, a2 with
      | Commute t, Commute t'
      | Emulate t, Emulate t'
      | ActInv t, ActInv t'
      | ActResp t, ActResp t'
      | Continue t, Continue t' => t =? t'
      | _, _ => false
    end.
  Definition history : Type := list action.

  Inductive event : Type := Event (t: tid) (s1 s2 : state) (a r : action) : event.
  Definition trace : Type := list event.
  Function history_of_trace (tr: trace) : history :=
    match tr with
      | [] => []
      | Event t s1 s2 a r :: tl =>
        match a,r with
          | Continue t, Continue t' => history_of_trace tl
          | Continue t, _ => r :: history_of_trace tl
          | _, Continue t => a :: history_of_trace tl
          | _,_ => a :: r :: history_of_trace tl
        end
    end.
  Function invocations_of_trace (tr:trace) : list action :=
    filter (fun a => match a with | ActInv _ => true | _ => false end) (history_of_trace tr).
    
  Definition swappable (a1 a2 : action) :=
    match a1, a2 with
      | ActInv t, ActInv t'
      | ActInv t, ActResp t'
      | ActResp t, ActInv t'
      | ActResp t, ActResp t' => t <> t'
      | _, _ => False
    end.
  Inductive reordered : relation history :=
  | ro_perm_nil : reordered [] []
  | ro_perm_skip : forall x t1 t2,
                     reordered t1 t2 ->
                     reordered (x::t1) (x::t2)
  | ro_perm_swap : forall a2 a1 t,
                     swappable a2 a1 ->
                     reordered (a2 :: a1 :: t) (a1 :: a2 :: t)
  | ro_perm_trans : forall t1 t2 t3,
                      reordered t1 t2 ->
                      reordered t2 t3 ->
                      reordered t1 t3.

End Histories.

Section Commutativity.
  Definition write_tid_set (ts1 ts2 : tid -> nat) : Ensemble tid :=
    fun tid => ts1 tid <> ts2 tid.
  Definition step_writes (s1 s2 : state) : Ensemble tid :=
    match s1, s2 with
      | State rs1 th1 tc1, State rs2 th2 tc2 =>
        let writes_tid := Union tid (write_tid_set th1 th2) (write_tid_set tc1 tc2) in
        if rs1 =? rs2 then writes_tid
        else Add tid writes_tid all_tid
    end.
  Function trace_writes (tr : trace) : Ensemble tid :=
    match tr with
      | [] => Empty_set tid
      | Event t s1 s2 a r :: tl =>
        Union tid (step_writes s1 s2) (trace_writes tl)
    end.
  Function trace_conflict_free (tr : trace) : Prop :=
    match tr with
      | [] => True
      | Event t s1 s2 a r :: tl =>
        Intersection tid (step_writes s1 s2) (trace_writes tl) = Empty_set tid
        /\ trace_conflict_free tl
    end.

  Definition sim_commutes (h : history) (s : state) : Prop. Admitted.
End Commutativity.

Section Emulator.
  Parameter ref_impl : (refstate * action) -> (refstate * action).
  Parameter spec : list history.
  Parameter num_threads : nat.
  Hypothesis tid_le_num_threads : forall tid, tid <= num_threads.

  Inductive ref_impl_generated_trace : trace -> state -> state -> Prop :=
  | RINil : forall s, ref_impl_generated_trace [] s s
  | RICons : forall rs a rs' r tr rs0 th tc, 
               ref_impl (rs, a) = (rs', r) ->
               ref_impl_generated_trace tr (State rs0 th tc) (State rs th tc) ->
               ref_impl_generated_trace ((Event all_tid (State rs th tc) (State rs' th tc) a r) :: tr)
                                        (State rs0 th tc) (State rs' th tc).
  Hypothesis ref_impl_correct : forall (tr : trace) (s1 s2 : state),
                                  ref_impl_generated_trace tr s1 s2 ->
                                  List.In (history_of_trace tr) spec.

  Hypothesis comm_region_ref_impl_produces_same_results : 
    forall tr tr' s0 sf sf', sim_commutes (history_of_trace tr) s0 ->
                             ref_impl_generated_trace tr s0 sf ->
                             ref_impl_generated_trace tr' s0 sf' ->
                             invocations_of_trace tr = invocations_of_trace tr' ->
                             reordered (history_of_trace tr') (history_of_trace tr).
              
  Hypothesis SIM_reordered_histories_correct :
    forall tr0 tr1 tr2 tr1' s0 s0f,
      List.In (history_of_trace (tr0 ++ tr1 ++ tr2)) spec ->
      reordered (history_of_trace tr1) (history_of_trace tr1') ->
      ref_impl_generated_trace tr0 s0 s0f ->
      sim_commutes (history_of_trace tr1) s0f ->
      List.In (history_of_trace (tr0 ++ tr1' ++ tr2)) spec.
  
  Definition inc_index (th : tid -> nat) (t: tid) :=
    fun tid => if tid =? t then th tid + 1 else th tid.
  Definition set_index (tc : tid -> nat) (t : tid) :=
    fun tid => if tid =? t then 1 else tc t.
  Definition try_enter_conflict_free_mode (hbase: history) (s: state) (t: tid) : state :=
    match s with
      | State rs th tc =>
        let hd := nth (th t) hbase (Emulate t) in
        let tc' := if action_eq hd (Commute t) then set_index tc t else tc in
        let th' := if action_eq hd (Commute t) then inc_index th t else th in
        State rs th' tc'
    end.
  Function ref_impl_replay_helper (hbase : history)
           (th: tid -> nat) (t: tid) (rs : refstate)
  : refstate :=    
    match t with
      | 0 => rs
      | S t' => let new_rs := fold_left
                                (fun rs a => let (rs', r) :=
                                                 match a with
                                                   | ActInv _ => ref_impl (rs, a)
                                                   | _ => (rs, a) end
                                             in rs')
                                       (firstn (th t) hbase) rs
               in ref_impl_replay_helper hbase th t' new_rs
    end.
  Definition ref_impl_replay (hbase: history) (th: tid -> nat) (rs0 : refstate) : refstate :=
    ref_impl_replay_helper hbase th num_threads rs0.
  Definition try_switch_to_emulate (hbase : history) (s : state) (a : action) (t : tid) : state :=
    match s with
      | State rs th tc =>
        let hd := nth (th t) hbase (Emulate t) in
        if eqb (action_eq hd a) false
                && (eqb (action_eq a (Continue t)) false || eqb (action_eq hd (ActResp t)) false)
                && eqb (action_eq hd (Emulate t)) false
        then let th' := fun tid => (length hbase) + 1 in (* always return Emulate *)
             let rs' := ref_impl_replay hbase th rs in
             State rs' th' tc
        else s
    end.
  Definition emulator_act
             (hbase : history) (s : state) (a : action) : (state * action) :=
    let t := thread_of_action a in
    let s' := try_enter_conflict_free_mode hbase s t in
    let s'' := try_switch_to_emulate hbase s' a t in
    match s'' with
      | State rs th tc => 
        let hd := nth (th t) hbase (Emulate t) in
        let (rs', r) := if action_eq hd a then (rs, Continue t)
                        else if action_eq a (Continue t) && action_eq hd (ActResp t)
                             then (rs, hd)
                             else ref_impl (rs, a) in (* XXX we know we must be in emulate mode *)
        if action_eq hd (Emulate t) then (State rs' th tc, r) (* emulate mode *)
        else let th' := if tc t =? 1 then inc_index th t (* conflict-free mode *)
                        else fun tid => (th tid) + 1 in (* replay mode *)
             (State rs th' tc, r)
    end.
  Function emulator_trace (hbase hrun : history) (s0 : state) (tr : trace) : trace :=
    match hrun with
      | [] => tr
      | a :: rest => let (s', r) := emulator_act hbase s0 a in
                     let t := thread_of_action a in
                     emulator_trace hbase rest s' (Event t s0 s' a r :: tr)
    end.

End Emulator.

Section Theorems.
  Lemma sim_commutes_cons : forall a h s t s' r,
                              sim_commutes (a :: h) s ->
                              emulator_act (Commute t :: a :: h) s a = (s', r) ->
                              sim_commutes h s'.
  Admitted.

  Lemma emulator_trace_cons : forall t a h s0, exists s r,
                                emulator_trace (Commute t :: a :: h) (a::h) s0 [] =
                                (Event t s0 s a r) :: (emulator_trace (Commute t :: h) h s []).
  Admitted.

  Lemma trace_conflict_free_cons : forall e tr,
    trace_conflict_free (e :: tr) -> trace_conflict_free tr.
  Admitted.
    
  (* if we have a correct trace whose corresponding history is SIM-comm,
   * then the emulator produces a conflict-free trace for that history *)
  Lemma emulator_impl_conflict_free :
    forall t tr s0 s1,
      ref_impl_generated_trace tr s0 s1 ->
      sim_commutes (history_of_trace tr) s0 ->
      trace_conflict_free (emulator_trace (Commute t :: (history_of_trace tr))
                                          (history_of_trace tr)
                                          s0 []).
  Proof.
    intros t tr s0 s1 Hrigt Hsi.
    remember (history_of_trace tr) as h.
    generalize dependent s0. generalize dependent tr. 
    induction h; subst; intros.
    simpl; auto.
    pose (emulator_trace_cons t a h s0). destruct e as [s [r e]]. rewrite e.
    simpl; split.
    
  Admitted.

  (* if we have the emulator instantiated with a SIM-comm history,
   * and the emulator acts on some input sequence, then the emulator
   * produces a correct trace for the spec *)
  Lemma emulator_impl_correct :
    forall t tr s0 s1 h,
      ref_impl_generated_trace tr s0 s1 ->
      sim_commutes (history_of_trace tr) ->
      List.In (history_of_trace (emulator_trace (Commute t :: history_of_trace tr)
                                                h s0 []))
              spec.
  Proof.
  Admitted.

  Theorem scalable_commutativity_rule :
    forall t tr s0 s1 h,
      ref_impl_generated_trace tr s0 s1 ->
      sim_commutes (history_of_trace tr) ->
      trace_conflict_free (emulator_trace (Commute t :: (history_of_trace tr))
                                          (history_of_trace tr) s0 [])
      /\ List.In
           (history_of_trace (emulator_trace (Commute t :: history_of_trace tr) h s0 []))
           spec.
  Proof.
    intros; split; [eapply emulator_impl_conflict_free | eapply emulator_impl_correct]; eauto.
  Qed.
End Theorems.