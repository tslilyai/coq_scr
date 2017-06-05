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

  Inductive event : Type := | NoEvent | Event (t: tid) (s1 s2 : state) (a r : action) : event.
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
      | _ :: tl => history_of_trace tl
    end.
  Definition invocations_of_trace (tr:trace) : list action :=
    filter (fun a => match a with | ActInv _ => true | _ => false end) (history_of_trace tr).
  Definition responses_of_trace (tr:trace) : list action :=
    filter (fun a => match a with | ActResp _ => true | _ => false end) (history_of_trace tr).
  Definition trace_end_state (tr:trace) : option state :=
    match last tr NoEvent with
      | Event t s1 s2 a r => Some s2
      | _ => None
    end.
    
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
      | Event t s1 s2 a r :: tl =>
        Union tid (step_writes s1 s2) (trace_writes tl)
      | _ => Empty_set tid
    end.
  Function trace_conflict_free (tr : trace) : Prop :=
    match tr with
      | Event t s1 s2 a r :: tl =>
        Intersection tid (step_writes s1 s2) (trace_writes tl) = Empty_set tid
        /\ trace_conflict_free tl
      | _ => True
  end.

  Definition sim_commutes (h pasth : history) : Prop. Admitted.
  Lemma sim_commutes_cons :
    forall h1 h2 pasth, sim_commutes (h1 ++ h2) pasth -> sim_commutes h1 pasth.
  Admitted.
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
               ref_impl_generated_trace ((Event all_tid (State rs th tc)
                                                (State rs' th tc) a r)
                                           :: tr)
                                        (State rs0 th tc) (State rs' th tc).
  Hypothesis ref_impl_correct : forall (tr : trace) (s1 s2 : state),
                                  ref_impl_generated_trace tr s1 s2 ->
                                  List.In (history_of_trace tr) spec.

  Parameter ref_impl_replay_state : history -> state -> state.

  (* captures idea that responses never change, also that *some* order of continues exist 
   * for every reordering *)
  Hypothesis ref_impl_generates_all_SIM_reordered_histories :
    forall tr0 tr1 tr1' s0 s1f,
      sim_commutes (history_of_trace tr1) (history_of_trace tr0) ->
      ref_impl_generated_trace (tr0 ++ tr1) s0 s1f ->
      reordered (history_of_trace tr1) (history_of_trace tr1') ->
      ref_impl_generated_trace (tr0 ++ tr1') s0
                               (ref_impl_replay_state (history_of_trace (tr0 ++ tr1)) s0).
  
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

  Definition try_switch_to_emulate (hbase : history) (s : state) (a : action) (t : tid) : state :=
    match s with
      | State rs th tc =>
        let hd := nth (th t) hbase (Emulate t) in
        if eqb (action_eq hd a) false
                && (eqb (action_eq a (Continue t)) false || eqb (action_eq hd (ActResp t)) false)
                && eqb (action_eq hd (Emulate t)) false
        then let th' := fun tid => (length hbase) + 1 in (* always return Emulate *)
             ref_impl_replay_state hbase (State rs th' tc)
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
  Function emulator_trace_helper (hbase hrun : history) (s0: state) (tr : trace) :=
    match hrun with
      | [] => tr
      | a :: rest => let (s', r) := emulator_act hbase s0 a in
                     let t := thread_of_action a in
                     emulator_trace_helper hbase rest s' (Event t s0 s' a r :: tr)
    end.
  Definition emulator_trace (hbase hrun : history) (s0 : state) : trace :=
    emulator_trace_helper hbase hrun s0 [].

End Emulator.

Section Theorems.
  Lemma emulator_trace_cons : forall t a h s0, exists s r,
                                emulator_trace (Commute t :: a :: h) (a::h) s0 =
                                (Event t s0 s a r) :: (emulator_trace (Commute t :: h) h s).
  Admitted.

  Lemma trace_conflict_free_cons : forall e tr,
    trace_conflict_free (e :: tr) -> trace_conflict_free tr.
  Admitted.
    
  (* if we have a SIM-comm region of history, then the emulator produces a
   * conflict-free trace for the SIM-comm part of the history *)
  Lemma emulator_impl_conflict_free :
    forall x y trX trY s0 sf sx t,
      x = history_of_trace trX ->
      y = history_of_trace trY ->
      ref_impl_generated_trace (trX ++ trY) s0 sf -> (* history is correct *)
      sim_commutes y x ->
      Some sx = trace_end_state (emulator_trace (x ++ (Commute t :: y)) x s0) ->
      trace_conflict_free (emulator_trace (x ++ (Commute t :: y)) y sx).
  Proof.
    intros h t.
    induction h; subst; intros tr tr0 s0 s1 Hhist Href Hsim.
    simpl; auto.
    pose (emulator_trace_cons t a h s0). destruct e as [s [r e]]. rewrite e.
    simpl; split.
    (* need to relate history_of_trace with emulator_trace / histories with traces *)
  Admitted.

  (* if we have the emulator instantiated with a SIM-comm history,
   * and the emulator acts on some input sequence, then the emulator
   * produces a trace that the ref_impl could have produced, i.e. a trace
   * that is in the spec *)
  Lemma emulator_impl_correct :
    forall t tr tr0 s0 s1 h,
      ref_impl_generated_trace (tr0 ++ tr) s0 s1 ->
      sim_commutes (history_of_trace tr) (history_of_trace tr0) ->
      List.In (history_of_trace (emulator_trace (Commute t :: history_of_trace tr)
                                                h s0 []))
              spec.
  Proof.
  Admitted.

  Theorem scalable_commutativity_rule :
    forall t tr tr0 s0 s1 h,
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