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

Section Histories.
  Definition tid : Type := nat.

  Inductive invocation : Type :=
    | Inv : nat -> invocation.
  Inductive response : Type :=
  | Resp : nat -> response
  | NoResp.
  Definition invocation_eq (a1 a2: invocation) :=
    match a1, a2 with | Inv n, Inv n' => (n =? n') end.
  Definition response_eq (a1 a2: response) :=
    match a1, a2 with | Resp n, Resp n' => (n =? n')
                   | NoResp, NoResp => true
                   | _, _ => false
    end.
  Inductive mode : Type :=
  | Commute : mode
  | Emulate : mode
  | Replay : mode.

  Definition action : Type := tid * invocation * response.
  Definition action_invocation_eq (a : action) (i : invocation) :=
    match a, i with
      | (_, Inv i1, _), Inv i2 => i1 =? i2
    end.
  Definition thread_of_action (a : action) := let '(t, _, _) := a in t.
                      
  Definition history : Type := list action.
  Definition base_history_pos_state : Type := tid -> nat.
  Definition current_history_state : Type := tid -> history.
  Definition mode_state : Type := tid -> mode.
  Inductive state : Type :=
  | State : base_history_pos_state -> current_history_state -> mode_state
            -> state.
  Definition get_state_components s :=
    match s with | State bh ch md => (bh, ch, md) end.

  Inductive event : Type := | NoEvent | Event (s1 s2 : state) (a : action) : event.
  Definition trace : Type := list event.
  Function history_of_trace (tr: trace) : history :=
    match tr with
      | [] => []
      | Event s1 s2 a :: tl => a :: history_of_trace tl
      | _ :: tl => history_of_trace tl
    end.
  Function history_of_thread (h : history) (t : tid) : history :=
    match h with
      | [] => []
      | a :: tl => if thread_of_action a =? t then a :: history_of_thread tl t
                   else history_of_thread tl t
    end.
  Definition trace_end_state (tr:trace) : option state :=
    match last tr NoEvent with
      | Event s1 s2 a => Some s2
      | _ => None
    end.
    
  Definition swappable (a1 a2 : action) :=
    match a1, a2 with
      | (t, _, _), (t',_, _) => t <> t'
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
  Definition write_tid_set {A : Type} (ts1 ts2 : tid -> A) : Ensemble tid :=
    fun tid => ts1 tid <> ts2 tid.
  Definition step_writes (s1 s2 : state) : Ensemble tid :=
    match s1, s2 with
      | State bh1 ch1 md1, State bh2 ch2 md2 =>
        Union tid (write_tid_set md1 md2)
              (Union tid (write_tid_set bh1 bh2) (write_tid_set ch1 ch2))
    end.
 Function trace_writes (tr : trace) : Ensemble tid :=
    match tr with
      | Event s1 s2 a :: tl => Union tid (step_writes s1 s2) (trace_writes tl)
      | _ => Empty_set tid
    end.
  Function trace_conflict_free (tr : trace) : Prop :=
    match tr with
      | Event s1 s2 (t, _, _) :: tl => Intersection tid (step_writes s1 s2) (trace_writes tl)
                                       = Singleton tid t
                                       /\ trace_conflict_free tl
      | _ => True
  end.

  Definition sim_commutes (h past : history) : Prop. Admitted.
  Lemma sim_commutes_cons :
    forall h1 h2 past, sim_commutes (h1 ++ h2) past -> sim_commutes h1 past.
  Admitted.
End Commutativity.

Section Emulator_Components.
  Parameter num_threads : nat.
  Parameter num_invocations : nat.
  Parameter num_responses : nat.
  Parameter tid_le_num_threads : forall tid, tid < num_threads.
  Parameter inv_types_le_num_invocations :
    forall a n, a = Inv n -> n < num_invocations.
  Parameter resp_types_le_num_resp :
    forall r n, r = Resp n -> n < num_responses.

  Parameter spec : list history.
  Parameter spec_oracle : history -> bool.
  Parameter X : history.
  Parameter Y : history.
  Function get_invocations (h : history) (acc : list (tid * invocation)) :=
    match h with
      | [] => acc
      | (t, i, _) :: tl => get_invocations tl ((t, i) :: acc)
    end.
  Definition X_invocations := get_invocations X [].
  Definition Y_invocations := get_invocations Y [].

  Hypothesis response_always_exists : (* XXX *)
    forall i h t, spec_oracle h = true ->
                 exists r, spec_oracle ((t, i, r) :: h) = true.
  Parameter spec_oracle_correct :
    forall history, List.In history spec <-> spec_oracle history = true.

  Parameter base_history : tid -> history.
  Parameter base_history_well_formed :
    forall t,
      base_history t = X ++ (history_of_thread Y t)
      /\ spec_oracle (rev (X ++ Y)) = true
      /\ sim_commutes Y X.
  Definition start_state : state := State (fun tid => 0) (fun tid => []) (fun tid => Replay).
End Emulator_Components.

Section Emulator.  
  Definition inc_tid_base_history_pos (bh : tid -> nat) (t: tid) :=
    fun tid => if tid =? t then bh tid + 1 else bh tid.
  Definition set_all_mode (md: mode) :=
    fun (t : tid) => md.
  Definition add_to_tid_current_history (t : tid) (ch : current_history_state) (a : action) :=
    fun tid => if tid =? t then a :: ch tid else ch tid.    
  Definition add_to_all_current_histories (ch : current_history_state) (a: action) :=
    fun tid => a :: ch tid. (* note that history goes backward for ease of proof *)
  
  Function combine_histories (ch : current_history_state) (tid : tid)
           (combined : history) : history :=
    match tid with
      | 0 => combined
      | S n => combine_histories ch n ((firstn (length (ch tid) - length X) (ch tid)) ++ combined)
                                 (* note that we can just stick it on because Y is
                                  * sim-commutative! *)
    end.
  Definition switch_to_emulate (s : state) : state :=
    let '(bh, ch, mds) := get_state_components s in
    let hcombined := combine_histories ch num_threads (ch 0) in
    State bh (fun tid => hcombined) (set_all_mode Emulate).

  Function get_emulate_response_helper (s : state) (t: tid) (i : invocation) (rtyp : nat) :
    state * action :=
    let '(bh, ch, md) := get_state_components s in
    let response_action := (t, i, Resp rtyp) in
    let new_history := response_action :: (ch t) in
    let new_state := State bh (fun tid => new_history) md in
    if spec_oracle new_history then (new_state, (t, i, Resp rtyp))
    else match rtyp with
           | 0 => (new_state, (t, i, Resp rtyp)) (* XXX *)
           | S rt' => get_emulate_response_helper s t i rt'
         end.
  Definition get_emulate_response (s : state) (t: tid) (i : invocation) : state * action :=
    get_emulate_response_helper s t i num_responses.

  Definition get_base_history_response (s : state) (t: tid) (i : invocation) : state * action :=
    let '(bh, ch, mds) := get_state_components s in
    let hd := nth_error (base_history t) (bh t) in
    match hd with
      | None => let new_state := switch_to_emulate s in
                get_emulate_response new_state t i
      | Some bh_action => if action_invocation_eq bh_action i
                          then let new_state := State (inc_tid_base_history_pos bh t)
                                                      (add_to_tid_current_history t ch bh_action)
                                                      mds in                               
                               (new_state, bh_action)
                          else let new_state := switch_to_emulate s in
                               get_emulate_response new_state t i
    end.

  Definition emulator_act (s : state) (t: tid) (i : invocation) : (state * action) :=
    let '(bh, ch, mds) := get_state_components s in
    match mds t with
      | Emulate => get_emulate_response s t i
      | Commute => get_base_history_response s t i
      | Replay => let '(State bh' ch' mds', a) := get_base_history_response s t i in
                  if leb (length X) (bh t)
                  then (State bh' ch' (set_all_mode Commute), a)
                  else (State bh' ch' mds', a)
    end.
  Function emulator_trace_helper (ils : list (tid * invocation)) (s0: state) (tr : trace) :=
    match ils with
      | [] => tr
      | (t, i) :: rest => let (s', a) := emulator_act s0 t i in
                          emulator_trace_helper rest s' (Event s0 s' a :: tr)
    end.
  Definition emulator_trace (ils : list (tid * invocation)) (s0 : state) : trace :=
    emulator_trace_helper ils s0 [].

End Emulator.

Section Theorems.
  Lemma state_after_X_invocations :
    forall bh ch mds,
      Some (State bh ch mds) = trace_end_state (emulator_trace X_invocations start_state) ->
      forall t,
        mds t = Commute /\ bh t = length X.
  Proof.
  Admitted.
  
  Lemma trace_conflict_free_cons : forall e tr,
    trace_conflict_free (e :: tr) -> trace_conflict_free tr.
  Admitted.
    
  (* if we have a SIM-comm region of history, then the emulator produces a
   * conflict-free trace for the SIM-comm part of the history *)
  Lemma emulator_impl_conflict_free :
    forall sComm,
      Some sComm = trace_end_state (emulator_trace X_invocations start_state) ->
      trace_conflict_free (emulator_trace Y_invocations sComm).
  Proof.
  Admitted.

  (* if we have the emulator instantiated with a SIM-comm history,
   * and the emulator acts on some input sequence, then the emulator
   * produces a trace whose corresponding history is correct *)
  Lemma emulator_impl_correct :
    forall (ils : list (tid * invocation)),
      spec_oracle (history_of_trace (emulator_trace ils start_state)) = true.
  Proof.
  Admitted.

  Theorem scalable_commutativity_rule :
    forall sComm ils,
      (Some sComm = trace_end_state (emulator_trace X_invocations start_state) ->
      trace_conflict_free (emulator_trace Y_invocations sComm))
      /\ spec_oracle (history_of_trace (emulator_trace ils start_state)) = true.
  Proof.
    intros; split; [eapply emulator_impl_conflict_free | eapply emulator_impl_correct]; eauto.
  Qed.
End Theorems.