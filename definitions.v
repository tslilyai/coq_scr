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
    | Resp : nat -> response.
  Definition invocation_eq (a1 a2: invocation) :=
    match a1, a2 with | Inv n, Inv n' => (n =? n') end.
  Definition response_eq (a1 a2: response) :=
    match a1, a2 with | Resp n, Resp n' => (n =? n') end.

  Inductive mode : Type :=
  | Commute : mode
  | Emulate : mode
  | Replay : mode.

  Definition action : Type := tid * invocation * response.
  Definition action_eq a1 a2 :=
    match a1, a2 with | (t1, Inv i1, Resp r1), (t2, Inv i2, Resp r2) =>
                       (t1 =? t2) && (i1 =? i2) && (r1 =? r2) end.
  Definition thread_of_action (a : action) := let '(t, Inv i1, Resp r1) := a in t.
                      
  Definition history : Type := list action.
  Definition base_history_pos_state : Type := tid -> nat.
  Definition current_history_state : Type := tid -> history.
  Definition mode_state : Type := tid -> mode.
  Inductive state : Type :=
  | State : base_history_pos_state -> current_history_state -> mode_state
            -> state.
  Definition get_state_components s :=
    match s with | State bh ch md => (bh, ch, md) end.

  Inductive event : Type := | NoEvent | Event (t: tid) (s1 s2 : state)
                                              (i : invocation) (r : response) : event.
  Definition trace : Type := list event.
  Function history_of_trace (tr: trace) : history :=
    match tr with
      | [] => []
      | Event t s1 s2 a r :: tl => (t, a, r) :: history_of_trace tl
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
      | Event t s1 s2 a r => Some s2
      | _ => None
    end.
    
  Definition swappable (a1 a2 : action) :=
    match a1, a2 with
      | (t, Inv _, Resp _), (t', Inv _, Resp _) => t <> t'
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
      | Event t s1 s2 a r :: tl =>
        Union tid (step_writes s1 s2) (trace_writes tl)
      | _ => Empty_set tid
    end.
  Function trace_conflict_free (tr : trace) : Prop :=
    match tr with
      | Event t s1 s2 a r :: tl =>
        Intersection tid (step_writes s1 s2) (trace_writes tl) = Singleton tid t
        /\ trace_conflict_free tl
      | _ => True
  end.

  Definition sim_commutes (h past : history) : Prop. Admitted.
  Lemma sim_commutes_cons :
    forall h1 h2 past, sim_commutes (h1 ++ h2) past -> sim_commutes h1 past.
  Admitted.
End Commutativity.

Section Emulator_Components.
  Parameter spec : list history.
  Parameter spec_oracle : history -> bool.
  Parameter X : history.
  Parameter Y : history.
  Parameter base_history : tid -> history.
  Parameter num_threads : nat.
  Parameter num_invocations : nat.
  Parameter num_responses : nat.

  Parameter tid_le_num_threads : forall tid, tid < num_threads.
  Parameter inv_types_le_num_invocations :
    forall a n, a = Inv n -> n < num_invocations.
  Parameter resp_types_le_num_resp :
    forall r n, r = Resp n -> n < num_responses.
  (* XXX *)
  Hypothesis response_always_exists :
    forall i h t, spec_oracle h = true ->
                 exists r, spec_oracle ((t, i, r) :: h) = true.
  Parameter spec_oracle_correct :
    forall history, List.In history spec <-> spec_oracle history = true.
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
  Definition set_tid_mode (mds: mode_state) (t : tid) (md: mode) :=
    fun tid => if tid =? t then md else mds t.
  Definition add_to_current_history (ch : current_history_state) (a: action) :=
    fun tid => a :: ch tid. (* note that history goes backward for ease of proof *)
  
  Function combine_histories (ch : current_history_state) (tid : tid)
           (combined : history) : history :=
    match tid with
      | 0 => combined
      | S n => combine_histories ch n ((firstn (length (ch tid) - length X) (ch tid)) ++ combined)
                                 (* note that we can just stick it on because Y is
                                  * sim-commutative! *)
    end.
  Definition get_and_set_combined_history (s : state) (base : history) : state :=
    let '(bh, ch, comm) := get_state_components s in
    let hcombined := combine_histories ch num_threads base in
    State bh (fun tid => hcombined) comm.

  Function get_emulate_response_helper (s : state) (a: action) (rt : nat) : state * action :=
    let '(bh, ch, md) := get_state_components s in
    let t := thread_of_action a in
    let new_history := ActResp t rt :: a :: (ch t) in
    let new_state := State bh (fun tid => new_history) md in
    if spec_oracle new_history then (new_state, ActResp t rt)
    else match rt with
           | 0 => (s, ActResp t 0) (* XXX *)
           | S rt' => get_emulate_response_helper s a rt'
         end.
  Definition get_emulate_response (s : state) (a : action) : state * action :=
    get_emulate_response_helper s a num_responses.
        
  Definition emulator_act (s : state) (a : action) : (state * action) :=
    let t := thread_of_action a in
    let '(bh, ch, mds) := get_state_components s in
    match mds t with
      | Emulate => get_emulate_response s a
      | Commute => let hd := nth_error (bh t) (base_history t) in
                   match hd with
                     | None => switch_to_emulate_and_get_response
                     | Some bh_action => if 
    (* get the response and perform emulation if necessary *)
    let (s_response, r) := if action_eq hd a
                           then (s', Continue t)
                           else if action_eq (Continue t) a &&
                                             is_response hd &&
                                             (thread_of_action hd =? t)
                                then (s', hd)
                                else emulate_mode_and_perform_emulation s' hd t in
    let '(bh_new, ch_new, comm_new) := get_state_components s_response in
    let final_bh := if comm_new t
                    then inc_tid_base_history_pos bh_new t (* conflict-free mode *)
                    else fun tid => (bh_new tid) + 1 in (* replay mode *) 
    (State final_bh ch_new comm_new, r).
  Function emulator_trace_helper (hrun : history) (s0: state) (tr : trace) :=
    match hrun with
      | [] => tr
      | a :: rest => let (s', r) := emulator_act s0 a in
                     let t := thread_of_action a in
                     emulator_trace_helper rest s' (Event t s0 s' a r :: tr)
    end.
  Definition emulator_trace (hrun : history) (s0 : state) : trace :=
    emulator_trace_helper hrun s0 [].

End Emulator.

Section Theorems.
  Lemma state_after_X_invocations :
    forall bh ch comm,
      Some (State bh ch comm) = trace_end_state (emulator_trace X_invocations start_state) ->
      forall t,
        nth (bh t) (base_history t) (Emulate t) = Commute t /\
        ch t = X.
  Proof.
  Admitted.

  Lemma state_

  
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
    intros s0 sComm Hs0.
    pose base_history_well_formed as Hwf.
    pose spec_oracle_correct as Hspec.
    remember Y_invocations as yi.
    unfold Y_invocations in *.
    induction yi.
    simpl; auto.
    
  Admitted.

  (* if we have the emulator instantiated with a SIM-comm history,
   * and the emulator acts on some input sequence, then the emulator
   * produces a trace whose corresponding history is correct *)
  Lemma emulator_impl_correct :
    forall invocations,
      only_has_invocations invocations ->
      spec_oracle (history_of_trace (emulator_trace invocations start_state)) = true.
  Proof.
  Admitted.

  Theorem scalable_commutativity_rule :
    forall sComm invocations,
      (Some sComm = trace_end_state (emulator_trace X start_state) ->
      trace_conflict_free (emulator_trace Y_invocations sComm))
      /\ (only_has_invocations invocations ->
          spec_oracle (history_of_trace (emulator_trace invocations start_state)) = true).
  Proof.
    intros; split; [eapply emulator_impl_conflict_free | eapply emulator_impl_correct]; eauto.
  Qed.
End Theorems.