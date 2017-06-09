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
  
  Inductive action : Type :=
  | ActInv (tid : tid) : nat -> action
  | ActResp (tid : tid) : nat -> action
  | Continue (tid: tid) : action
  | Emulate (tid: tid) : action
  | Commute (tid: tid) : action.

  Definition thread_of_action (a: action) :=
    match a with 
      | ActInv t n | ActResp t n => t
      | Continue t | Emulate t | Commute t => t
    end.
  Definition action_eq (a1 a2: action) :=
    match a1, a2 with
      | Commute t, Commute t'
      | Emulate t, Emulate t'
      | Continue t, Continue t' => t =? t'
      | ActInv n t, ActInv n' t'
      | ActResp t n, ActResp t' n' => (t =? t') && (n =? n')
      | _, _ => false
    end.
  Definition is_response (a : action) :=
    match a with
      | ActResp _ _ => true
      | _ => false
    end.

  Definition history : Type := list action.
  Definition is_implementation_history (h : history) :=
    fold_left (fun acc a => exists t n, (a = ActInv t n \/ a = Continue t \/ a = ActResp t n) /\ acc) h True.
  Definition is_interface_history (h : history) :=
    fold_left (fun acc a => exists t n, (a = ActInv t n \/ a = ActResp t n) /\ acc) h True.

  Definition base_history_pos_state : Type := tid -> nat.
  Definition current_history_state : Type := tid -> history.
  Definition commute_state : Type := tid -> bool.
  Inductive state : Type :=
  | State : base_history_pos_state -> current_history_state -> commute_state
            -> state.
  Definition get_state_components s := match s with | State bh ch comm => (bh, ch, comm) end.

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
  Function history_of_thread (h : history) (t : tid) : history :=
    match h with
      | [] => []
      | a :: tl => if thread_of_action a =? t then a :: history_of_thread tl t
                   else history_of_thread tl t
    end.
  Definition invocations_of_trace (tr:trace) : list action :=
    filter (fun a => match a with | ActInv _ _ => true | _ => false end) (history_of_trace tr).
  Definition responses_of_trace (tr:trace) : list action :=
    filter (fun a => match a with | ActResp _ _ => true | _ => false end) (history_of_trace tr).
  Definition trace_end_state (tr:trace) : option state :=
    match last tr NoEvent with
      | Event t s1 s2 a r => Some s2
      | _ => None
    end.
    
  Definition swappable (a1 a2 : action) :=
    match a1, a2 with
      | ActInv t _, ActInv t' _
      | ActInv t _, ActResp t' _
      | ActResp t _, ActInv t' _
      | ActResp t _, ActResp t' _ => t <> t'
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
  Definition write_tid_set {A : Type} (ts1 ts2 : tid -> A) : Ensemble tid :=
    fun tid => ts1 tid <> ts2 tid.
  Definition step_writes (s1 s2 : state) : Ensemble tid :=
    match s1, s2 with
      | State bh1 ch1 _, State bh2 ch2 _ =>
        Union tid (write_tid_set bh1 bh2) (write_tid_set ch1 ch2)
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
    forall a t n, a = ActInv t n -> n < num_invocations.
  Parameter resp_types_le_num_resp :
    forall r t n, r = ActResp t n -> n < num_responses.

  (*  Hypothesis response_always_exists :
    forall a ch, spec_oracle ch = true ->
                 t = thread_of_action a ->
                 exists rt, spec_oracle ((ActResp t rt) :: (a :: ch)) = true.*)

  Parameter spec_oracle_correct :
    forall history, List.In history spec <-> spec_oracle history = true.

  Parameter base_history_well_formed :
    forall t,
      base_history t = X ++ Commute t :: (history_of_thread Y t)
      /\ spec_oracle (rev (X ++ Y)) = true
      /\ sim_commutes Y X.

  Function get_invocations h acc := (* Note that we add from the front *)
    match h with
      | [] => acc
      | hd :: tl => match hd with
                      | ActInv _ _ => get_invocations tl
                                                      hd :: acc) (*XXX*)
    end.
  Definition X_invocations := get_invocations X []. (* XXX *)
  Definition Y_invocations := get_invocations Y [].
  Definition start_state : state := State (fun tid => 0) (fun tid => []) (fun tid => false).
End Emulator_Components.

Section Emulator.  
  Definition inc_tid_base_history_pos (bh : tid -> nat) (t: tid) :=
    fun tid => if tid =? t then bh tid + 1 else bh tid.
  Definition set_tid_commute (tc : commute_state) (t : tid) :=
    fun tid => if tid =? t then true else tc t.
  Definition add_to_current_history (ch : current_history_state) (a: action) :=
    fun tid => a :: ch tid. (* note that history goes backward for ease of proof *)
  
  Definition try_enter_conflict_free_mode (s: state) (t: tid) : state :=
    let '(bh, ch, comm) := get_state_components s in
    let hd := nth (bh t) (base_history t) (Emulate t) in
    let comm' := if action_eq hd (Commute t)
                 then set_tid_commute comm t else comm in
    let bh' := if action_eq hd (Commute t)
               then inc_tid_base_history_pos bh t else bh in
    State bh' ch comm'.

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
    let '(bh, ch, comm) := get_state_components s in
    let t := thread_of_action a in
    let new_history := ActResp t rt :: a :: (ch t) in
    let new_state := State bh (fun tid => new_history) comm in
    if spec_oracle new_history then (new_state, ActResp t rt)
    else match rt with
           | 0 => (s, Continue t) (* XXX we could just spin forever? *)
           | S rt' => get_emulate_response_helper s a rt'
         end.
  Definition get_emulate_response (s : state) (a : action) : state * action :=
    get_emulate_response_helper s a num_responses.
    
  Definition emulate_mode_and_perform_emulation (s : state) (a : action) (t : tid) :
    state * action :=
    let '(bh, ch, _) := get_state_components s in
    let hd := nth (bh t) (base_history t) (Emulate t) in
    if eqb (action_eq hd (Emulate t)) false
    then let s' := if bh t <=? length X then s
                   (* if we're in the commutative region *)
                   else get_and_set_combined_history s (ch 0) in
         get_emulate_response s' a
    else get_emulate_response s a.
    
  Definition emulator_act (s : state) (a : action) : (state * action) :=
    let t := thread_of_action a in
    let s' := try_enter_conflict_free_mode s t in
    let '(bh, ch, _) := get_state_components s' in
    let hd := nth (bh t) (base_history t) (Emulate t) in 
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