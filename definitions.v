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

  Definition base_history_pos_state : Type := tid -> nat.
  Definition current_history_state : Type := tid -> history.
  Definition commute_state : Type := tid -> bool.
  Inductive state : Type :=
  | State : base_history_pos_state -> current_history_state -> commute_state
            -> state.
  Definition get_base_history_pos_state s := match s with | State bh _ _ => bh end.
  Definition get_current_history_state s := match s with | State _ ch _ => ch end.
  Definition get_commute_state s := match s with | State _ _ comm => comm end.

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

Section Emulator_Hypotheses.
  Parameter spec : list history.
  Parameter spec_oracle : history -> bool.
  Parameter base_history : tid -> history.

  Parameter num_threads : nat.
  Hypothesis tid_le_num_threads : forall tid, tid < num_threads.
  Parameter num_invocations : nat.
  Parameter num_responses : nat.
  Hypothesis inv_types_le_num_invocations :
    forall a t n, a = ActInv t n -> n < num_invocations.
  Hypothesis resp_types_le_num_resp :
    forall r t n, r = ActResp t n -> n < num_responses.
(*  Hypothesis response_always_exists :
    forall a ch, spec_oracle ch = true ->
                 t = thread_of_action a ->
                 exists rt, spec_oracle ((ActResp t rt) :: (a :: ch)) = true.*)

  Hypothesis spec_oracle_correct :
    forall history, List.In history spec <-> spec_oracle history = true.

  Hypothesis base_history_well_formed :
    exists x y, forall t,
                  base_history t = x ++ (history_of_thread y t) /\
                  sim_commutes y x.
End Emulator_Hypotheses.

Section Emulator.  
  Definition inc_tid_base_history_pos (bh : tid -> nat) (t: tid) :=
    fun tid => if tid =? t then bh tid + 1 else bh tid.
  Definition set_tid_commute (tc : commute_state) (t : tid) :=
    fun tid => if tid =? t then true else tc t.
  Definition add_to_current_history (ch : current_history_state) (a: action) :=
    fun tid => a :: ch tid. (* note that history goes backward for ease of proof *)
  Definition try_enter_conflict_free_mode (s: state) (t: tid) : state :=
    let bh := get_base_history_pos_state s in
    let comm := get_commute_state s in
    let ch := get_current_history_state s in
    let hd := nth (bh t) (base_history t) (Emulate t) in
    let comm' := if action_eq hd (Commute t)
                 then set_tid_commute comm t else comm in
    let bh' := if action_eq hd (Commute t)
               then inc_tid_base_history_pos bh t else bh in
    State bh' ch comm'.

  Function get_emulate_response_helper (s : state) (a: action) (rt : nat) : state * action :=
    let bh := get_base_history_pos_state s in
    let comm := get_commute_state s in
    let ch := get_current_history_state s in
    let t := thread_of_action a in
    let new_history := ActResp t rt :: a :: (ch t) in
    let new_state := State bh (fun tid => if tid =? t then new_history else ch tid) comm in
    if spec_oracle new_history then (new_state, ActResp t rt)
    else match rt with
           | 0 => (s, Continue t) (* XXX we could just spin forever? *)
           | S rt' => get_emulate_response_helper s a rt'
         end.
  Function get_emulate_response (s : state) (a : action) : state * action :=
    get_emulate_response_helper s a num_responses.
  
  Definition get_and_set_combined_history (s : state) : state.
    let bh := get_base_history_pos_state s in
    let comm := get_commute_state s in
    let ch := get_current_history_state s in
    
  Admitted.
  Definition switch_and_perform_emulation (s : state) (a : action) (t : tid) : state * action :=
    let bh := get_base_history_pos_state s in
    let hd := nth (bh t) (base_history t) (Emulate t) in
    if eqb (action_eq hd (Emulate t)) false
    then let s' := get_and_set_combined_history s in
         get_emulate_response s' a
    else get_emulate_response s a.
    
  Definition emulator_act (s : state) (a : action) : (state * action) :=
    let t := thread_of_action a in
    let s' := try_enter_conflict_free_mode s t in
    match s' with
      | State bh ch comm =>
        let hd := nth (bh t) (base_history t) (Emulate t) in 
        (* get the response and perform emulation if necessary *)
        let (s_response, r) := if action_eq hd a
                        then (s', Continue t)
                        else if action_eq (Continue t) a &&
                                          is_response hd &&
                                          (thread_of_action hd =? t)
                             then (s', hd)
                             else switch_and_perform_emulation s' hd t in
        match s_response with
          | State bh_new ch_new comm_new =>
            let final_bh := if comm_new t
                            then inc_tid_base_history_pos bh_new t (* conflict-free mode *)
                            else fun tid => (bh_new tid) + 1 in (* replay mode *) 
            (State final_bh ch_new comm_new, r)
        end
    end.
  Function emulator_trace_helper (hbase hrun : history) (s0: state) (tr : trace) :=
    match hrun with
      | [] => tr
      | a :: rest => let (s', r) := emulator_act s0 a in
                     let t := thread_of_action a in
                     emulator_trace_helper hbase rest s' (Event t s0 s' a r :: tr)
    end.
  Definition emulator_trace (hbase hrun : history) (s0 : state) : trace :=
    emulator_trace_helper hbase hrun s0 [].

End Emulator.

Section Theorems.
  Lemma trace_conflict_free_cons : forall e tr,
    trace_conflict_free (e :: tr) -> trace_conflict_free tr.
  Admitted.
    
  (* if we have a SIM-comm region of history, then the emulator produces a
   * conflict-free trace for the SIM-comm part of the history *)
  Lemma emulator_impl_conflict_free :
    forall x y trX trY s0 sy sx t,
      x = history_of_trace trX ->
      y = history_of_trace trY ->
      ref_impl_generated_trace (trX ++ trY) s0 sy -> (* history is correct *)
      sim_commutes y x ->
      Some sx = trace_end_state (emulator_trace (x ++ (Commute t :: y)) x s0) ->
      trace_conflict_free (emulator_trace (x ++ (Commute t :: y)) y sx).
  Proof.
    intros h t.
    induction h; subst; intros tr tr0 s0 s1 Hhist Href Hsim.
    simpl; auto.
  Admitted.

  (* if we have the emulator instantiated with a SIM-comm history,
   * and the emulator acts on some input sequence, then the emulator
   * produces a trace that the ref_impl could have produced, i.e. a trace
   * that is in the spec *)
  Lemma emulator_impl_correct :
    forall x y trX trY s0 sy tr srand srand' t,
      (* set up the base commutative history for the emulator *)
      x = history_of_trace trX ->
      y = history_of_trace trY ->
      ref_impl_generated_trace (trX ++ trY) s0 sy ->
      sim_commutes y x ->
      (* running the emulator on any valid history is correct *)
      (* XXX todo invocations vs history *)
      ref_impl_generated_trace tr srand srand' ->
      List.In (history_of_trace (emulator_trace (x ++ Commute t :: y)
                                                (invocations_of_trace tr) srand))
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