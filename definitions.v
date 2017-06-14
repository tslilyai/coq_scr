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

  Parameter num_threads : nat.
  Parameter tid_le_num_threads : forall tid, tid < num_threads.

  Definition action : Type := tid * invocation * response.
  Definition action_invocation_eq (a : action) (i : invocation) :=
    match a, i with
      | (_, Inv i1, _), Inv i2 => i1 =? i2
    end.
  Definition thread_of_action (a : action) := let '(t, _, _) := a in t.

  Definition history : Type := list action.
  Function history_of_thread (h : history) (t : tid) : history :=
    match h with
      | [] => []
      | a :: tl => if thread_of_action a =? t then a :: history_of_thread tl t
                   else history_of_thread tl t
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

  Definition sim_commutes (h past : history) : Prop. Admitted.
End Histories.

Section MachineState.
  Parameter max_response_number : nat.
  Parameter spec : history -> Prop.
  Parameter spec_nonempty : spec [].
  Parameter spec_prefix_closed : forall h h1 h2,
                                    spec h ->
                                    h = h2 ++ h1 ->
                                    spec h1.
  Parameter spec_last_inv : forall t i r h,
                               spec ((t,i,r) :: h) ->
                               spec ((t, i, NoResp) :: h).
  Hypothesis spec_responses: forall x h1 t i r h2,
                               spec ((x :: h1) ++ (t,i,r) :: h2) ->
                               r <> NoResp.
  Hypothesis spec_resp_exists : forall t i h,
                                  spec ((t,i,NoResp) :: h) ->
                                  exists rtyp, rtyp < max_response_number
                                               /\ spec ((t,i,Resp rtyp) :: h).
  Parameter spec_oracle : history -> bool.
  Parameter spec_oracle_correct :
    forall history, spec history <-> spec_oracle history = true.

  Parameter X : history.
  Definition Y : history := [].
  Function get_invocations (h : history) (acc : list (tid * invocation)) :=
    match h with
      | [] => acc
      | (t,i,_) :: tl => get_invocations tl ((t,i) :: acc)
    end.
  Definition X_invocations := get_invocations X [].
  Definition Y_invocations := get_invocations Y [].
  Parameter X_and_Y_in_spec : spec (Y ++ X).
  
  Record state := mkState { X_copy : history;
                            Y_copy : tid -> history;
                            preH : history;
                            commH : tid -> history;
                            postH : history;
                            md : mode
                          }.

  Definition start_state : state := mkState X (history_of_thread Y) [] (fun tid => []) [] Replay.
End MachineState.
  
Section Conflict.
  Definition write_tid_set {A : Type} (ts1 ts2 : tid -> A) : Ensemble tid :=
    fun tid => ts1 tid <> ts2 tid.
  Definition step_writes (s1 s2 : state) : Ensemble tid :=
    Union tid
          (write_tid_set s1.(commH) s2.(commH))
          (write_tid_set s1.(Y_copy) s2.(Y_copy)).
 Definition conflict_free_step (t :tid) (s1 s2 : state) :=
   step_writes s1 s2 = Singleton tid t /\
   s1.(md) = s2.(md) /\
   s1.(X_copy) = s2.(X_copy) /\
   s1.(preH) = s2.(preH) /\
   s1.(postH) = s2.(postH).
End Conflict.

Section Emulator.
  Function combine_tid_commH (s : state) (t : tid) (acc : history) :=
    let newacc := (s.(commH) t) ++ acc in
    match t with
      | 0 => newacc
      | S t' => combine_tid_commH s t' newacc
    end.
  Definition get_state_history (s : state) := s.(preH) ++ s.(postH). (*
    s.(preH) ++ (combine_tid_commH s num_threads []) ++ s.(postH).*)
  Function get_emulate_response_helper (s : state) (t: tid) (i : invocation)
           (rtyp : nat) (fuel : nat) :
    state * action :=
    let response_action := (t, i, Resp rtyp) in
    let state_history := get_state_history s in
    let new_history := response_action :: state_history in
    if spec_oracle (response_action :: state_history) then
      (mkState s.(X_copy) s.(Y_copy) s.(preH) s.(commH) (response_action :: s.(postH)) Emulate,
       (t, i, Resp rtyp))
    else match fuel with
           | 0 => (s, (t, i, NoResp)) (* should never reach this *)
           | S n' => get_emulate_response_helper s t i (S rtyp) n'
         end.
  Definition get_emulate_response (s : state) (t: tid) (i : invocation) : state * action :=
    get_emulate_response_helper s t i 0 max_response_number.
  Definition get_commute_response (s : state) (t: tid) (i: invocation) : state * action :=
    match rev (s.(Y_copy) t) with
      | [] => get_emulate_response s t i
      | hd::tl => if action_invocation_eq hd i
                  then (mkState s.(X_copy) (fun tid => if tid =? t
                                                       then (rev tl)
                                                       else s.(Y_copy) t)
                                           s.(preH) (fun tid => if tid =? t
                                                                then hd::(s.(commH) t)
                                                                else s.(commH) tid)
                                                    s.(postH) Commute, hd)
                    else get_emulate_response s t i
    end.
  Definition get_replay_response (s : state) (t: tid) (i : invocation) : state * action :=
    match rev s.(X_copy) with
      | [] => get_commute_response s t i (* will change to Commute... *)
      | hd::tl => if action_invocation_eq hd i
                  then (mkState (rev tl) s.(Y_copy) (hd::s.(preH))
                                                    s.(commH) s.(postH) Replay, hd)
                          else get_emulate_response s t i
    end.
  Definition emulator_act (s : state) (t: tid) (i : invocation) : (state * action) :=
    match s.(md) with
      | Emulate => get_emulate_response s t i
      | Commute => get_commute_response s t i
      | Replay => get_replay_response s t i
    end.

  Inductive generated : state -> history -> Prop :=
  | GenNil : generated start_state []
  | GenCons : forall s1 s2 t i r h,
      emulator_act s1 t i = (s2, (t,i,r)) ->
      generated s1 h ->
      generated s2 ((t,i,r)::h).
End Emulator.

Section Theorems.
  
  Lemma generated_history_corresponds_state_history :
    forall s h, (*combined_commH*)
      generated s h ->
(*      reordered combined_commH (combine_tid_commH s num_threads []) ->
      s.(preH) ++ combined_commH ++ s.(postH) = h.*)
      s.(preH) ++ s.(postH) = h.
  Admitted.
  
  Lemma response_always_exists :
    forall s h t i s' a',
      generated s h ->
      spec ((t,i,NoResp) :: h) ->
      emulator_act s t i = (s', a') ->
      exists rtyp, a' = (t,i,Resp rtyp).
  Admitted.

  Ltac discriminate_noresp :=
    match goal with
    | [ H : (?s, (?t, ?i, NoResp)) = (?s', ?a') |- _ ] =>
      let M := fresh "SO" in
      assert (exists rtyp, a' = (t, i, Resp rtyp)) as M; [
          now eapply response_always_exists; eauto | 
          destruct M as [rtyp_new M] ; subst; discriminate] end.

  Lemma inv_of_action_eq : forall a t i r,
    a = (t, i, r) ->
    action_invocation_eq a i = true.
  Proof.
    intros. unfold action_invocation_eq; subst. destruct i. apply Nat.eqb_refl.
  Qed.

  Lemma get_commute_response_correct : Prop. Admitted.

  Lemma get_replay_response_correct :
    forall h1 h2 s s' a' t i r,
      h1 ++ (t,i,r) :: h2 = X ->
      generated s h2 ->
      emulator_act s t i = (s', a') ->
      s.(md) = Replay /\ s.(preH) = h2 /\ s.(X_copy) = h1 ++ [(t,i,r)] /\
      s'.(md) = Replay /\ s'.(preH) = (t,i,r)::h2 /\ s'.(X_copy) = h1 /\
      a' = (t,i,r) /\ spec ((t,i,r) :: h2).
  Proof.
    intros h1 h2 s s' a' t i r HX Hgen Hact.
    pose Hact as Hact'. 
    generalize dependent t.
    generalize dependent i.
    generalize dependent r.
    generalize dependent h1.
    remember (length h2) as Hlen.
    generalize dependent h2.
    induction (Hlen); intros.
    - destruct h2; try discriminate.
      inversion Hgen; subst.
      unfold emulator_act in Hact'. 
      unfold start_state in Hact; simpl in *.
      unfold get_replay_response in Hact'. simpl in *.
      rewrite <- HX in Hact'; simpl in *.
      rewrite rev_unit in Hact'.
      rewrite (inv_of_action_eq (t,i,r) t i r) in Hact'.

      repeat (split; auto); inversion Hact'; auto; simpl.
      apply rev_involutive.
      assert (spec X) as HspecX.
      eapply (spec_prefix_closed (Y++X) X Y); eauto. apply X_and_Y_in_spec. 
      eapply spec_prefix_closed. apply HspecX. symmetry in HX; apply HX.
      auto.

    - 


    
  Admitted.
  (* TODO: lemmas about transitions *)
  
  Lemma get_emulate_response_correct :
    forall s h t i s' a',
    generated s h ->
    s.(md) = Emulate ->
    spec ((t,i,NoResp) :: h) ->
    emulator_act s t i = (s', a') ->
    (exists rtyp, a' = (t,i,Resp rtyp))
    /\ spec (a' :: h)
    /\ s'.(md) = Emulate.
  Proof.
    intros s h t i s' a' Hgen Hmd Hspec Hact.
    pose Hact as Hact'.
    split. eapply response_always_exists; eauto.
    split;
      unfold emulator_act in Hact';
      rewrite Hmd in Hact';
      unfold get_emulate_response in Hact';
      functional induction (get_emulate_response_helper s t i 0 max_response_number).
    2,5: discriminate_noresp.
    2,4: now apply IHp in Hact'.
    all : inversion Hact'; subst; auto.
    pose (generated_history_corresponds_state_history s h Hgen) as Hh.
    unfold get_state_history in e. rewrite Hh in e.
    now rewrite (spec_oracle_correct ((t,i,Resp rtyp) :: h)).
  Qed.
      
  Lemma emulator_correct :
    forall s h t i s' a',
      generated s h ->
      spec ((t,i,NoResp) :: h) ->
      emulator_act s t i = (s', a') ->
      (exists rtyp, a' = (t,i,Resp rtyp)) /\ spec (a' :: h).
  Proof.
    intros s h t i s' a' Hgen Hspec Hact.
    split.
    - eapply emulate_response_always_exists; eauto.
    - unfold emulator_act in Hact.
      destruct (md s); subst.
      unfold get_commute_response in Hact.
      
  Admitted.

  (* if we have a SIM-comm region of history, then the emulator produces a
   * conflict-free trace for the SIM-comm part of the history *)
  Lemma emulator_impl_conflict_free :
    forall sComm,
      Some sComm = trace_end_state (emulator_trace X_invocations start_state) ->
      trace_conflict_free (emulator_trace Y_invocations sComm).
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