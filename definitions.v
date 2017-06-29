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
  Definition action_invocation_eq (a : action) (t : tid) (i : invocation) :=
    match a, i with
      | (tid, Inv i1, _), Inv i2 => (i1 =? i2) && (t =? tid)
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
  Parameter spec_responses: forall x h1 t i r h2,
                               spec ((x :: h1) ++ (t,i,r) :: h2) ->
                               r <> NoResp.
  Parameter spec_resp_exists : forall t i h,
                                  spec ((t,i,NoResp) :: h) ->
                                  exists rtyp, rtyp < max_response_number
                                               /\ spec ((t,i,Resp rtyp) :: h).
  Parameter spec_oracle : history -> bool.
  Parameter spec_oracle_correct :
    forall history, spec history <-> spec_oracle history = true.

  Parameter X : history.
  Parameter Y : history.
  Function get_invocations (h : history) (acc : list (tid * invocation)) :=
    match h with
      | [] => acc
      | (t,i,_) :: tl => get_invocations tl ((t,i) :: acc)
    end.
  Definition X_invocations := get_invocations X [].
  Definition Y_invocations := get_invocations Y [].
  Parameter X_and_Y_in_spec : spec (Y ++ X).
  Parameter X_and_Y_wf : forall t i r, List.In (t,i,r) (Y++X) ->
                                       exists rtyp, r = Resp rtyp.
  
  Record state := mkState { X_copy : history;
                            Y_copy : tid -> history;
                            preH : history;
                            commH : tid -> history;
                            postH : history;
                            md : mode
                          }.

  Definition start_state : state := mkState X (history_of_thread Y) [] (fun tid => []) [] Replay.

  Definition sim_commutes : Prop :=
    forall n h h' Y' Z,
      h = skipn n Y' ->
      reordered Y' Y ->
      reordered h' h ->
      spec (Z++h++X) ->
      spec (Z++h'++X).

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
  Definition combined_commH (s : state) := combine_tid_commH s num_threads [].
  Definition get_state_history (s : state) := s.(postH) ++ combined_commH s ++ s.(preH).
  Definition state_with_md (s : state) (md : mode) :=
    mkState s.(X_copy) s.(Y_copy) s.(preH) s.(commH) s.(postH) md.
             
  Function get_emulate_response_helper (s : state) (t: tid) (i : invocation)
           (rtyp : nat) (fuel : nat) : state * action :=
    let response_action := (t, i, Resp rtyp) in
    let state_history := get_state_history s in
    let new_history := response_action :: state_history in
    if spec_oracle (response_action :: state_history) then
      (mkState s.(X_copy) s.(Y_copy) s.(preH) s.(commH) (response_action :: s.(postH)) Emulate,
       (t, i, Resp rtyp))
    else match fuel with
           | 0 => (state_with_md s Emulate, (t, i, NoResp)) (* should never reach this *)
           | S n' => get_emulate_response_helper s t i (S rtyp) n'
         end.
  Definition get_emulate_response (s : state) (t: tid) (i : invocation) : state * action :=
    get_emulate_response_helper s t i 0 max_response_number.
  Definition get_commute_response (s : state) (t: tid) (i: invocation) : state * action :=
    match rev (s.(Y_copy) t) with
      | hd::tl => (mkState s.(X_copy)
                               (fun tid => if tid =? t then (rev tl)
                                           else s.(Y_copy) t)
                               s.(preH) (fun tid => if tid =? t then hd::(s.(commH) t)
                                                    else s.(commH) tid)
                                        s.(postH) Commute, hd)
      | _ => (s, (t,i,NoResp)) (* should never hit this *)
    end.
  Definition get_replay_response (s : state) (t: tid) (i : invocation) : state * action :=
    match rev s.(X_copy) with
      | hd::tl => (mkState (rev tl) s.(Y_copy) (hd::s.(preH)) s.(commH) s.(postH) Replay, hd)
      | _ => (s, (t,i,NoResp)) (* should never hit this *)
    end.
  Definition next_mode (s : state) (t: tid) (i: invocation) : mode :=
    match s.(md) with
      | Emulate => Emulate
      | Commute => match rev (s.(Y_copy) t) with
                     | [] => Emulate
                     | hd :: tl => if action_invocation_eq hd t i then Commute
                                   else Emulate
                   end
      | Replay => match rev s.(X_copy) with
                    | [] => Emulate
                    | hd :: tl => if action_invocation_eq hd t i then Replay
                                  else Emulate
                  end
    end.
  Definition emulator_act (s : state) (t: tid) (i : invocation) : (state * action) :=
    let mode := next_mode s t i in
    match mode with
      | Emulate => get_emulate_response (state_with_md s mode) t i
      | Commute => get_commute_response (state_with_md s mode) t i
      | Replay => get_replay_response (state_with_md s mode) t i
    end.

  Inductive generated : state -> history -> Prop := (* XXX: not sure about this *)
  | GenNil : generated start_state []
  | GenCons : forall s1 s2 t i r h,
                emulator_act s1 t i = (s2, (t,i,r)) ->
                spec ((t,i,NoResp) :: h) ->
                generated s1 h ->
                generated s2 ((t,i,r)::h).

End Emulator.
    Ltac unfold_action_inv_eq :=
    match goal with
      | [ HeqHacteq : true = action_invocation_eq (?t', Inv ?i', ?r') ?t (Inv ?i) |- _ ] =>
        assert (t = t' /\ i = i') as Heq; [
            unfold action_invocation_eq in HeqHacteq; symmetry in HeqHacteq;
            apply andb_prop in HeqHacteq; destruct HeqHacteq as [Heqi Heqt];
            now rewrite Nat.eqb_eq in Heqi, Heqt |
            destruct Heq as [Heqi Heqt]; rewrite Heqt, Heqi in *; auto];
        clear HeqHacteq 
      | [ HeqHacteq : false = action_invocation_eq (?t', Inv ?i', ?r') ?t (Inv ?i) |- _ ] =>
        assert (t <> t' \/ i' <> i) as Hneq; [
            unfold action_invocation_eq in HeqHacteq;
            symmetry in HeqHacteq;
            rewrite andb_false_iff in HeqHacteq; destruct HeqHacteq as [H|H];
            rewrite Nat.eqb_neq in H; [now right | now left]
          | destruct Hneq as [Hneqt | Hneqi]]
      | _ => idtac
    end.

    Ltac unfold_me :=
      try unfold emulator_act in *; try unfold next_mode in *;
      try unfold start_state in *; try unfold state_with_md in *; simpl in *.

Section Helpers.
  Lemma inv_of_action_eq : forall a t i r,
                             a = (t, i, r) ->
                             action_invocation_eq a t i = true.
  Proof.
    intros. unfold action_invocation_eq; subst. destruct i; repeat rewrite Nat.eqb_refl. auto. 
  Qed.

  Lemma state_with_md_has_md :
    forall s s' mode,
      s' = state_with_md s mode ->
      s'.(md) = mode.
  Proof.
    intros. unfold state_with_md in *. rewrite H in *; simpl; auto.
  Qed.

  Lemma state_with_md_comp_eq :
    forall s s' mode,
      s' = state_with_md s mode ->
      s'.(X_copy) = s.(X_copy) /\
      s'.(Y_copy) = s.(Y_copy) /\
      s'.(preH) = s.(preH) /\
      s'.(postH) = s.(postH) /\
      s'.(commH) = s.(commH).
  Proof.
    intros. unfold state_with_md in *; rewrite H; simpl; auto.
  Qed.

  Lemma state_with_md_same_md_eq :
    forall s mode,
      s.(md) = mode -> state_with_md s mode = s.
  Proof.
    intros. destruct s. unfold state_with_md; simpl in *. rewrite H. auto.
  Qed.

  Lemma generated_history_corresponds_state_history :
    forall s h,
      generated s h ->
      exists gencommH,
        reordered gencommH (combined_commH s) /\
        s.(postH) ++ gencommH ++ s.(preH) = h.
  Admitted.

  Lemma sim_commutative_prefix_in_spec :
    forall s h gencommH,
      generated s h->
      s.(postH) ++ gencommH ++ s.(preH) = h ->
      reordered gencommH (combined_commH s) ->
      spec h -> spec (s.(postH) ++ (combined_commH s) ++ s.(preH)).
  Admitted.

End Helpers.

Section Existance.
  Lemma generated_deterministic :
    forall s s' h,
      generated s h ->
      generated s' h ->
      s = s'.
  Proof.
  Admitted.
    
  Lemma emulator_deterministic :
    forall s1 s2 s2' t i a a',
      emulator_act s1 t i = (s2, a) ->
      emulator_act s1 t i = (s2', a') ->
      s2 = s2' /\ a = a'.
  Proof.
  Admitted.

  Lemma generated_commute_response_exists :
    forall s h t i,
      generated s h ->
      (*next_state s = Commute ->*)
      spec ((t,i,NoResp)::h) ->
      exists rtyp s',
        generated s' ((t,i,Resp rtyp)::h).
  Proof.
  Admitted.
  
  Lemma generated_response_exists :
    forall s h t i,
      generated s h ->
      spec ((t,i,NoResp)::h) ->
      exists rtyp s',
        generated s' ((t,i,Resp rtyp)::h).
  Proof.
    
  Admitted.

  Lemma response_always_exists :
    forall s h t i r,
      generated s h ->
      List.In (t,i,r) h ->
      exists rtyp, r = Resp rtyp.
  Proof.
    intros s h t i r Hgen Hin.
    pose Hgen as Hgen'.
    induction Hgen'.
    inversion Hin.
    assert (exists rtyp s', generated s' ((t0,i0,Resp rtyp)::h)) as Hgenexists. {
      eapply generated_response_exists; eauto.
    } destruct Hgenexists as [rtyp [s' Hgenexists]].
    inversion Hgenexists; subst.

    remember (action_invocation_eq (t,i,r) t0 i0) as Heq.
    destruct Heq, i, i0, r, r0; try destruct (Nat.eq_dec n1 n2); unfold_action_inv_eq;
    subst; inversion Hin; try inversion H1; try (now exists n2); try (now exists n1);
    try eapply IHHgen'; eauto.

    all : subst; rewrite (generated_deterministic s0 s1 h) in H5; auto.
    all : pose (emulator_deterministic s1 s' s2 t (Inv n) (t, Inv n, Resp rtyp) (t, Inv n, NoResp))
      as Heq; destruct Heq as [Hseq Haeq]; auto.
    all : inversion Haeq.
  Qed.

End Existance.

  Ltac discriminate_noresp :=
    match goal with
      | [ H : (_, (?t, ?i, NoResp)) = (_, ?a'),
              Hspec : spec ((?t, ?i, NoResp) :: ?h),
                      Hact : emulator_act ?s ?t ?i = (?s', ?a') |- _ ] =>
        let M := fresh "SO" in
        assert (exists rtyp, a' = (t, i, Resp rtyp)) as M; [
            now apply (response_always_exists s h t i s' a') |
            destruct M as [rtyp_new M] ; subst; discriminate ]
      | [ Hresp : _ = X |-
          exists _, (?t', Inv ?i', NoResp) = (?t', Inv ?i', Resp _) ] =>
        let M := fresh "SO" in pose (X_and_Y_wf t' (Inv i') NoResp) as M;
          assert (List.In (t', Inv i', NoResp) (Y++X)) as Hin; [
            rewrite <- Hresp; apply List.in_app_iff; right;
            apply List.in_app_iff; right; apply List.in_eq | ];
          apply M in Hin; destruct Hin as [rtyp Hin]; discriminate
      | [ Hgen : generated ?s2 ((?t,?i,NoResp)::?h) |- _] =>
          pose (response_always_exists s2 ((t,i,NoResp)::h) t i NoResp Hgen) as Hexists;
            assert (List.In (t, i, NoResp) ((t, i, NoResp) :: h)) as Hin; [ apply in_eq |];
            destruct (Hexists Hin) as [rtyp Ha]; inversion Ha; auto
    end.

  Ltac simpl_actions :=
    (* get rid of weird associativity and rev stuff *)
    repeat (match goal with
      | [ Hresp : (?h1 ++ ?x) ++ _ = X |- _ ] =>
        rewrite <- app_assoc in Hresp; try rewrite app_nil_r in Hresp; auto
      | [ H : context[rev (_ ++ [_]) ] |- _ ] => rewrite rev_unit in H
      | [ H : context[rev []] |- _ ] => simpl in *
      | _ => idtac
    end);
    (* pose "spec X" *)
    match goal with
      | [ _: spec X |- _ ] => idtac
      | _ => let HspecX := fresh "HspecX" in
             assert (spec X) as HspecX by
                   now eapply (spec_prefix_closed (Y++X) X Y X_and_Y_in_spec)
    end;
    (* factor out pair equalities *)
    match goal with
      | [ Hact' : (?s, ?a) = (?s', ?a') |- _ ] =>
        inversion Hact'; clear Hact'; simpl; auto
      | _ => idtac
    end;
    (* solve for prefix spec cases *)
    match goal with
      | [ Hresp : ?h1 ++ [(?t, ?i, ?r)] = X, HspecX : spec X |-
          spec [(?t, ?i, ?r)] ] =>
        eapply (spec_prefix_closed (h1 ++ [(t, i, r)]) ([(t,i,r)]) h1); eauto;
        rewrite <- Hresp in HspecX; auto
      | [ Hresp : ?h1 ++ [(?t, ?i, ?r)] ++ ?h2 = X, HspecX : spec X |-
          spec ((?t, ?i, ?r) :: ?h2) ] =>
        eapply (spec_prefix_closed (h1 ++ [(t, i, r)] ++ h2) ([(t,i,r)] ++ h2) h1); eauto;
        rewrite <- Hresp in HspecX; auto
      | _ => idtac
    end;
    (* solve for silly exists cases *)
    match goal with
      | [ H : (?t', Inv ?i', Resp ?n) = ?a' |- 
          exists _, (?t', Inv ?i', Resp ?n) = (?t', Inv ?i', Resp _)] =>
        exists n; auto
      | [ H : (?t', Inv ?i', NoResp) = ?a' |-
          exists _ : nat, (?t', Inv ?i', NoResp) = (?t', Inv ?i', Resp _)] =>
        discriminate_noresp
      | _ => idtac
    end;
  (* when we want to solve for emulate cases *)
    let M := fresh "H" in
    let IHp := fresh "IHp" in
    match goal with
      | [ Hact : get_emulate_response ?s ?t ?i = (?s', ?a) |- _ ] =>
        unfold get_emulate_response in Hact;
          functional induction (get_emulate_response_helper s t i 0 max_response_number)
          as [ | | IHp];
          inversion Hact as [M]; subst; simpl in *; try discriminate;
          try apply IHp in M; auto
      | _ => idtac
    end.

  
  Section Correctness.

    Lemma emulate_mode_retention :
      forall s t i s' a',
        s.(md) = Emulate ->
        emulator_act s t i = (s', a') ->
        s'.(md) = Emulate.
    Proof.
      intros.
      unfold_me. rewrite H in *.
      unfold get_emulate_response in *.
      functional induction (get_emulate_response_helper  {|
         X_copy := X_copy s;
         Y_copy := Y_copy s;
         preH := preH s;
         commH := commH s;
         postH := postH s;
         md := Emulate |} t i 0 max_response_number); eauto.
      inversion H0; auto.
      inversion H0; auto.
    Qed.

    Lemma get_emulate_response_correct :
      forall s h t i s' rtyp,
        generated s h ->
        spec ((t,i,NoResp)::h) ->
        next_mode s t i = Emulate ->
        get_emulate_response (state_with_md s Emulate) t i = (s',(t,i,Resp rtyp)) ->
        spec ((t,i,Resp rtyp)::h).
    Proof.
    Admitted.

    Lemma get_commute_response_correct :
      forall s h t i s' rtyp,
        generated s h ->
        spec ((t,i,NoResp)::h) ->
        next_mode s t i = Commute ->
        get_commute_response (state_with_md s Commute) t i = (s',(t,i,Resp rtyp)) ->
        spec ((t,i,Resp rtyp)::h).
    Proof.
    Admitted.

    Lemma replay_mode_state :
      forall s t i,
        next_mode s t i = Replay ->
        exists hd tl, rev (X_copy (state_with_md s Replay)) = hd :: tl
                      /\ action_invocation_eq hd t i = true.
    Proof.
      intros. 
      unfold next_mode in *.
      remember (rev (X_copy s)) as xcpy.
      destruct (md s); try discriminate.
      induction (Y_copy s t) using rev_ind; simpl in *; try rewrite rev_unit in *;
      try rewrite rev_unit in *; try destruct (action_invocation_eq x t i); try discriminate.
      induction (xcpy); simpl in *; try rewrite rev_unit in *.
      discriminate.
      remember (action_invocation_eq a t i) as Heq; destruct Heq; try discriminate.
      exists a. exists l. split; auto.
    Qed.
    
    Lemma get_replay_response_correct :
      forall s h t i s' rtyp,
        generated s h ->
        spec ((t,i,NoResp)::h) ->
        next_mode s t i = Replay ->
        get_replay_response (state_with_md s Replay) t i = (s',(t,i,Resp rtyp)) ->
        spec ((t,i,Resp rtyp)::h).
    Proof.
      intros s h t i s' rtyp Hgen Hspec Hmd Hact.
      unfold get_replay_response in Hact.
      pose (replay_mode_state s t i) as Hstate; destruct Hstate as [hd [tl [Hnil Heq]]]; auto.
      
    Admitted.

    Lemma next_mode_dec : forall s t i, {next_mode s t i = Commute}
                                        + {next_mode s t i = Emulate}
                                        + {next_mode s t i = Replay}.
    Proof.
    Admitted.

  Lemma emulator_correct :
    forall s h,
      generated s h ->
      spec h.
  Proof.
    intros s h Hgen. pose Hgen as Hgen'.
    induction Hgen'.
    apply spec_nonempty.
    pose H as Hact.
    unfold emulator_act in Hact.
    assert (generated s2 ((t,i,r)::h)). eapply GenCons; eauto.
    destruct (next_mode_dec s1 t i) as [[Hnextmd | Hnextmd] | Hnextmd];
    rewrite Hnextmd in Hact.
    - destruct r. eapply get_commute_response_correct; eauto.
      discriminate_noresp.
    - destruct r. eapply get_emulate_response_correct; eauto.
      discriminate_noresp.
    - destruct r. eapply get_replay_response_correct; eauto.
      discriminate_noresp.
   Qed.    
    
  (* if we have a SIM-comm region of history, then the emulator produces a
   * conflict-free trace for the SIM-comm part of the history *)
  Lemma emulator_conflict_free :
    forall Y' n s s' h t i a',
       generated s (h ++ X) ->
       spec ((t,i,NoResp) :: h ++ X) ->
       h = skipn n Y' ->
       reordered Y' Y ->
       emulator_act s t i = (s', a') ->
       conflict_free_step t s s'.
  Proof.
  Admitted.

  Theorem scalable_commutativity_rule :
    (forall s s' h t i a',
       generated s h ->
       spec ((t,i,NoResp) :: h) ->
       emulator_act s t i = (s', a') ->
       (exists rtyp, a' = (t,i,Resp rtyp)) /\ spec (a' :: h)) /\
    (forall Y' n s s' h t i a',
       generated s (h ++ X) ->
       spec ((t,i,NoResp) :: h ++ X) ->
       h = skipn n Y' ->
       reordered Y' Y ->
       emulator_act s t i = (s', a') ->
       conflict_free_step t s s').
  Proof.
    intros; split; [eapply emulator_correct | eapply emulator_conflict_free]; eauto.
  Qed.
End Lemmas.