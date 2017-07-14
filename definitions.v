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
  Hint Constructors reordered.

  Lemma swappable_sym : forall a1 a2, swappable a1 a2 -> swappable a2 a1.
  Proof.
    intros.
    destruct a1 as [[t i] r].
    destruct a2 as [[t2 i2] r2].
    unfold swappable in *; auto.
  Qed.

  Lemma reordered_nil : forall h, reordered h [] -> h = [].
  Proof.
    intros.
    remember [] as N in H.
    induction H; discriminate || auto.
  Qed.

  Lemma reordered_sym : forall h1 h2, reordered h1 h2 -> reordered h2 h1.
  Proof.
    intros.
    induction H; eauto.
    apply ro_perm_swap. apply swappable_sym; auto.
  Qed.

  Lemma reordered_unit : forall h a, reordered h [a] -> h = [a].
  Proof.
    intros.
    remember [a] as act.
    induction H; eauto.
    assert ([x] ++ t2 = x :: t2) as temp by now simpl. rewrite <- temp in *.
    destruct (app_eq_unit _ _ Heqact) as [Heq | Heq]; destruct_conjs; try discriminate.
    rewrite H1 in *.
    apply reordered_nil in H; rewrite H in *; rewrite app_nil_r; auto.
    inversion Heqact.
    rewrite (IHreordered2 Heqact) in IHreordered1. apply (IHreordered1 Heqact).
  Qed.

  Lemma reordered_app_head {t1 t2} l:
    reordered t1 t2 ->
    reordered (l++t1) (l++t2).
  Proof.
    induction l; auto; intros.
    rewrite <- app_comm_cons; apply ro_perm_skip; now apply IHl.
  Qed.
  
  Lemma reordered_prefix :
    forall h1 h2 h3 h4,
      reordered (h1 ++ h2) h4 -> reordered h2 h3 -> reordered (h1 ++ h3) h4.
  Proof.
    intros. generalize dependent h4. generalize dependent h1.
    induction H0; intros; simpl in *; auto.
    - pose (IHreordered (h1 ++ [x]) h4) as IHr.
      repeat rewrite <- app_assoc in *.
      assert (h1 ++ [x] ++ t1 = h1 ++ x :: t1) as tmp1 by now simpl.
      assert (h1 ++ [x] ++ t2 = h1 ++ x :: t2) as tmp2 by now simpl.
      rewrite tmp1, tmp2 in *.
      now apply IHr.
    - assert (reordered (h1 ++ a1 :: a2 :: t) (h1 ++ a2 :: a1 :: t)).
      apply reordered_app_head. apply ro_perm_swap. now apply swappable_sym.
      apply (ro_perm_trans _ _ _ H1 H0).    
  Qed.
  
  Lemma reordered_in : forall l l' x, reordered l l' -> List.In x l ->List.In x l'.
  Proof.
    intros l l' x Hperm; induction Hperm; simpl; tauto.
  Qed.
  
  Lemma reorder_length_eq : (forall h1 h2, reordered h1 h2 -> length h1 = length h2).
  Proof.    
    intros.
    induction H; subst; simpl in *; auto.
    rewrite IHreordered1, <- IHreordered2; auto.
  Qed.    

  Lemma reorder_unit_eq : (forall a b, reordered [a] [b] -> a = b).
  Proof.
    intros.
    assert (List.In a [b]).
    apply (reordered_in _ _ a H). apply in_eq.
    inversion H0; auto.
    apply in_inv in H0; destruct H0; try discriminate; subst; auto;
      inversion H0.
  Qed.

  Lemma history_of_thread_not_nil :
    forall t i r h,
      List.In (t,i,r) h -> history_of_thread h t <> [].
  Proof.
    intros. induction h. inversion H.
    apply in_inv in H; destruct H; subst.
    unfold history_of_thread; simpl. rewrite <- beq_nat_refl in *.
    intuition.
    eapply (nil_cons). symmetry in H; eauto.
    pose (IHh H).
    unfold history_of_thread. destruct a as [[t' i'] r']. simpl in *.
    Search (_ =? _ = false).
    destruct (Nat.eq_dec t' t) as [T | F]; subst;
      [rewrite <- beq_nat_refl | rewrite <- Nat.eqb_neq in *; rewrite F];
      fold history_of_thread; auto.
    intuition.
    eapply nil_cons; eauto.
  Qed.

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
  Definition start_mode := match X with | [] => Commute | _ => Replay end.
  Definition start_state : state :=
    mkState X (history_of_thread Y) [] (fun tid => []) [] start_mode.
                                        
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
  Function combine_tid_histories (histories : tid -> history) (t : tid) (acc : history) :=
    let newacc := (histories t) ++ acc in
    match t with
      | 0 => newacc
      | S t' => combine_tid_histories histories t' newacc
    end.
  Definition combined_histories (histories : tid -> history) :=
    combine_tid_histories histories num_threads [].
  Definition get_state_history (s : state) :=
    s.(postH) ++ combined_histories s.(commH) ++ s.(preH).
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
    | hd::tl => (mkState (rev tl) s.(Y_copy) (hd::s.(preH)) s.(commH) s.(postH) s.(md), hd)
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
      | Emulate => get_emulate_response (state_with_md s Emulate) t i
      | Commute => get_commute_response (state_with_md s Commute) t i
      | Replay => match rev (s.(X_copy)) with
                  | [hd] => get_replay_response (state_with_md s Commute) t i
                                                (* Changes mode to Commute *)
                  | _ => get_replay_response (state_with_md s Replay) t i
                  end
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
  Lemma next_mode_dec : forall s t i, {next_mode s t i = Commute}
                                      + {next_mode s t i = Emulate}
                                      + {next_mode s t i = Replay}.
  Proof.
    intros; destruct s; unfold next_mode in *; simpl in *; destruct md0.
    - destruct (rev (Y_copy0 t)). left. right. auto.
      destruct (action_invocation_eq a t i). left; left; auto.
      left; right; auto.
    - left; right; auto.
    - destruct (rev X_copy0).
      destruct (rev (Y_copy0 t)).
      left; right; auto.
      destruct (action_invocation_eq a t i). left; right; auto. 
      left; right; auto.
      destruct (action_invocation_eq a t i). right; auto. 
      left; right; auto.
  Qed.

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

  Lemma state_with_md_get_state_history :
    forall s mode,
      (get_state_history s = get_state_history (state_with_md s mode)).
  Proof.
    intros.
    destruct (state_with_md_comp_eq s (state_with_md s mode0) mode0); auto.
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
        reordered gencommH (combined_histories s.(commH)) /\
        s.(postH) ++ gencommH ++ s.(preH) = h.
  Admitted.
  
  Lemma rev_rev {A: Type} :
    forall l1 l2 : list A,
      rev l1 = rev l2 <-> l1 = l2.
  Proof.
    split; intros; generalize dependent l2;
    induction l1 using rev_ind; destruct l2 using rev_ind; intros;
    simpl in *; try rewrite rev_unit in *; try discriminate; auto;
    try rewrite rev_unit in H; try inversion H; subst.
    apply IHl1 in H2; subst; auto.
    destruct l2; simpl in *; discriminate.
    destruct l1; simpl in *; discriminate.
    inversion H1; subst. rewrite rev_unit; auto.
  Qed.

  Lemma rev_not_nil_or_unit : forall (x y : action) tl,
      exists x' y' tl', rev (x :: y :: tl) = x' :: y' :: tl'.
  Proof.
    intros.
    destruct (tl) using rev_ind; simpl in *.
    exists y; exists x; exists []; auto.
    rewrite rev_unit. destruct (rev l).
    exists x0; exists y; exists [x]; simpl in *; auto.
    exists x0; exists a; exists (l0 ++ [y] ++ [x]); simpl in *; auto.
    rewrite <- app_assoc, app_comm_cons in *; simpl in *; auto. 
  Qed.
  
  Lemma state_combined_histories_is_reordered_Y :
    forall s h,
      generated s h ->
      reordered (combined_histories s.(Y_copy) ++ combined_histories s.(commH)) Y.
  Proof.
  Admitted.
  
  Lemma reordered_Y_prefix_correct :
    forall h' h,
      reordered (h' ++ h) Y ->
      spec (h ++ X).
  Proof.
  Admitted.
    
  Lemma correct_state_correct_generated_history :
    forall s h,
      generated s h ->
      spec (get_state_history s) ->
      spec h.
  Proof.
    intros s h Hgen Hspec.
    destruct (generated_history_corresponds_state_history s h Hgen) as [gencommH [Horder Hh]].
    unfold get_state_history in *; simpl in *.
    pose (state_combined_histories_is_reordered_Y s h Hgen) as Hh'.
    pose (reordered_Y_prefix_correct (combined_histories s.(Y_copy))
                                     (combined_histories s.(commH)) Hh') as Hcomm.
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
      next_mode s t i = Commute ->
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
    end.

Section State_Lemmas.

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
      induction (Y_copy s t) using rev_ind; simpl in *;
      try rewrite rev_unit in *; try destruct (action_invocation_eq x t i); try discriminate.
      induction (xcpy); simpl in *; try rewrite rev_unit in *.
      destruct (rev (Y_copy s t)).
      discriminate.
      destruct (action_invocation_eq a t i); discriminate.
      remember (action_invocation_eq a t i) as Heq; destruct Heq; try discriminate.
      exists a. exists l. split; auto.
    Qed.

    Lemma next_mode_replay_implies_current_mode_replay :
      forall s t i h,
        generated s h ->
        next_mode s t i = Replay ->
        s.(md) = Replay.
    Proof.
      intros s t i h Hgen Hnext.
      induction Hgen.
      - unfold start_state in *; unfold start_mode in *; auto.
        destruct X; auto.
        unfold next_mode in *; simpl in *.
        destruct (rev (history_of_thread Y t));
          [|destruct (action_invocation_eq a t i)]; discriminate.
      - unfold emulator_act in H. destruct (next_mode s1 t0 i0).
        + unfold get_commute_response in H.
          destruct (rev (Y_copy (state_with_md s1 Commute) t0));
            inversion H; subst;
              unfold next_mode in Hnext; simpl in *.
          unfold state_with_md in *; simpl in *; auto.
          destruct (rev (Y_copy s1 t));
            [discriminate | destruct (action_invocation_eq a t i); simpl in *; discriminate].
          destruct (t =? t0). destruct (rev (rev l)). discriminate.
          destruct (action_invocation_eq a t i); simpl in *; discriminate.
          destruct (rev (Y_copy s1 t0));
            [discriminate | destruct (action_invocation_eq a t i); simpl in *; discriminate].
        + unfold get_emulate_response in H.
          functional induction (get_emulate_response_helper (state_with_md s1 Emulate) t0 i0 0
                                                          max_response_number);
          inversion H; subst; simpl in *; auto.
        + unfold get_replay_response in H. remember (X_copy s1) as s1xcpy.
          destruct (s1xcpy).
          destruct (rev (X_copy (state_with_md s1 Replay)));
            inversion H; auto.
          destruct h0.
          * destruct (rev (X_copy (state_with_md s1 Commute)));
              unfold next_mode in Hnext; inversion H; unfold state_with_md in *;
                subst; simpl in *.
            1-2: destruct (rev (Y_copy s1 t)); [|destruct (action_invocation_eq a0 t i)];
              discriminate.
          * destruct (rev_not_nil_or_unit a a0 h0) as [x [y [tl' Heq]]]; rewrite Heq in *.
            destruct (rev (X_copy (state_with_md s1 Replay))); inversion H; auto.
    Qed.
      
    Lemma current_mode_replay_implies_last_mode_replay :
      forall s s' t i h a,
        generated s h ->
        emulator_act s t i = (s', a) ->
        s'.(md) = Replay ->
        s.(md) = Replay.
    Proof.
      intros s s' t i h a Hgen Hact Hmd.
      unfold emulator_act in Hact.
      remember (next_mode s t i) as nextmd in Hact.
      destruct nextmd.
      - unfold get_commute_response in Hact.
        destruct (rev (Y_copy (state_with_md s Commute) t));
        inversion Hact; subst;
        unfold state_with_md in *; simpl in *; auto; discriminate.
      - unfold get_emulate_response in *.
        functional induction (get_emulate_response_helper
                                (state_with_md s Emulate) t i 0 max_response_number);
          unfold state_with_md in *; simpl in *;
          inversion Hact; subst; simpl in *; try discriminate.
        now apply IHp.
      - unfold get_replay_response in *; unfold next_mode in *; simpl in *; auto.
        remember (md s) as mds.
        destruct (mds); auto.
        destruct (rev (Y_copy s t)); try discriminate.
        destruct (action_invocation_eq a0 t i); discriminate.
    Qed.
      
    Lemma during_replay_state :
      forall s h,
        generated s h ->
        s.(md) = Replay ->
        s.(preH) = h /\
        s.(postH) = [] /\
        s.(commH) = (fun tid => []) /\
        s.(Y_copy) = (fun tid => history_of_thread Y tid) /\
        exists h', h' ++ h = X /\
                   s.(X_copy) = h'.
    Proof.
      intros s h Hgen Hmd. generalize dependent s.
      induction h; intros; inversion Hgen; subst; auto.
      - unfold start_state; simpl; repeat (split; auto).
        exists X; split; [apply app_nil_r | ]; auto.
      -  unfold emulator_act in H1.
         assert (next_mode s1 t i = Replay) as Hs1nextmd.
         {
           destruct (next_mode s1 t i); auto.
           - unfold get_commute_response in *; unfold state_with_md in *; simpl in *.
             destruct (rev (Y_copy s1 t)) in *; inversion H1; subst; discriminate.
           - unfold get_emulate_response in *.
             functional induction (get_emulate_response_helper
                                     (state_with_md s1 Emulate) t i 0 max_response_number);
               inversion H1; subst; try discriminate.
             now eapply IHp.
         }
         assert (s1.(md) = Replay) as Hs1md.
         {
          eapply next_mode_replay_implies_current_mode_replay; eauto.
         }
         
         pose (IHh s1 H4 Hs1md) as Hs1state; destruct Hs1state as
             [Hs1pre [Hs1post [Hs1comm [Hs1ycpy [h' [HX Hxcpys1]]]]]].
         
         destruct (replay_mode_state s1 t i) as [hd [tl [Hnil Heq]]]; auto.

         assert (X_copy (state_with_md s1 Commute) = X_copy s1) as Ht1 by
               now eapply state_with_md_comp_eq.
         assert (X_copy (state_with_md s1 Replay) = X_copy s1) as Ht2 by
             now eapply state_with_md_comp_eq.
         rewrite Hs1nextmd in *; unfold get_replay_response in *; rewrite Ht1, Ht2 in *;
           rewrite Hnil in H1.
         destruct tl; simpl in *; auto;
           inversion H1; subst; simpl in *; try discriminate; repeat (split; auto).
         exists (rev tl ++ [a]); split; auto.
         assert (rev tl ++ [a] ++ [(t,i,r)] = X_copy s1).
         assert (rev ((rev tl ++ [a]) ++ [(t,i,r)]) = (t,i,r) :: a :: tl) as tmp.
         {
           repeat rewrite (rev_unit). rewrite rev_involutive; auto.
         }
         assert ((rev ((rev tl ++ [a]) ++ [(t,i,r)])) = rev (X_copy s1)).
         {
           rewrite tmp in *; auto.
         }
         rewrite rev_rev in H; simpl in *; rewrite <- app_assoc in *; auto.
         rewrite <- H in HX. repeat rewrite <- app_assoc in *; simpl in *.
         apply HX.
    Qed.
    
    Lemma after_replay_state :
      forall s h t i,
        generated s h ->
        s.(md) = Replay ->
        next_mode s t i = Commute ->
        h = X /\
        s.(preH) = X /\
        s.(postH) = [] /\
        s.(commH) = (fun tid => []) /\
        s.(X_copy) = [] /\
        s.(Y_copy) = (fun tid => history_of_thread Y tid).
    Proof.
      intros s h t i Hgen Hm Hnextmd.
      pose Hnextmd as Hnextmd'.
      unfold next_mode in Hnextmd'.
      rewrite Hm in Hnextmd'.
      destruct (rev (X_copy s)), (rev (Y_copy s t)); try discriminate;
        try destruct (action_invocation_eq a t i); try discriminate.
    Qed.

    Lemma commute_mode_state :
      forall s t i,
        next_mode s t i = Commute ->
        exists hd tl, rev (Y_copy (state_with_md s Commute) t) = hd :: tl
                      /\ action_invocation_eq hd t i = true.
    Proof.
      intros. 
      unfold next_mode in *.
      remember (rev (Y_copy s t)) as ycpy.
      remember (rev (X_copy s)) as xcpy.
      destruct (md s); try discriminate.
      induction (ycpy); simpl in *; try rewrite rev_unit in *;
      try rewrite rev_unit in *; try destruct (action_invocation_eq x t i); try discriminate.
      remember (action_invocation_eq a t i) as Heq; destruct Heq; try discriminate.
      exists a. exists l. split; auto.
      destruct (xcpy), ycpy; simpl in *; 
      try rewrite rev_unit in *;
      try remember (action_invocation_eq a t i) as Heq; try destruct Heq; try discriminate.
    Qed.
    
    Lemma during_commute_state :
      forall s h,
        generated s h ->
        s.(md) = Commute ->
        reordered (combined_histories s.(Y_copy) ++ combined_histories s.(commH)) Y /\
        (exists gencomm, h = gencomm ++ X /\ reordered gencomm (combined_histories s.(commH))) /\
        s.(preH) = X /\
        s.(postH) = [] /\
        s.(X_copy) = [].
    Admitted.

End State_Lemmas.
  
Section Correctness.

    Lemma emulate_mode_preservation :
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
      intros s h t i s' rtyp Hgen Hspec Hnextmd Hact.
      assert (get_emulate_response (state_with_md s Emulate) t i = (s', (t,i,Resp rtyp))) as Hact'.
      auto.
      unfold get_emulate_response in Hact.
      functional induction (get_emulate_response_helper
                              (state_with_md s Emulate) t i 0 max_response_number).
      - assert (spec (get_state_history (state_with_md s Emulate))) as Hprefix.
        {
          rewrite <- (spec_oracle_correct
                        ((t,i,Resp rtyp0) :: get_state_history (state_with_md s Emulate))) in e.
          pose (spec_prefix_closed).
          apply (spec_prefix_closed
                   ((t, i, Resp rtyp0) :: get_state_history (state_with_md s Emulate))
                   (get_state_history (state_with_md s Emulate))
                   [(t,i,Resp rtyp0)]); auto.
        }
        assert (spec h).
        {
          eapply correct_state_correct_generated_history; eauto.
        }
        assert (generated s' ((t, i, Resp rtyp0) :: h)) as Hnewgen.
        {
          assert (emulator_act s t i = (s', (t,i,Resp rtyp))).
          unfold emulator_act in *. rewrite Hnextmd. apply Hact'.
          eapply GenCons; eauto.
          inversion Hact; subst; auto.
        }
        inversion Hact; subst; auto.
        eapply correct_state_correct_generated_history; eauto.
        assert ((t,i,Resp rtyp) :: get_state_history (state_with_md s Emulate) =
                get_state_history {|
              X_copy := X_copy s;
              Y_copy := Y_copy s;
              preH := preH s;
              commH := commH s;
              postH := (t, i, Resp rtyp) :: postH s;
              md := Emulate |}).
        unfold get_state_history in *; simpl in *. auto.
        rewrite H0 in e. apply spec_oracle_correct in e; auto.
      - rewrite (state_with_md_same_md_eq) in Hact; auto. inversion Hact.
      - now apply IHp in Hact.
    Qed.
  
  Lemma get_commute_response_correct :
    forall s h t i s' rtyp,
      generated s h ->
      spec ((t,i,NoResp)::h) ->
      next_mode s t i = Commute ->
      get_commute_response (state_with_md s Commute) t i = (s',(t,i,Resp rtyp)) ->
      spec ((t,i,Resp rtyp)::h).
  Proof.
    intros s h t i s' rtyp Hgen Hspec Hnextmd Hact.
    pose Hact as Hact'.
    unfold get_commute_response in Hact'.
    pose (commute_mode_state s t i) as Hstate; destruct Hstate as [hd [tl [Hnil Heq]]]; auto.
    rewrite Hnil in Hact'.
    unfold state_with_md in Hact'; subst; simpl in *.
    assert (s.(md) = Replay \/ s.(md) = Commute) as Hsmd.
    {
      unfold next_mode in *.
      destruct (md s); [right | discriminate | left]; auto.
    }
    assert (emulator_act s t i = (s', (t,i,Resp rtyp))) as Hemact.
    {
      unfold emulator_act. rewrite Hnextmd; auto.
    }
    assert (generated s' ((t,i,Resp rtyp) :: h)) as Hgens' by now eapply GenCons; eauto.
    assert (md s' = Commute) as Hmds' by now inversion Hact'; now subst.
    destruct Hsmd as [Hsmd | Hsmd];
      [pose (after_replay_state s h t i Hgen Hsmd Hnextmd) as Hstate | 
       pose (during_commute_state s h Hgen Hsmd) as Hstate];
      pose (reordered_Y_prefix_correct) as HY.

    (* Finished Replay *)
    - destruct Hstate as [HX [Hspre [Hspost [Hcomms [Hxcpys Hycpys]]]]].
      inversion Hact'.
      rewrite HX in *.
      pose (during_commute_state s' ((t,i,Resp rtyp) :: X) Hgens' Hmds') as Hstate.
      destruct Hstate as [Hreordered [[gencomm [Hrespeq Hgencommorder]] [HHistory rest]]].
      apply HY in Hreordered.
      assert (combined_histories (commH s') = [(t,i,Resp rtyp)]) as HcommH.
      {
        assert (gencomm = [(t,i,Resp rtyp)]) as Hrewrite.
        {
          assert ((t, i, Resp rtyp) :: X = [(t,i,Resp rtyp)] ++ X) as Hrewrite.
          simpl; auto.
          rewrite Hrewrite in *.
          now apply (app_inv_tail X [(t,i,Resp rtyp)] gencomm) in Hrespeq.
        }
        rewrite Hrewrite in *.
        apply reordered_sym in Hgencommorder.
        now apply reordered_unit in Hgencommorder.
      }
      now rewrite HcommH in *.
      
    (* During Commute *)
    - pose (during_commute_state s' _ Hgens' Hmds') as Hstates'.
      destruct Hstates' as [Hreordered [[gencomm [Hrespeq Hgencommorder]] [HHistory rest]]].
      apply reordered_sym in Hgencommorder.
      pose (reordered_prefix _ _ _ _ Hreordered Hgencommorder) as HYorder.
      apply HY in HYorder.
      now rewrite Hrespeq in *.
  Qed.

  Lemma get_replay_response_correct :
    forall s h t i s' rtyp mde,
      generated s h ->
      spec ((t,i,NoResp)::h) ->
      next_mode s t i = Replay ->
      get_replay_response (state_with_md s mde) t i = (s',(t,i,Resp rtyp)) ->
      spec ((t,i,Resp rtyp)::h).
  Proof.
    intros s h t i s' rtyp mde Hgen Hspec Hmd Hact.
    unfold get_replay_response in Hact.
    pose (replay_mode_state s t i) as Hstate; destruct Hstate as [hd [tl [Hnil Heq]]]; auto.
    assert (X_copy (state_with_md s Replay) = X_copy s) as Htmp by
          now eapply state_with_md_comp_eq.
    assert (X_copy (state_with_md s mde) = X_copy s) as Htmp' by
          now eapply state_with_md_comp_eq.
    rewrite Htmp, Htmp' in *.
    rewrite Hnil in Hact.
    unfold state_with_md in *; subst; simpl in *.
    assert (md s = Replay) as Hmds.
    {
      eapply next_mode_replay_implies_current_mode_replay; eauto.
    }
    destruct (during_replay_state s h Hgen Hmds) as
        [Hpres [Hposts [Hcomms [Hycpy [h' [HX Hxcpy]]]]]].
    assert (X = rev tl ++ hd :: h) as HX'.
    {
      rewrite <- Hxcpy in HX.
      assert (rev (hd :: tl) = rev (rev (X_copy s))) as temp.
      rewrite rev_rev. auto.
      rewrite rev_involutive in temp.
      rewrite <- temp in HX.
      simpl in *; rewrite <- app_assoc in HX. auto.
    }
    simpl_actions.
    eapply spec_prefix_closed. apply HspecX.
    rewrite H1 in HX'. apply HX'.
  Qed.


End Correctness.

Section SCR.

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
    - destruct (rev (X_copy s1)).
      destruct r; [eapply get_replay_response_correct; eauto | discriminate_noresp].
      destruct l; destruct r; try discriminate_noresp.
      all: eapply get_replay_response_correct; eauto.
  Qed.    

  Lemma mode_generated_replay :
    forall s h h' t i r,
      generated s h ->
      h' ++ (t,i,r) :: h = X ->
      s.(md) = Replay.
  Proof.
  Admitted.

  Lemma mode_generated_commute :
    forall s h Yend Yfront t i r,
      generated s h ->
      h = Yend ++ X ->
      reordered (Yfront ++ (t,i,r) :: Yend) Y ->
      s.(md) = Commute.
  Proof.
  Admitted.
        
  (* if we have a SIM-comm region of history, then the emulator produces a
   * conflict-free trace for the SIM-comm part of the history *)
  Lemma emulator_conflict_free :
    forall s s' h t i r,
      generated s (h ++ X) ->
      spec ((t,i,NoResp) :: h ++ X) ->
      (exists h', reordered (h' ++ (t,i,r) :: h) Y) ->
      emulator_act s t i = (s', (t,i,r)) ->
      conflict_free_step t s s'.
  Proof.
    intros s s' h t i r Hgen Hspec [h' Hreordered] Hact.
    unfold conflict_free_step.
    inversion Hgen; subst.

    (* we've generated [] so far *)
    - unfold start_state, start_mode in *; destruct X; simpl in *;
       unfold step_writes, write_tid_set in *; simpl in *;
         unfold emulator_act in Hact;
         unfold next_mode in *; subst; simpl in *.
      (* X = [] *)
      + rewrite app_nil_r in *; subst.
        assert (List.In (t,i,r) Y) as HinY.
        {
          apply (reordered_in _ _ (t,i,r) Hreordered).
          apply in_or_app.
          right; apply in_eq.
        }
        assert (history_of_thread Y t <> []) as Hist.
        {
          eapply history_of_thread_not_nil; eauto.
        }
        remember (history_of_thread Y t) as Yhist.
        destruct Yhist using rev_ind.
        intuition; discriminate.
        rewrite rev_unit in *.
        clear IHYhist.
        assert (exists h', history_of_thread Y t = h' ++ [(t,i,r)]) as HYhistEnd.
        {
          admit.
        }
        assert (action_invocation_eq x t i = true) as Heq.
        {
          destruct HYhistEnd as [bleh HYhistEnd].
          rewrite HYhistEnd in *; simpl in *.
          assert (rev (Yhist ++ [x]) = rev (bleh ++ [(t,i,r)])).
          rewrite HeqYhist; simpl in *; auto.
          repeat rewrite rev_unit in *. destruct x as [[t' [i']] r'].
          inversion H; subst; auto.
          unfold action_invocation_eq; simpl in *; repeat rewrite <- beq_nat_refl; auto.
        }
        rewrite Heq in *.
        unfold get_commute_response in *; unfold state_with_md in *; simpl in *.
        rewrite <- HeqYhist in *; try rewrite rev_unit in *.
        inversion Hact; subst; simpl in *; repeat (split; auto).
        admit.
      (* X = a :: h *)
      + pose (app_cons_not_nil h h0 a). contradiction.

    (* we've generated some history h so far *)
    - remember X as HX. destruct h; destruct HX; simpl in *.
      symmetry in H. pose (nil_cons H); discriminate.
      pose (after_replay_state).
      
  Admitted.

  Theorem scalable_commutativity_rule :
    (forall s h t i r,
       generated s h ->
       spec h /\
       (List.In (t,i,r) h -> exists rtyp, r = Resp rtyp)) /\
    (forall Y' n s s' h t i a',
       generated s (h ++ X) ->
       spec ((t,i,NoResp) :: h ++ X) ->
       h = skipn n Y' ->
       reordered Y' Y ->
       emulator_act s t i = (s', a') ->
       conflict_free_step t s s').
  Proof.
    intros; split. split; [eapply emulator_correct | eapply response_always_exists]; eauto.
    eapply emulator_conflict_free; eauto.
  Qed.
End SCR.