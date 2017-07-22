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
Require Import model.

Section Histories.
  Definition IsHistories (histories: tid -> list action) : Prop :=
    forall t a, List.In a (histories t) -> thread_of_action a = t.

  Lemma combine_lt:
    forall histories t,
      IsHistories histories ->
      forall a n, t + n = thread_of_action a ->
           ~ List.In a (combine_tid_histories histories t).
  Proof.
    induction t; intros; simpl; auto.
    intros X.
    apply in_app_or in X.
    destruct X.
    apply H in H1.
    omega.
    replace (S t + n) with (t + (S n)) in H0; auto.
    eapply IHt in H0; eauto.
    omega.
  Qed.

  Lemma combine_tid_histories_parts:
    forall histories,
      IsHistories histories ->
      forall t maxt,
        t < maxt ->
        exists x y,
          combine_tid_histories histories maxt = x ++ histories t ++ y
          /\ (forall a, thread_of_action a = t -> (~ List.In a x /\ ~ List.In a y)).
  Proof.
    intros histories IsH t maxt; induction maxt; intros. omega.
    destruct (Nat.eq_dec t maxt).
    - exists [].
      exists (combine_tid_histories histories maxt).
      subst.
      clear H IHmaxt. split; split.
      apply in_nil. subst.
      eapply (combine_lt histories (thread_of_action a) IsH a 0) ; eauto.
    - assert (t < maxt) by omega.
      pose (IHmaxt H0) as tmp.
      destruct tmp as [xx [yy HH]].
      exists (histories maxt ++ xx), yy.
      destruct_conjs; simpl.
      rewrite <- app_assoc, <- H1.
      repeat (split; auto); pose (H2 a H3); destruct_conjs; auto.
      intro F. 
      apply in_app_or in F; 
      destruct F; [apply IsH in H6; omega | contradiction].
  Qed.
    
  Lemma history_of_thread_app_distributes :
    forall h h' t,
      history_of_thread (h ++ h') t = history_of_thread h t ++ history_of_thread h' t.
  Proof.
    induction h; intros.
    simpl in *; auto.
    destruct a as [[ta ia] ra].
    unfold history_of_thread in *. simpl in *. fold history_of_thread in *.
    repeat rewrite (IHh h' t).
    destruct (Nat.eq_dec ta t); subst;
      [rewrite Nat.eqb_refl in * | rewrite <- Nat.eqb_neq in *; rewrite n in *]; auto.
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

  Lemma history_of_thread_nil :
    forall h t, (forall a, thread_of_action a = t -> ~List.In a h) ->
             history_of_thread h t = [].
  Proof.
    induction h; intros; eauto.
    assert (thread_of_action a <> t).
    {
      remember (thread_of_action a) as ta.
      destruct (Nat.eq_dec ta t); subst; auto.
      intro F. pose (H a F). intuition.
    }
    simpl. rewrite <- Nat.eqb_neq in H0. rewrite H0. eapply IHh.
    intros a0 Heq; pose (H a0 Heq).
    intuition.
  Qed.

  Lemma history_of_thread_dummy :
    forall h t, (forall a, List.In a h -> thread_of_action a = t) ->
         history_of_thread h t = h.
  Proof.
    induction h; intros; auto.
    simpl.
    assert (thread_of_action a = t).
    {
      eapply H; eauto. apply in_eq.
    }
    rewrite <- Nat.eqb_eq in H0; rewrite H0.
    assert (history_of_thread h t = h).
    {
      eapply IHh; eauto. intros. eapply (H a0).
      apply in_cons. eauto.
    }
    rewrite H1; auto.
  Qed.
    
  Lemma history_of_thread_combined_is_application :
    forall (histories : tid -> history) t,
      IsHistories histories ->
      history_of_thread (combined_histories histories) t = histories t.
  Proof.
    intros.
    unfold combined_histories.
    destruct (tid_le_num_threads t) as [HG bleh].
    destruct (combine_tid_histories_parts histories H t num_threads HG) as
        [xx [yy [Heq Hin]]].
    rewrite Heq.
    repeat rewrite history_of_thread_app_distributes.
    assert (forall a : action, thread_of_action a = t -> ~ List.In a xx) as Hxx by
          now eapply Hin.
    assert (forall a : action, thread_of_action a = t -> ~ List.In a yy) as Hyy by
          now eapply Hin.
    rewrite (history_of_thread_nil xx t Hxx), (history_of_thread_nil yy t Hyy);
      rewrite app_nil_r in *; simpl.
    unfold IsHistories in *.
    eapply history_of_thread_dummy; eauto.
  Qed.

  Lemma history_of_thread_end :
    forall h t i r, exists h',
        (history_of_thread (h ++ [(t,i,r)]) t = h' ++ [(t,i,r)]).
  Proof.
    intros.
    induction h; simpl in *. rewrite Nat.eqb_refl. exists []; auto.
    destruct a as [[ta ia] ra]; simpl in *; auto.
    destruct (Nat.eq_dec ta t); subst; destruct IHh as [h' IHh]; rewrite IHh;
      [rewrite Nat.eqb_refl; exists ((t,ia,ra)::h') 
      | rewrite <- Nat.eqb_neq in *; rewrite n; exists h']; simpl in *; auto.
  Qed.

  Lemma history_of_thread_in_teq :
    forall h t t' i r, List.In (t',i,r) (history_of_thread h t) -> t' = t.
  Proof.
    induction h; intros; simpl in *; auto. omega.
    destruct a as [[ta [ia]] ra]; destruct i as [i]; destruct ra as [ra|];
      destruct r as [r|]; simpl in *;
    destruct (Nat.eq_dec ta t), (Nat.eq_dec ia i); try destruct (Nat.eq_dec r ra); subst;
      try rewrite Nat.eqb_refl in *; try rewrite <- Nat.eqb_neq in *; auto;
        try apply in_inv in H; try destruct H; try inversion H; try rewrite n in *; subst; auto;
          eapply IHh; eauto.
  Qed.
  
  Lemma history_of_thread_reordered_eq :
    forall h h' t,
      reordered h h' ->
      history_of_thread h' t = history_of_thread h t.
  Proof.
    unfold reordered in *; auto.
  Qed.

  Lemma reordered_sym : forall h1 h2, reordered h1 h2 -> reordered h2 h1.
  Proof.
    intros. unfold reordered in *. auto.
  Qed.

  Lemma reordered_prefix :
    forall h1 h2 h3 h4,
      reordered (h1 ++ h2) h4 -> reordered h2 h3 -> reordered (h1 ++ h3) h4.
  Proof.
    unfold reordered; intros.
    pose (H t).
    rewrite history_of_thread_app_distributes in *. now rewrite <- H0.
  Qed.

  Lemma in_history_of_thread :
    forall x h t,
      List.In x (history_of_thread h t) -> List.In x h.
  Proof.
    induction h; intros; auto.
    simpl in *.
    destruct (thread_of_action a =? t). inversion H; auto.
    right; eapply IHh; eauto.
    right; eapply IHh; eauto.
  Qed.
       
  Lemma reordered_in : forall l l' x, reordered l l' -> List.In x l ->List.In x l'.
  Proof.
    intros.
    unfold reordered in *.
    destruct x as [[tx ix] rx].
    pose (H tx).

    assert (List.In (tx,ix,rx) (history_of_thread l tx)).
    {
      apply in_split in H0.
      destruct H0 as [l1 [l2 H0]]; subst.
      rewrite history_of_thread_app_distributes; simpl.
      rewrite Nat.eqb_refl in *.
      apply in_or_app; right.
      apply in_eq.
    }
    rewrite e in H1.
    eapply in_history_of_thread; eauto.
  Qed.
  
  Lemma y_copy_state :
    forall s h,
      generated s h ->
      IsHistories s.(Y_copy).
  Proof.
    intros. induction H; subst; unfold IsHistories; intros.
    unfold start_state in *; simpl in *.
    destruct a as [[ta ia] ra].
    eapply history_of_thread_in_teq; eauto.

    unfold emulator_act in *.
    destruct (next_mode s1 t i).
    - unfold get_commute_response in *.
      unfold state_with_md in *; simpl in *.
      remember (Y_copy s1 t) as s1ycpy.
      destruct s1ycpy using rev_ind; simpl in *; inversion H; subst; simpl in *; auto.
      rewrite rev_unit in *. inversion H4; subst; simpl in *.
      clear IHs1ycpy.
      destruct (Nat.eq_dec t0 t); subst;
        [rewrite Nat.eqb_refl in *; rewrite rev_involutive in *
        |rewrite <- Nat.eqb_neq in *; rewrite n in *]; auto.
      eapply IHgenerated.
      rewrite <- Heqs1ycpy. apply in_or_app; left; auto.
    - unfold get_emulate_response in *.
      functional induction (get_emulate_response_helper
                              (state_with_md s1 Emulate) t i 0);
        inversion H; subst; auto.
    - destruct (rev (X_copy s1));
        unfold get_replay_response, state_with_md in *; simpl in *;
          [|destruct l];
          destruct (rev (X_copy s1)); inversion H; subst; auto.
  Qed.
  
  Lemma commH_state :
    forall s h,
      generated s h ->
      IsHistories s.(commH).
  Proof.
    intros. induction H; subst; unfold IsHistories; intros.
    unfold start_state in *; simpl in *. omega.
    unfold emulator_act in *.
    destruct (next_mode s1 t i).
    - unfold get_commute_response in *.
      unfold state_with_md in *; simpl in *.
      remember (Y_copy s1 t) as s1ycpy.
      destruct s1ycpy using rev_ind; simpl in *; inversion H; subst; simpl in *; auto.
      rewrite rev_unit in *. inversion H4; subst; simpl in *.
      clear IHs1ycpy.
      destruct (Nat.eq_dec t0 t); subst;
        [rewrite Nat.eqb_refl in *; rewrite rev_involutive in *
        |rewrite <- Nat.eqb_neq in *; rewrite n in *]; auto.
      apply in_inv in H2. destruct H2; [inversion H2; subst|]; auto.
    - unfold get_emulate_response in *.
      functional induction (get_emulate_response_helper
                              (state_with_md s1 Emulate) t i 0);
        inversion H; subst; auto.
    - destruct (rev (X_copy s1));
        unfold get_replay_response, state_with_md in *; simpl in *;
          [|destruct l];
          destruct (rev (X_copy s1)); inversion H; subst; auto.
  Qed.

  Hint Resolve y_copy_state commH_state.
  
  Lemma state_ycpy_nonempty :
    forall s h h1 h2 t i r gencomm,
      reordered (combined_histories (Y_copy s) ++ combined_histories (commH s)) Y ->
      reordered (h1 ++ [(t,i,r)] ++ h2 ++ gencomm) Y ->
      reordered gencomm (combined_histories (commH s)) ->
      generated s h ->
      Y_copy s t = (history_of_thread h1 t) ++ [(t,i,r)] ++ history_of_thread h2 t.
  Proof.
    unfold reordered.
    intros s h h1 h2 t i r gencomm Hr1 Hr2 Hr3 Hgen.
    pose (Hr1 t); pose (Hr2 t); pose (Hr3 t).
    repeat rewrite history_of_thread_app_distributes in *.
    do 2 rewrite history_of_thread_combined_is_application in *; eauto.
    rewrite e1 in *.
    rewrite <- e in *.
    replace (history_of_thread h1 t ++
                               history_of_thread [(t, i, r)] t ++ history_of_thread h2 t ++ commH s t)
    with ((history_of_thread h1 t ++ [(t, i, r)] ++ history_of_thread h2 t) ++ commH s t) in e0.
    eapply app_inv_tail; eauto.
    simpl in *. rewrite Nat.eqb_refl. simpl in *. rewrite <- app_assoc. auto.
  Qed.    

  Lemma history_of_thread_sublist :
    forall a t h,
      List.In a (history_of_thread h t) -> List.In a h.
  Proof.
    intros.
    induction h. simpl in *; auto.
    assert ({a = a0} + {a <> a0}) as ActEqDec.
    {
      destruct a as [[ta [ia]] ra]; destruct a0 as [[ta0 [ia0]] ra0].
      destruct (Nat.eq_dec ta ta0), (Nat.eq_dec ia ia0), ra as [ra|], ra0 as [ra0|];
        try destruct (Nat.eq_dec ra ra0); subst;
          try (left; auto; fail); try (right; intuition; inversion H0; auto).
    }
    destruct ActEqDec; subst.
    apply in_eq. apply in_cons.
    assert ((a0 :: h) = [a0] ++ h) as tmp by now simpl. rewrite tmp in *.
    rewrite history_of_thread_app_distributes in *.
    destruct a0 as [[t0 i0] r0].
    destruct (Nat.eq_dec t0 t); subst; unfold history_of_thread; simpl in *;
      [rewrite Nat.eqb_refl in * | rewrite <- Nat.eqb_neq in *; rewrite n0 in *].

    apply in_app_or in H; destruct H.
    inversion H. rewrite H0 in *; intuition. inversion H0.
    eapply IHh; eauto.

    rewrite app_nil_l in *. eapply IHh; eauto.
  Qed.

End Histories.

Section Misc.
  Hint Resolve commH_state y_copy_state.
  
  Lemma next_mode_dec : forall s t i, {next_mode s t i = Commute}
                                      + {next_mode s t i = Emulate}
                                      + {next_mode s t i = Replay}.
  Proof.
    intros; destruct s; unfold next_mode in *; simpl in *; destruct md.
    - destruct (rev (Y_copy t)). left. right. auto.
      destruct (action_invocation_eq a t i). left; left; auto.
      left; right; auto.
    - left; right; auto.
    - destruct (rev X_copy).
      destruct (rev (Y_copy t)).
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
    destruct (state_with_md_comp_eq s (state_with_md s mode) mode); auto.
  Qed.
    
  Lemma state_with_md_same_md_eq :
    forall s mode,
      s.(md) = mode -> state_with_md s mode = s.
  Proof.
    intros. destruct s. unfold state_with_md; simpl in *. rewrite H. auto.
  Qed.
  
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

  Lemma combine_tid_histories_nil :
    combine_tid_histories (fun _ : tid => []) num_threads = nil.
  Proof.
    functional induction (combine_tid_histories (fun _ : tid => []) num_threads); auto.
  Qed.

  Lemma in_history_iff_in_thread_history :
    forall h a, List.In a h <-> exists t, List.In a (history_of_thread h t).
  Proof.
    intros; split.
    - destruct a as [[tt ti] tr].
      exists tt.
      destruct (in_split _ h H) as [l1 [l2 Hin]].
      rewrite Hin.
      rewrite history_of_thread_app_distributes; apply in_or_app.
      right. simpl. rewrite Nat.eqb_refl. apply in_eq.
    - intros. destruct H as [t Hin].
      induction h. simpl in *; inversion Hin; subst; eauto.
      simpl in *.
      destruct a as [[t1 [i1]] r1]. destruct a0 as [[t2 [i2]] r2].
      destruct (Nat.eq_dec t1 t2), (Nat.eq_dec i1 i2), r1, r2;
        try destruct (Nat.eq_dec r r0); subst;
        try (left; auto; fail); right; simpl in *;
          try rewrite Nat.eq_refl in *;
          destruct (t2 =? t);
          try (apply in_inv in Hin; destruct Hin;
               [inversion H; symmetry in H1; contradiction | auto]);
          try apply (IHh Hin).
  Qed.
        
  Lemma history_of_thread_all_nil :
    forall h, (forall t, history_of_thread h t = []) -> h = [].
  Proof.
    intros.
    destruct h. auto.
    assert (List.In a (a::h)) as Hin by now apply in_eq.
    apply (in_history_iff_in_thread_history (a :: h) a) in Hin. destruct Hin as [t Htin].
    rewrite (H t) in *. inversion Htin.
  Qed.

  Lemma history_of_thread_reapp :
    forall h t,
      history_of_thread (history_of_thread h t) t = history_of_thread h t.
  Proof.
    induction h; intros.
    simpl in *; auto.
    remember (thread_of_action a =? t) as ta.
    destruct (ta); simpl; rewrite <- Heqta; auto.
    simpl; rewrite <- Heqta.
    rewrite (IHh t); auto.
  Qed.    
    
  Lemma state_combined_histories_is_reordered_Y :
    forall h s,
      generated s h ->
      reordered (combined_histories s.(Y_copy) ++ combined_histories s.(commH)) Y.
  Proof.
    induction h; intros; inversion H; subst.
    - unfold start_state in *; simpl in *.
      unfold reordered; intros.
      rewrite history_of_thread_app_distributes.
      rewrite history_of_thread_combined_is_application in *.
      rewrite history_of_thread_combined_is_application in *.
      rewrite app_nil_r in *; eauto.
      all: unfold IsHistories; intros. inversion H0.
      destruct a as [[ta ia] ra]; simpl in *.
      eapply history_of_thread_in_teq; eauto.
    - pose (IHh s1 H5).
      unfold emulator_act in *.
      destruct (next_mode s1 t i) in *; unfold state_with_md in *; simpl in *.
      + unfold get_commute_response in *; simpl in *.
        remember (Y_copy s1 t) as s1ycpy.
        destruct s1ycpy using rev_ind; try rewrite rev_unit in *; simpl in *;
          inversion H2; subst; simpl in *; auto. clear IHs1ycpy.
        unfold reordered in *; intros.
        pose (r0 t0).
        rewrite history_of_thread_app_distributes in *.
        do 2 rewrite history_of_thread_combined_is_application in *;
          try rewrite rev_involutive.
        destruct (Nat.eq_dec t0 t); subst;
          [rewrite Nat.eqb_refl in * | rewrite <- Nat.eqb_neq in *; rewrite n in *]; auto.
        rewrite <- Heqs1ycpy in e. rewrite <- e. rewrite <- app_assoc. now simpl; auto.
        all: eauto; unfold IsHistories; intros;
          pose (commH_state s1 _ H5);
          pose (y_copy_state s1 _ H5);
          unfold IsHistories in *.          
        all: destruct (Nat.eq_dec t1 t); subst;
            [rewrite Nat.eqb_refl in * | rewrite <- Nat.eqb_neq in *; rewrite n in *]; auto.
          inversion H0; subst. now simpl.
          eapply i0; eauto.
          eapply i1; eauto.
          rewrite <- Heqs1ycpy. apply in_or_app; left; auto.
      + unfold get_emulate_response in *.
        functional induction (get_emulate_response_helper
         {|
         X_copy := X_copy s1;
         Y_copy := Y_copy s1;
         preH := preH s1;
         commH := commH s1;
         postH := postH s1;
         md := Emulate |} t i 0); inversion H2; subst; simpl in *; auto.
      + remember (rev (X_copy s1)) as rxcpys1.
        destruct (rxcpys1); unfold get_replay_response in *; simpl in *; inversion H2; subst; auto.
        rewrite <- Heqrxcpys1 in *.
        1,2: inversion H1; subst; simpl in *; auto.
        rewrite <- Heqrxcpys1 in *. destruct l; inversion H3; subst; simpl in *; auto.
  Qed.
  
  Lemma reordered_Y_prefix_correct :
    forall h h',
      reordered (h' ++ h) Y ->
      spec (h ++ X).
  Proof.
    induction h; simpl in *; intros.
    - pose (X_and_Y_in_spec); eapply (spec_prefix_closed); eauto.
    - assert (reordered ((h' ++ [a]) ++ h) Y).
      rewrite <- app_assoc. simpl in *. auto.
      assert (spec (Y++X)) by apply X_and_Y_in_spec.
      assert (spec ((h' ++ a :: h) ++ X)).
      pose (sim_commutes [] Y (h' ++ a :: h) []).
      unfold reordered in *; simpl in *. eapply s; eauto.
      replace ((h' ++ a :: h) ++ X) with (h' ++ a :: h ++ X) in H2; simpl; auto.
      eapply spec_prefix_closed; eauto.
      rewrite <- app_assoc. simpl. auto.
  Qed.

End Misc.


Section State_Lemmas.
  
  Hint Resolve y_copy_state commH_state.
  
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
          destruct (rev (Y_copy s1 t));
            [discriminate | destruct (action_invocation_eq a t i); simpl in *; discriminate].
        + unfold get_emulate_response in H.
          functional induction (get_emulate_response_helper (state_with_md s1 Emulate) t0 i0 0);
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
                                (state_with_md s Emulate) t i 0);
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
                                     (state_with_md s1 Emulate) t i 0);
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
    Proof.
      intros s h Hgen Hmd. revert dependent s.
      induction h; intros; inversion Hgen; subst; simpl in *.
      - unfold start_state in *; unfold start_mode in *; simpl in *.
        remember X as HX; destruct HX; try discriminate.
        pose (state_combined_histories_is_reordered_Y _ _  Hgen); simpl in *.
        repeat split; auto.
        exists []; simpl in *; repeat split; auto.
        unfold combined_histories.
        functional induction (combine_tid_histories (fun _ : tid => []) num_threads).
        unfold reordered; simpl in *. auto.
        eapply IHl0; eauto.

      - assert (md s1 = Replay \/ md s1 = Commute) as Hmds1.
        {
          unfold emulator_act in H1.
          remember (next_mode s1 t i) as s1nmd. destruct s1nmd;
          unfold next_mode in *; remember (md s1) as s1md; destruct s1md; try discriminate.
          destruct (rev (Y_copy s1 t)); try discriminate.
          destruct (action_invocation_eq a t i); try discriminate.
          now right. now left. now right.
          unfold get_emulate_response in *.
          functional induction (get_emulate_response_helper
                                  (state_with_md s1 Emulate) t i 0);
            inversion H1; subst; simpl in *; try discriminate.
          eapply IHp; eauto.
          now left. now right. now left.
        } destruct Hmds1 as [Hmds1 | Hmds1].
        + pose (during_replay_state _ _ H4 Hmds1); destruct_conjs; subst; simpl in *.
          remember (preH s1) as pres1.
          destruct (pres1); simpl in *; inversion H4; subst.

          * unfold start_state in *; unfold start_mode in *;
              remember X as HX; destruct HX using rev_ind; try clear IHHX; try discriminate;
                simpl in *; auto.
            assert (exists hd tl, HX ++ [x] = hd :: tl) as bleh.
            {
              assert (HX ++ [x] <> []).
              intuition; simpl in *. apply app_eq_nil in H.
              destruct_conjs; discriminate.
              destruct (HX++[x]); try discriminate; intuition. exists a. exists l. auto.
            } destruct bleh as [hd [tl bleh]]; rewrite bleh in *. rewrite <- bleh in *.
            unfold emulator_act in *. unfold next_mode in *; simpl in *.
            rewrite rev_unit in *; simpl in *.
            assert (action_invocation_eq x t i = true) as Hacteq.
            {
              remember (action_invocation_eq x t i) as Hacteq.
              destruct Hacteq; auto. 
              unfold get_emulate_response, state_with_md in *; simpl in *.
              functional induction (get_emulate_response_helper
                                      {|
                                        X_copy := HX ++ [x];
                                        Y_copy := history_of_thread Y;
                                        preH := [];
                                        commH := fun _ : tid => [];
                                        postH := [];
                                        md := Emulate |} t i 0);
                inversion H1; subst; try discriminate.
              now eapply IHp.
            }
            rewrite Hacteq in *.
            destruct HX using rev_ind; [simpl in *|rewrite rev_unit in *];
              unfold get_replay_response, state_with_md in *; simpl in *;
                inversion H1; subst; simpl in *.
            repeat (split; auto).
            eapply (state_combined_histories_is_reordered_Y _ _  Hgen); simpl in *.
            exists []; simpl in *; repeat split; auto.
            unfold combined_histories.
            functional induction (combine_tid_histories (fun _ : tid => []) num_threads).
            unfold reordered; simpl in *; auto.
            eapply IHl0; eauto.

            rewrite rev_unit in *. inversion H6; subst; try discriminate.

          * assert (exists t i r, X_copy s1 = [(t,i,r)]) as s1xcpy.
            {
              unfold emulator_act in *.
              remember (next_mode s1 t i) as s1nmd.
              destruct s1nmd;
                unfold next_mode in *; remember (md s1) as s1md; destruct s1md; try discriminate.
              destruct (rev (X_copy s1)); try discriminate. destruct (action_invocation_eq a t i);
                                                              discriminate.
              unfold get_emulate_response, state_with_md in *; simpl in *. clear H8.
              functional induction (get_emulate_response_helper
                                      {|
                                        X_copy := X_copy s1;
                                        Y_copy := Y_copy s1;
                                        preH := preH s1;
                                        commH := commH s1;
                                        postH := postH s1;
                                        md := Emulate |} t i 0);
                inversion H1; subst; try discriminate.
              now eapply IHp.

              remember (X_copy s1) as s1xcpy. destruct s1xcpy using rev_ind; simpl in *;
                                                try discriminate.
              rewrite rev_unit in *. destruct s1xcpy using rev_ind; simpl in *.
              destruct x as [[tx ix] rx]; exists tx; exists ix; exists rx; auto.
              rewrite rev_unit in *; unfold get_replay_response in *.
              destruct (rev (X_copy (state_with_md s1 Replay)));
                inversion H1; unfold state_with_md in *; simpl in *; subst; discriminate.
            } destruct s1xcpy as [ts1 [is1 [rs1 Hs1xcpy]]].
            unfold emulator_act, next_mode in H1.
            rewrite Hmds1 in *. rewrite Hs1xcpy in *; simpl in *.
            destruct is1 as [is1]; destruct i as [i].
            assert ((is1 =? i) && (t =? ts1) = true).
            {
              destruct (Nat.eq_dec is1 i), (Nat.eq_dec t ts1); subst;
                repeat try rewrite Nat.eqb_refl in *; try rewrite <- Nat.eqb_neq in *;
                  try rewrite n in *; try rewrite n0 in *; simpl in *; auto.
              all: unfold get_emulate_response in *.
              1,3: functional induction (get_emulate_response_helper
                                        (state_with_md s1 Emulate) t (Inv i) 0);
                inversion H1; subst; unfold state_with_md in *; simpl in *; try discriminate;
                  try now eapply IHp.
              functional induction (get_emulate_response_helper
                                        (state_with_md s1 Emulate) ts1 (Inv i) 0);
                inversion H1; subst; unfold state_with_md in *; simpl in *; try discriminate;
                  try now eapply IHp.
            }
            rewrite H in *.
            unfold get_replay_response, state_with_md in *; simpl in *.
            rewrite Hs1xcpy in *; simpl in *. inversion H1; subst; simpl in *; auto.
            repeat (split; auto).
            eapply (state_combined_histories_is_reordered_Y _ _  Hgen); simpl in *.
            exists []; simpl in *; repeat split; auto.
            unfold combined_histories. rewrite H2 in *.
            functional induction (combine_tid_histories (fun _ : tid => []) num_threads).
            unfold reordered; simpl in *; auto.
            eapply IHl0; eauto.
            rewrite <- Heqpres1; auto.

        + pose (IHh s1 H4 Hmds1); destruct_conjs.
          unfold emulator_act in *. unfold next_mode in *.
          rewrite Hmds1 in H1.
          remember (Y_copy s1 t) as s1ycpy.
          destruct s1ycpy using rev_ind; simpl in *; try rewrite rev_unit in *;
            [| destruct (action_invocation_eq x t i)].
          
          1,3: unfold get_emulate_response in *;
            functional induction (get_emulate_response_helper
                                    (state_with_md s1 Emulate) t i 0);
            inversion H1; subst; unfold state_with_md in *; simpl in *; try discriminate;
              try now eapply IHp.

          clear IHs1ycpy.
          unfold get_commute_response, state_with_md in *; simpl in *.
          rewrite <- Heqs1ycpy, rev_unit in *.
          inversion H1; subst; simpl in *.
          repeat (split; auto).
          eapply (state_combined_histories_is_reordered_Y _ _ Hgen); simpl in *; eauto.
          exists ((t,i,r) :: H0); split; auto.
          unfold reordered in *; intros.
          rewrite history_of_thread_combined_is_application in *; eauto.
          simpl in *.
          destruct (Nat.eq_dec t t0); subst;
            [rewrite Nat.eqb_refl in * | rewrite <- Nat.eqb_neq in *; rewrite n in *];
            pose (H8 t0); rewrite history_of_thread_combined_is_application in *; eauto.
          rewrite e; eauto.
          rewrite Nat.eqb_sym in n.
          rewrite n in *; auto.
          pose (commH_state s1 _ H4).
          unfold IsHistories in *; intros; simpl in *; auto.
          destruct (Nat.eq_dec t1 t); subst;
            [rewrite Nat.eqb_refl in * | rewrite <- Nat.eqb_neq in *; rewrite n in *].
          inversion H7; subst; auto.
          eapply i0; eauto.
    Qed.

  Lemma not_emulate_postH_nil :
    forall h s,
      generated s h ->
      s.(md) <> Emulate ->
      s.(postH) = [].
    Proof.
      induction h; intros; inversion H; subst.
      unfold start_state in *; simpl in *; auto.
      assert (s1.(md) <> Emulate).
      {
        unfold emulator_act in *.
        unfold next_mode in *.
        remember (md s1) as mds1. destruct mds1; subst; try discriminate.
        unfold get_emulate_response in *.
        functional induction (get_emulate_response_helper
                                (state_with_md s1 Emulate) t i 0);
          inversion H3; subst; auto.
      }
      pose (IHh s1 H6 H1).
      unfold emulator_act in *.
      assert (next_mode s1 t i <> Emulate).
      {
        unfold emulator_act in *.
        remember (next_mode s1 t i) as mds1. destruct mds1; subst; try discriminate.
        unfold get_emulate_response in *.
        functional induction (get_emulate_response_helper
                                (state_with_md s1 Emulate) t i 0);
          inversion H3; subst; auto.
      }
      remember (next_mode s1 t i) as s1nextmd.
      destruct s1nextmd; intuition.
      unfold get_commute_response, state_with_md in *; simpl in *.
      destruct (rev (Y_copy s1 t)); inversion H3; subst; auto.
      remember (rev (X_copy s1)) as xcpy.
      destruct xcpy; unfold get_replay_response, state_with_md in *;
        simpl in *. rewrite <- Heqxcpy in *; simpl in *; inversion H3; subst; auto.
      destruct xcpy; rewrite <- Heqxcpy in *; simpl in *; inversion H3; subst; auto.
    Qed.
    
  Lemma emulate_response_state :
    forall h s t i s' a,
      generated s h ->
      spec ((t,i,NoResp) :: h) ->
      get_emulate_response (state_with_md s Emulate) t i = (s', a) ->
      s.(commH) = s'.(commH) /\ s'.(postH) = a :: s.(postH) /\ s'.(preH) = s.(preH).
  Proof.
    intros.
    unfold get_emulate_response in *; simpl in *.
    functional induction (get_emulate_response_helper (state_with_md s Emulate)
                                                      t i 0);
      unfold state_with_md in *; simpl in *;
        inversion H1; subst; auto.
  Qed.

  Lemma replay_response_state :
    forall h s t i,
      generated s h ->
      spec ((t,i,NoResp) :: h) ->
      next_mode s t i = Replay ->
      s.(postH) = start_state.(postH)
      /\ s.(commH) = start_state.(commH).
  Proof.
    induction h; intros; inversion H; subst; simpl in *; auto.
    remember (next_mode s1 t0 i0) as s1nmd.
    assert (next_mode s1 t0 i0 = Replay).
    {
      destruct s1nmd; unfold emulator_act in H4; rewrite <- Heqs1nmd in *; auto.
      - unfold get_commute_response, state_with_md in *; simpl in *.
        destruct (rev (Y_copy s1 t0)); inversion H4; subst; simpl in *; auto.
        all: unfold next_mode in H1; simpl in *.
        destruct (rev (Y_copy s1 t)); [|destruct (action_invocation_eq a t i)]; discriminate.
        destruct (t =? t0); destruct (rev (rev l)). discriminate.
        destruct (action_invocation_eq a t i); discriminate.
        destruct (rev (Y_copy s1 t)); [|destruct (action_invocation_eq a t i)]; discriminate.
        destruct (rev (Y_copy s1 t)); [|destruct (action_invocation_eq a0 t i)]; discriminate.
      - unfold get_emulate_response in *.
        functional induction (get_emulate_response_helper (state_with_md s1 Emulate)
                                                          t0 i0 0);
          unfold next_mode in H1; inversion H4; subst; simpl in *; auto.
    }
    
    assert (postH s1 = [] /\ commH s1 = (fun _ : tid => [])).
    {
      eapply IHh; eauto. 
    }
    unfold emulator_act in *.
    rewrite H2 in *.
    remember (rev (X_copy s1)) as xcpyrev.
    destruct xcpyrev; unfold get_replay_response, state_with_md in *; simpl in *.
    rewrite <- Heqxcpyrev in *. inversion H4; subst; auto.
    destruct xcpyrev. rewrite <- Heqxcpyrev in *. inversion H4; subst; auto.
    rewrite <- Heqxcpyrev in *; inversion H4; subst; auto.
  Qed.

  Lemma generated_history_corresponds_state_history :
    forall h s,
      generated s h ->
      exists gencommH,
        reordered gencommH (combined_histories s.(commH)) /\
        s.(postH) ++ gencommH ++ s.(preH) = h.
  Proof.
    induction h; intros; inversion H; subst.
    - unfold start_state in *; simpl in *.
      exists []; split; auto. unfold combined_histories; auto.
      functional induction (combine_tid_histories (fun _ : tid => []) num_threads); auto.
      constructor.
    - pose (IHh s1 H5) as IHs1; destruct IHs1 as [gencomm IHs1]; destruct_conjs.
      unfold emulator_act in *.
      remember (next_mode s1 t i) as s1nmd.
      destruct (s1nmd); unfold state_with_md in *; simpl in *.
      + unfold get_commute_response in *; simpl in *.
        remember (Y_copy s1 t) as s1ycpy.
        destruct (s1ycpy) using rev_ind. inversion H2; subst; simpl in *; auto.
        * unfold next_mode in *; simpl in *.
          destruct (md s1); try discriminate. rewrite <- Heqs1ycpy in *; simpl in *; discriminate.
          destruct (rev (X_copy s1)); [|destruct (action_invocation_eq a t i)]; discriminate.
        * clear IHh0. 
          rewrite rev_unit in *; inversion H2; subst;
            unfold reordered in *; simpl in *; destruct_conjs.
          exists ((t,i,r) :: gencomm); split; intros.
          -- pose (H0 t). pose (H0 t0).
             rewrite history_of_thread_combined_is_application in *; eauto.
             destruct (Nat.eq_dec t0 t); subst; simpl in *;
               [rewrite Nat.eqb_refl in *| rewrite <- Nat.eqb_neq in *; rewrite n in *].
             now rewrite e.
             rewrite Nat.eqb_sym in n. rewrite n. auto.

             pose (commH_state _ _ H5).
             unfold IsHistories in *; intros.
             destruct (Nat.eq_dec t1 t); subst; simpl in *;
               [rewrite Nat.eqb_refl in *| rewrite <- Nat.eqb_neq in *; rewrite n in *].
             inversion H1; subst; auto. eapply i0; eauto.
          -- assert (postH s1 = []).
             eapply not_emulate_postH_nil; eauto.
             unfold next_mode in Heqs1nmd.
             remember (md s1) as s1md. destruct s1md; try discriminate.
             rewrite H1 in *; simpl in *; auto.
      + exists gencomm.
        split; auto.
        -- assert (commH s1 = commH s). eapply emulate_response_state; eauto.
           rewrite <- H3. auto.
        -- assert (postH s = (t,i,r) :: postH s1 /\ preH s = preH s1).
           eapply emulate_response_state; eauto.
           destruct_conjs; subst.
           rewrite H3, H6; simpl in *; auto.
      + exists gencomm.
        assert (commH s1 = commH s /\ postH s1 = postH s).
        {
           remember (rev (X_copy s1)) as rxcpy.
           destruct rxcpy; unfold get_replay_response in *; simpl in *.
           rewrite <- Heqrxcpy in *; simpl in *.
           inversion H2; subst; auto.
           destruct rxcpy; try rewrite <- Heqrxcpy in *; simpl in *;
             inversion H2; subst; auto.
        } destruct_conjs.
        split.
        -- now rewrite <- H3. 
        -- assert (postH s1 = [] /\ (commH s1 = (fun _ : tid => []))).
           {
             pose replay_response_state.
             unfold start_state in *; simpl in *.
             eapply a; eauto.
           } destruct_conjs.
           rewrite H8 in H0. unfold reordered in *.
           assert (combined_histories (fun _ : tid => []) = []).
           unfold combined_histories.
           functional induction ( combine_tid_histories (fun _ : tid => []) num_threads); auto.
           rewrite H9 in *.
           assert (gencomm = []) by now eapply history_of_thread_all_nil; eauto.
           rewrite H10, <- H6, H7 in *. simpl in *.

           remember (rev (X_copy s1)) as xcpyrev.
           destruct xcpyrev; unfold get_replay_response, state_with_md in *; simpl in *.
           rewrite <- Heqxcpyrev in *. inversion H2; subst; auto.
           destruct xcpyrev. rewrite <- Heqxcpyrev in *. inversion H2; subst; auto.
           rewrite <- Heqxcpyrev in *; inversion H2; subst; auto.
  Qed.           

  
  Lemma mode_generated_replay :
    forall h s h' t i r,
      generated s h ->
      h' ++ (t,i,r) :: h = X ->
      s.(X_copy) = h' ++ [(t,i,r)] /\
      s.(md) = Replay.
  Proof.
    induction h; intros; inversion H; subst; simpl in *.
    - unfold start_mode. 
      assert (X <> []).
      { rewrite <- H0. intuition. apply app_eq_nil in H1. destruct_conjs; discriminate. }
      destruct X; intuition.
    - assert (s1.(X_copy) = (h' ++ [(t,i,r)]) ++ [(t0,i0,r0)] /\ s1.(md) = Replay) as Hmds1.
      eapply (IHh s1 (h' ++ [(t,i,r)]) t0 i0 r0); eauto. rewrite <- app_assoc. now simpl in *.
      unfold emulator_act in *.
      unfold next_mode in *.
      destruct_conjs.
      rewrite H1, H2 in *; rewrite rev_unit in *.
      destruct i0 as [i0]; simpl in *; repeat rewrite Nat.eqb_refl in *; simpl in *.
      rewrite rev_unit in *.
      unfold get_replay_response, state_with_md in *; simpl in *.
      rewrite H1 in *. rewrite rev_unit in *. inversion H3; subst; simpl in *.
      split; [rewrite rev_involutive|]; auto.
  Qed.

  Lemma mode_generated_commute :
    forall Yend h s Yfront t i r,
      generated s h ->
      h = Yend ++ X ->
      reordered (Yfront ++ (t,i,r) :: Yend) Y ->
      (forall t', s.(Y_copy) t' = history_of_thread (Yfront ++ [(t,i,r)]) t') /\
      s.(md) = Commute.
  Proof.
    induction Yend; intros.
    simpl in *; subst. remember X as HX. destruct HX; inversion H; subst.
    - unfold start_state, start_mode in *. rewrite <- HeqHX; auto.
      simpl in *; split; auto.
    - pose (mode_generated_replay _ s1 [] t0 i0 r0 H6). rewrite app_nil_l in *.
      apply a in HeqHX. destruct_conjs.
      unfold emulator_act in *.
      unfold next_mode in *.
      rewrite H2 in *. rewrite H0 in *. rewrite app_nil_l in *; simpl in *.
      destruct i0 as [i0]; simpl in *; repeat rewrite Nat.eqb_refl in *; simpl in *.
      unfold get_replay_response, state_with_md in *; rewrite H0 in *; simpl in *.
      inversion H3; subst; simpl in *; split; auto.

      intros.
      pose (history_of_thread_reordered_eq _ _ t' H1) as tmp. 
      rewrite history_of_thread_app_distributes in *; simpl in *.
      assert (Y_copy s1 = fun tid => history_of_thread Y tid).
      eapply (during_replay_state s1); eauto.
      now rewrite H4, tmp. 
    - rewrite H0 in H. inversion H.
      destruct a as [[ta ia] ra]; inversion H2; subst.
      assert ((forall t', s1.(Y_copy) t' = history_of_thread
                                           ((Yfront ++ [(t,i,r)]) ++ [(ta, ia, ra)]) t')
             /\ md s1 = Commute) as Hmds1.
      {
        assert (reordered ((Yfront ++ [(t,i,r)]) ++ (ta, ia, ra) :: Yend) Y).
        rewrite <- app_assoc; simpl; auto. 
        eapply (IHYend (Yend ++ X) s1 (Yfront ++ [(t,i,r)]) ta ia ra); eauto.
      }
      unfold emulator_act, next_mode in *. destruct_conjs. rewrite H3 in *.
      pose (H0 ta).
      rewrite history_of_thread_app_distributes in *. simpl in *. rewrite Nat.eqb_refl in *.
      rewrite e, rev_unit in *.
      destruct ia; simpl in *; repeat rewrite Nat.eqb_refl in *; simpl in *.
      unfold get_commute_response in *.
      assert (Y_copy s1 = Y_copy (state_with_md s1 Commute)).
      unfold state_with_md in *; simpl in *; eauto.
      rewrite H5 in *; unfold state_with_md in *; simpl in *.
      rewrite e in *; rewrite rev_unit in *.
      inversion H4; simpl in *; subst.
      split; auto.
      intros.
      destruct (Nat.eq_dec t' ta); subst;
        [rewrite Nat.eqb_refl in *; rewrite rev_involutive
        | rewrite <- Nat.eqb_neq in *; rewrite n0 in *]; auto.
      rewrite (H0 t').
      rewrite history_of_thread_app_distributes in *; simpl in *.
      rewrite Nat.eqb_sym in n0. rewrite n0 in *. now rewrite app_nil_r in *.
  Qed.

  Lemma preHs :
    forall h s, generated s h ->
           preH s = X \/
           (h = postH s ++ preH s /\ exists a x1 x2, preH s = x2 /\ X = a :: x1 ++ x2).
    Proof.
      induction h; intros; inversion H; subst; simpl in *.
      - unfold start_state in *.
        destruct X; auto. right; split; auto.
        exists a, h, []; split; auto. rewrite app_nil_r; auto.
        
      - pose (IHh s1 H5) as e; destruct e; clear IHh;
          unfold emulator_act in *; remember (next_mode s1 t i) as s1nextmd.
        + destruct s1nextmd; symmetry in Heqs1nextmd; auto. 
          * left; pose (commute_mode_state s1 _ _ Heqs1nextmd).
            assert (md s = Commute).
            {
              destruct_conjs.
              unfold get_commute_response in *. rewrite H3 in *. inversion H2; subst; auto.
            }
            eapply during_commute_state; eauto.
          * pose (emulate_response_state _ _ _ _ _ _ H5 H4 H2).
            destruct_conjs.
            rewrite H6. auto.
          * assert (md s1 = Replay).
            eapply next_mode_replay_implies_current_mode_replay; eauto.
            pose (during_replay_state s1 _ H5 H1). destruct_conjs; subst.
            pose (replay_mode_state s1 _ _ Heqs1nextmd); destruct_conjs; subst.
            replace (X_copy (state_with_md s1 Replay)) with (X_copy s1) in H9.
            rewrite <- rev_rev in H9.
            rewrite rev_involutive in *.
            rewrite H9 in H10. rewrite H0 in H10.
            assert (rev (e :: H3) ++ X = [] ++ X).
            rewrite H10. simpl; auto.
            apply app_inv_tail in H12. inversion H12.
            apply app_eq_nil in H14; destruct_conjs; discriminate.
            unfold state_with_md in *; simpl in *; auto.
        + destruct s1nextmd; symmetry in Heqs1nextmd.
          * pose (commute_mode_state s1 _ _ Heqs1nextmd).
            assert (md s = Commute).
            {
              destruct_conjs; subst.
              unfold get_commute_response in *. rewrite H6 in *. inversion H2; subst; auto.
            }
            left; eapply during_commute_state; eauto.
          * pose (emulate_response_state _ _ _ _ _ _ H5 H4 H2).
            destruct_conjs.
            rewrite H6, H3. auto. rewrite H0.
            right; split; simpl; auto.
            exists H7, H8, H9; auto.
          * assert (md s1 = Replay).
            eapply next_mode_replay_implies_current_mode_replay; eauto.
            pose (during_replay_state s1 _ H5 H1). destruct_conjs; subst.
            rewrite H6 in *; simpl in *.
            rewrite H16 in *.
            assert (X_copy s1 = H10 :: H13) by now eapply app_inv_tail; eauto. 
            assert (md s = Replay \/ md s = Commute).
            {

              remember (rev (X_copy s1)) as s1xcpy; destruct s1xcpy; unfold get_replay_response in *;
                unfold state_with_md in *; simpl in *; rewrite <- Heqs1xcpy in *.
              inversion H2; subst; auto.
              destruct s1xcpy; inversion H2; subst; auto.
            } destruct H9.
            -- pose (during_replay_state s _ H H9); destruct_conjs; subst.
               rewrite H16 in H19.
               right; split.
               rewrite H12. rewrite H14. simpl in *; auto.
               rewrite H0 in *. remember (H10 :: H13) as bleh; destruct bleh using rev_ind.
               inversion Heqbleh. clear IHbleh.
               rewrite rev_unit in *. destruct bleh; simpl in *.
               unfold get_replay_response, state_with_md in *; subst; simpl in *; auto.
               inversion Heqbleh; subst. rewrite H0 in *; simpl in *.
               inversion H2; subst; simpl in *; discriminate.

               remember (rev bleh ++ [a]) as tmp; destruct tmp.
               symmetry in Heqtmp. apply app_eq_nil in Heqtmp. destruct_conjs; discriminate.
               rewrite <- H11 in *.
               exists a, bleh, ((t,i,r) :: preH s1). split; simpl in *; auto.
               assert (x = (t,i,r)).
               {
                 assert ((X_copy s ++ [(t, i, r)]) ++ preH s1
                         = (a :: bleh ++ [x]) ++ preH s1).
                 rewrite <- app_assoc; simpl in *. auto.
                 apply app_inv_tail in H18.
                 assert (rev (X_copy s ++ [(t,i,r)]) = rev ((a :: bleh) ++ [x])).
                 apply rev_rev; auto.
                 repeat rewrite rev_unit in *. inversion H20; auto.
               }
               rewrite H18. rewrite <- app_assoc. simpl in *; auto.
            -- pose (during_commute_state s _ H H9); destruct_conjs; subst.
               pose (during_replay_state s1 _ H5 H1); destruct_conjs; subst.
               left. rewrite H16 in H15. auto.
    Qed.

    Lemma correct_state_correct_generated_history :
    forall s h x,
      generated s h ->
      spec (x ++ get_state_history s) <-> spec (x ++ h).
  Proof.
    intros s h x Hgen. split; intros Hspec;
    unfold get_state_history in *; simpl in *;
    pose (state_combined_histories_is_reordered_Y h s Hgen) as Hh';
    pose (reordered_Y_prefix_correct 
            (combined_histories s.(commH))
            (combined_histories s.(Y_copy))
            Hh') as Hcomm;
    destruct (preHs h s Hgen);
    destruct (generated_history_corresponds_state_history h s Hgen) as [gencommH [Horder Hh]].

    - rewrite <- Hh.
      rewrite H. rewrite app_assoc in *.
      eapply sim_commutes; eauto.
      rewrite H in Hspec. auto.
    - unfold reordered in *.
      destruct_conjs; subst.
      apply app_inv_head in Hh. rewrite <- app_nil_l in Hh.
      apply app_inv_tail in Hh. subst; simpl in *.
      unfold reordered in *.
      simpl in *.
      symmetry in Horder.
      rewrite (history_of_thread_all_nil _ Horder) in *. simpl in *; auto.
    - rewrite H, <- Hh in *. apply reordered_sym in Horder.
      assert (reordered (combined_histories (Y_copy s) ++ gencommH) Y).
      {
        eapply reordered_prefix; eauto.
      }
      rewrite app_assoc in *.
      eapply sim_commutes; eauto. 
    - unfold reordered in *.
      destruct_conjs; subst.
      apply app_inv_head in Hh. rewrite <- app_nil_l in Hh.
      apply app_inv_tail in Hh. subst; simpl in *.
      unfold reordered in *.
      simpl in *. symmetry in Horder.
      rewrite (history_of_thread_all_nil _ Horder) in *.
      simpl in *. auto.
  Qed.
  
End State_Lemmas.

