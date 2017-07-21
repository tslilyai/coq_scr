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
                              (state_with_md s1 Emulate) t i 0 max_response_number);
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
                              (state_with_md s1 Emulate) t i 0 max_response_number);
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
        try destruct (Nat.eq_dec n n0); subst;
        try (left; auto; fail); right; simpl in *;
          try rewrite Nat.eq_refl in *;
          destruct (t2 =? t);
          try (apply in_inv in Hin; destruct Hin; [inversion H; symmetry in H1; contradiction | auto]);
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
         md := Emulate |} t i 0 max_response_number); inversion H2; subst; simpl in *; auto.
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
    - pose (IHh s1 H5) as IHs1.
      unfold emulator_act in *.
      destruct (next_mode s1 t i) in *; unfold state_with_md in *; simpl in *.
      + unfold get_commute_response in *; simpl in *.
        destruct (rev (Y_copy s1 t)). inversion H2; subst; auto.
        simpl in *. 
  Admitted.

  Lemma correct_state_correct_generated_history :
    forall s h,
      generated s h ->
      spec (get_state_history s) ->
      spec h.
  Proof.
    intros s h Hgen Hspec.
    destruct (generated_history_corresponds_state_history h s Hgen) as [gencommH [Horder Hh]].
    unfold get_state_history in *; simpl in *.
    pose (state_combined_histories_is_reordered_Y h s Hgen) as Hh'.
    pose (reordered_Y_prefix_correct 
            (combined_histories s.(commH))
            (combined_histories s.(Y_copy))
            Hh') as Hcomm.
  Admitted.
 
End Misc.

