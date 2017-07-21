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
(*  Hint Constructors reordered. *)

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
  
  Lemma swappable_sym : forall a1 a2, swappable a1 a2 -> swappable a2 a1.
  Proof.
    intros.
    destruct a1 as [[t i] r].
    destruct a2 as [[t2 i2] r2].
    unfold swappable in *; auto.
  Qed.
(*
  Lemma reordered_nil : forall h, reordered h [] -> h = [].
  Proof.
    intros.
    remember [] as N in H.
    unfold reordered in *. subst. simpl in *.
    induction H; discriminate || auto.
  Qed.

  Lemma reordered_refl : forall h, reordered h h.
  Proof.
    intros; induction h; eauto.
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

  Hint Resolve reordered_sym reordered_refl swappable_sym.
  Theorem reordered_ind_bis :
    forall P : history -> history -> Prop,
      P [] [] ->
      (forall x l l', reordered l l' -> P l l' -> P (x :: l) (x :: l')) ->
      (forall x y l l', swappable x y ->
                        reordered l l' ->
                        P l l' ->
                        P (y :: x :: l) (x :: y :: l')) ->
      (forall l l' l'', reordered l l' -> P l l' -> reordered l' l'' -> P l' l'' -> P l l'') ->
      forall l l', reordered l l' -> P l l'.
  Proof.
    intros P Hnil Hskip Hswap Htrans.
    induction 1; auto.
    apply Htrans with (a1::a2::t); auto.
    apply Hswap; auto.
    induction t; auto.
    apply Hskip; auto.
    apply Hskip; auto.
    induction t; auto.
    eauto.
  Qed.

  Ltac break_list l x l' H :=
  destruct l as [|x l']; simpl in *;
  injection H; intros; subst; clear H.

  Lemma reordered_cons_app : forall l l1 l2 a,
      reordered l (l1 ++ l2) ->
      (forall a0, List.In a0 l1 -> swappable a a0) ->
      reordered (a :: l) (l1 ++ a :: l2).
  Proof.
    intros l l1; revert l.
    induction l1.
    simpl.
    intros; apply ro_perm_skip; auto.
    simpl; intros.
    apply ro_perm_trans with (a0::a::l1++l2).
    apply ro_perm_skip; auto.
    apply ro_perm_trans with (a::a0::l1++l2).
    apply ro_perm_swap; auto.
    apply ro_perm_skip; auto.
  Qed.
  Hint Resolve reordered_cons_app.

  Theorem reordered_app_inv : forall l1 l2 l3 l4 a,
      reordered (l1++a::l2) (l3++a::l4) -> reordered (l1++l2) (l3++l4).
  Proof.
    set (P:=fun l l' => 
             forall a l1 l2 l3 l4, l=l1++a::l2 -> l'=l3++a::l4 -> reordered (l1++l2) (l3++l4)).
    cut (forall l l', reordered l l' -> P l l').
    intros; apply (H _ _ H0 a); auto.
    intros; apply (reordered_ind_bis P); unfold P; clear P; try clear H l l'; simpl; auto.
    intros; destruct l1; simpl in *; discriminate.
    intros x l l' H IH; intros. admit. 
  Admitted.

  Lemma reordered_cons_inv : forall a l1 l2, reordered (a :: l1) (a :: l2) -> reordered l1 l2.
  Proof.
    intros. exact (reordered_app_inv [] l1 [] l2 a H).
  Qed.
  
  Lemma reordered_app_inv_hd :
    forall l l1 l2, reordered (l1++l) (l2++l) -> reordered l1 l2.
  Proof.
    induction l.
    intros l1 l2. do 2 rewrite app_nil_r; auto.
    intros.
    apply IHl.
    now apply reordered_app_inv in H.
  Qed.
    
  Lemma reordered_app_inv_prefix :
    forall hd1 hd2 tl1 tl2,
    reordered (hd1++tl1) (hd2++tl2) ->
    reordered tl1 tl2 ->
    reordered hd1 hd2.
  Proof.
    intros.
    assert (reordered (hd2++tl1) (hd1++tl1)).
    {
      eapply reordered_prefix; apply reordered_sym in H; apply reordered_sym in H0; eauto.
    }
    assert (reordered (hd1 ++ tl1) (hd2 ++ tl1)) by now eapply ro_perm_trans; eauto.
    eapply reordered_app_inv_hd; eauto.
  Qed.
*)    
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
    forall (f : state -> tid -> history) s t,
      IsHistories (f s) ->
      history_of_thread (combined_histories (f s)) t = f s t.
  Proof.
    intros.
    unfold combined_histories.
    destruct (tid_le_num_threads t) as [HG bleh].
    destruct (combine_tid_histories_parts (f s) H t num_threads HG) as
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

  Lemma history_of_thread_eq_iff_reordered :
    forall h h' t,
      reordered h h' <->
      history_of_thread h' t = history_of_thread h t.
  Proof.
    intros.
    induction H; subst; auto.
    - unfold history_of_thread in *; simpl in *; fold history_of_thread in *.
      rewrite IHreordered; auto.
    - destruct a2 as [[t1 i1] r1]; destruct a1 as [[t2 i2] r2]. unfold swappable in *.
      unfold history_of_thread in *; simpl in *; fold history_of_thread in *.
      destruct (Nat.eq_dec t1 t), (Nat.eq_dec t2 t); subst; try (now intuition);
        rewrite <- Nat.eqb_neq in *; try rewrite Nat.eqb_refl; try rewrite n in *; auto.
    - now rewrite <- IHreordered1.
  Qed.
  
  Lemma history_of_thread_nonempty :
    forall h' t i r h,
      reordered (h' ++ (t, i, r) :: h) Y ->
      history_of_thread Y t = history_of_thread h' t ++ (t,i,r) :: history_of_thread h t.
  Proof.
    intros.
    rewrite (history_of_thread_reordered_eq _ _ t H).
    rewrite history_of_thread_app_distributes.
    unfold history_of_thread in *; simpl in *; fold history_of_thread in *.
    now rewrite Nat.eqb_refl.
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
    Ltac equal_histories := eapply history_of_thread_reordered_eq; eauto;
                            apply reordered_sym; auto.
    intros s h h1 h2 t i r gencomm Hr1 Hr2 Hr3 Hgen.
    assert (reordered (h1 ++ (t,i,r) :: h2) (combined_histories (Y_copy s))).
    {
      eapply reordered_app_inv_prefix; eauto. eapply ro_perm_trans; eauto.
      rewrite <- app_assoc; eauto.
    }
    assert (history_of_thread
              (combined_histories (Y_copy s) ++ combined_histories (commH s)) t
            = history_of_thread Y t) as Ht1 by now equal_histories.
    assert (history_of_thread (h1 ++ [(t, i, r)] ++ h2 ++ gencomm) t
            = history_of_thread Y t) as Ht2 by now equal_histories.
    assert (history_of_thread gencomm t =
            history_of_thread (combined_histories (commH s)) t) as Ht3 by
          now equal_histories.
    assert (h1 ++ [(t, i, r)] ++ h2 ++ gencomm = ((h1 ++ [(t, i, r)]) ++ h2++ gencomm)) as rw by
          now rewrite <- app_assoc; simpl.
    rewrite rw in *.
    repeat rewrite history_of_thread_app_distributes in Ht2.
    rewrite history_of_thread_app_distributes in Ht1.
    do 2 rewrite history_of_thread_combined_is_application in Ht1.
    rewrite history_of_thread_combined_is_application in Ht3.
    rewrite <- Ht2, Ht3 in Ht1.
    rewrite app_assoc in Ht1. eapply app_inv_tail in Ht1.
    unfold history_of_thread in Ht1; simpl in *.
    fold history_of_thread in Ht1; rewrite Nat.eqb_refl in *;
      rewrite Ht1; try rewrite <- app_assoc; simpl in *; auto.
    all: eauto.
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
    
  Lemma reordered_thread_order :
    forall h h',
      (forall t, history_of_thread h t = history_of_thread h' t) ->
      reordered h h'.
  Proof.
    induction h; intros.
    simpl in *.
    assert (h' = []) by now eapply history_of_thread_all_nil; eauto.
    subst; constructor.

    assert (List.In a h').
    {
      assert (List.In a (a::h)) by now apply in_eq.
      apply (in_history_iff_in_thread_history _ _) in H0.
      destruct H0. rewrite (H x) in H0.
      eapply (in_history_iff_in_thread_history _ _); eauto.
    }
    destruct (in_split a h' H0) as [l1 [l2 Hh']]; subst.
    eapply in_history_iff_in_thread_history in H0. destruct H0.
    destruct a as [[ta ia] ra].
    apply history_of_thread_in_teq in H0; subst.
    assert ((forall t : tid, x =? t = false -> history_of_thread h t = history_of_thread (l1 ++ l2) t)).
    {
      intros. pose (H t) as Ht.
      rewrite history_of_thread_app_distributes in *.
      simpl in *. rewrite H0 in *; auto.
    }
    assert (reordered h (List.filter (fun a => eqb ((thread_of_action a) =? x) false) (l1 ++ l2))).
    {
      eapply IHh. intros.
      pose (H0 t).
      admit.
    }
    assert (reordered 
    pose (H x). rewrite history_of_thread_app_distributes in *.
    simpl in *. rewrite Nat.eqb_refl in *.
    assert (forall a, List.In a l1 -> thread_of_action a <> x).
    destruct (Nat.eq_dec x t).
    
    simpl in *.
    remember (thread_of_action a =? t) as Htaeq.
    apply IHh l2 
  Admitted.
    
  Lemma state_combined_histories_is_reordered_Y :
    forall h s,
      generated s h ->
      reordered (combined_histories s.(Y_copy) ++ combined_histories s.(commH)) Y.
  Proof.
    induction h; intros; inversion H; subst.
    - unfold start_state in *; simpl in *.
      unfold combined_histories in *.
      rewrite combine_tid_histories_nil, app_nil_r.
      Search (combine_tid_histories).
      
      admit.
    - pose (IHh s1 H5).
      unfold emulator_act in *.
      destruct (next_mode s1 t i) in *; unfold state_with_md in *; simpl in *.
      + unfold get_commute_response in *; simpl in *.
        destruct (rev (Y_copy s1 t)); inversion H2; subst; simpl in *; auto.
        admit.
      + unfold get_emulate_response in *.
        functional induction ( get_emulate_response_helper
         {|
         X_copy := X_copy s1;
         Y_copy := Y_copy s1;
         preH := preH s1;
         commH := commH s1;
         postH := postH s1;
         md := Emulate |} t i 0 max_response_number); inversion H2; subst; auto.
      + remember (rev (X_copy s1)) as rxcpys1.
        destruct (rxcpys1); unfold get_replay_response in *; simpl in *; inversion H2; subst; auto.
        rewrite <- Heqrxcpys1 in *.
        1,2: inversion H1; subst; simpl in *; auto.
        rewrite <- Heqrxcpys1 in *. destruct l; inversion H3; subst; simpl in *; auto.
  Admitted.
  
  Lemma reordered_Y_prefix_correct :
    forall h h',
      reordered (h' ++ h) Y ->
      spec (h ++ X).
  Proof.
    induction h; simpl in *; intros.
    - pose (X_and_Y_in_spec); eapply (spec_prefix_closed); eauto.
    - assert (reordered ((h' ++ [a]) ++ h) Y).
      eapply ro_perm_trans; eauto. rewrite <- app_assoc. simpl in *; apply reordered_refl.
      assert (spec (h++X)). eapply IHh; eauto.
      remember Y as HY.
      remember ((h' ++ [a]) ++ h) as hist.

      induction H0; subst; auto.
      + symmetry in Heqhist; apply app_eq_nil in Heqhist; destruct_conjs.
        apply app_eq_nil in H0; destruct_conjs; discriminate.
      + assert (spec ((x :: t2) ++ X)).
        {
          rewrite HeqHY. apply (X_and_Y_in_spec).
        }
        assert (spec (x :: t1 ++ X)).
        {
          eapply (sim_commutes [] (x::t2) (x::t1) []); simpl in *; eauto.
          rewrite HeqHY. apply reordered_refl.
          apply ro_perm_skip. auto.
        }
        eapply (spec_prefix_closed); eauto.
        rewrite (app_comm_cons). rewrite Heqhist.
        do 2 rewrite <- app_assoc; simpl in *; eauto.
      + assert (spec ((a1 :: a2 :: t) ++ X)).
        {
          rewrite HeqHY. apply (X_and_Y_in_spec).
        }
        assert (spec (a2 :: a1 :: t ++ X)).
        {
          eapply (sim_commutes [] (a1::a2::t) (a2::a1::t) []); simpl in *; eauto.
          rewrite HeqHY. apply reordered_refl.
          apply ro_perm_swap; eauto.
        }
        eapply (spec_prefix_closed); eauto.
        assert (a2 :: a1 :: t ++ X = (a2 :: a1 :: t) ++ X).
        simpl in *. auto.
        rewrite H4 in *. rewrite Heqhist; simpl in *; do 2 rewrite <- app_assoc in *; eauto.
      + apply (ro_perm_trans _ _ _ H0_) in H0_0.
        assert (spec (h' ++ [a] ++ h ++ X)).
        pose (sim_commutes [] Y (h' ++ a :: h) []); simpl in *.
        rewrite <- app_assoc in *. rewrite app_comm_cons in *.
        eapply s; eauto. apply reordered_refl.
        apply (X_and_Y_in_spec).
        eapply spec_prefix_closed; eauto.
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

Section StrongInduction.

  Variable P:nat -> Prop.

  (** The stronger inductive hypothesis given in strong induction. The standard
  [nat ] induction principle provides only n = pred m, with [P 0] required
  separately. *)
  Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

  Lemma P0 : P 0.
  Proof.
    apply IH; intros.
    exfalso; inversion H.
  Qed.

  Hint Resolve P0.

  Lemma pred_increasing : forall n m,
      n <= m ->
      Nat.pred n <= Nat.pred m.
  Proof.
    induction n; cbn; intros.
    apply le_0_n.
    induction H; subst; cbn; eauto.
    destruct m; eauto.
  Qed.

  Hint Resolve le_S_n.

  Local Lemma strong_induction_all : forall n,
      (forall m, m <= n -> P m).
  Proof.
    induction n; intros;
      match goal with
      | [ H: _ <= _ |- _ ] =>
        inversion H
      end; eauto.
  Qed.

  Theorem strong_induction : forall n, P n.
  Proof.
    eauto using strong_induction_all.
  Qed.

End StrongInduction.
