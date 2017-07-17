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

  Theorem reordered_cons_app : forall l l1 l2 a,
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
    intros x l l' H IH; intros. admit. (*
    break_list l1 b l1' H0; break_list l3 c l3' H1.
    auto.
    apply ro_perm_trans with (l3'++c::l4); auto.
    apply ro_perm_trans with (l1'++a::l2); auto using reordered_cons_app.
    apply perm_skip.
    apply (IH a l1' l2 l3' l4); auto. *)
    intros x y l l' Hswap Hp IH; intros.
    break_list l1 b l1' H; break_list l3 c l3' H0.
    auto.
    break_list l3' b l3'' H.
    auto.
    apply ro_perm_trans with (c::l3''++b::l4); auto. admit.
    break_list l1' c l1'' H1.
    auto.
    apply ro_perm_trans with (b::l1''++c::l2); auto. admit.
    break_list l3' d l3'' H; break_list l1' e l1'' H1.
    auto.
    apply ro_perm_trans with (e::a::l1''++l2); auto.
    apply ro_perm_trans with (e::l1''++a::l2); auto.
    admit.
    apply ro_perm_trans with (d::a::l3''++l4); auto.
    apply ro_perm_trans with (d::l3''++a::l4); auto.
    admit.
    apply ro_perm_trans with (e::d::l1''++l2); auto.
    apply ro_perm_skip; apply ro_perm_skip.
    apply (IH a l1'' l2 l3'' l4); auto.
    intros.
    destruct (In_split a l') as (l'1,(l'2,H6)).
    apply (reordered_in l _ a); auto.
    subst l.
    apply in_or_app; right; red; auto.
    apply ro_perm_trans with (l'1++l'2).
    apply (H0 _ _ _ _ _ H3 H6).
    apply (H2 _ _ _ _ _ H6 H4).
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
    assert (reordered (hd1 ++ tl1) (hd2 ++ tl1)).
    {
      eapply ro_perm_trans; eauto.
    }
    eapply reordered_app_inv_hd; eauto.
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
End Misc.
