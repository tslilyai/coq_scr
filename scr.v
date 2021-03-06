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
Require Import helpers.

Hint Resolve y_copy_state Y_performed_state.

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

Section Existance.
  
  Lemma get_oracle_response_exists :
    forall s h t i,
      current_state_history s h ->
      spec ((t,i,NoResp)::h) ->
      exists rtyp s', get_oracle_response (state_with_md s Oracle) t i = (s', (t,i,Resp rtyp)).
  Proof.
    intros. unfold get_oracle_response in *.
    pose (oracle_response_correct (get_state_history (state_with_md s Oracle)) t i);
      destruct_conjs; rewrite H1; subst; eauto.
  Qed.
  
  Lemma machine_act_response_exists :
    forall s h t i,
      current_state_history s h ->
      spec ((t,i,NoResp)::h) ->
      exists rtyp s',
        machine_act s t i = (s', (t,i,Resp rtyp)).
  Proof.
    intros s h t i Hgen Hspec.
    revert dependent s. revert dependent t. revert dependent i.
    induction h; intros; inversion Hgen; subst.

    Ltac solve_oracle_response :=
      match goal with
      | [ Hgen : current_state_history ?s ?h, Heqmds : ?md = md ?s |-
          exists rtyp s', get_oracle_response ?s0 ?t ?i = _ ] =>
        eapply (get_oracle_response_exists s); eauto;
        assert (current_state_history (state_with_md s0 md) h) as HAH; [
          unfold state_with_md in *; simpl in *;
          destruct s; simpl in *; rewrite <- Heqmds in *; auto
        | apply HAH]
      | [ Hgen : current_state_history ?s ?h |- exists rtyp s', get_oracle_response _ _ _ = _] =>
        eapply (get_oracle_response_exists s); eauto;
        unfold state_with_md in *
      end.
    
    - unfold start_state in *; unfold start_mode in *; simpl in *.
      unfold machine_act, next_mode.
      remember X as HX; destruct HX using rev_ind; simpl in *.
      remember (history_of_thread Y t) as Yhist.
      destruct (Yhist) using rev_ind; [|rewrite rev_unit]; unfold state_with_md; simpl in *.
      + solve_oracle_response.
      + remember (action_invocation_eq x t i) as Hacteq.
        destruct Hacteq.
        * unfold get_commute_response; simpl in *. rewrite <- HeqYhist; rewrite rev_unit; eauto.
          destruct x as [[tx [ix]] rx]; destruct i as [i]. inversion HeqHacteq.
          simpl in *. symmetry in H0; rewrite andb_true_iff in *;
                        destruct_conjs; rewrite Nat.eqb_eq in *; subst.
          destruct rx; eauto.
          assert (exists rtyp, NoResp = Resp rtyp).
          {
            eapply X_and_Y_wf.
            assert (List.In (tx, Inv i, NoResp) Y).
            assert (List.In (tx, Inv i, NoResp) (history_of_thread Y tx)).
            rewrite <- HeqYhist. apply in_or_app; right. apply in_eq.
            eapply history_of_thread_sublist; eauto.
            apply in_or_app; left; eauto.
          }
          destruct H as [rtyp bleh]; discriminate.
        * solve_oracle_response.
      + clear IHHX.
        remember (HX ++ [x]) as blah; destruct blah;
          [symmetry in Heqblah; apply app_eq_nil in Heqblah; destruct_conjs; discriminate|
           rewrite Heqblah in *].
        rewrite rev_unit.
        remember (action_invocation_eq x t i) as Hacteq.
        destruct Hacteq.
        * destruct HX using rev_ind; try rewrite app_nil_l in *; simpl in *.
          unfold get_replay_response, state_with_md in *; simpl in *.
          assert (exists rtyp, x = (t,i,Resp rtyp)).
          destruct x as [[tx [ix]] rx]; destruct rx.
          inversion HeqHacteq; destruct i as [i].
          symmetry in H0; rewrite andb_true_iff in *; repeat rewrite Nat.eqb_eq in *;
            destruct_conjs; subst.
          exists r; auto.
          assert (exists rtyp, NoResp = Resp rtyp).
          {
            eapply X_and_Y_wf.
            assert (List.In (tx, Inv ix, NoResp) X).
            rewrite <- HeqHX; apply in_eq.
            apply in_or_app; right; eauto.
          } destruct H as [rtyp bleh]; discriminate.
          destruct H as [rtyp bleh]; rewrite bleh; eauto.

          rewrite rev_unit. clear IHHX.
          unfold get_replay_response, state_with_md in *; simpl in *.
          assert (exists rtyp, x = (t,i,Resp rtyp)).
          destruct x as [[tx [ix]] rx]; destruct rx.
          inversion HeqHacteq; destruct i as [i].
          symmetry in H0; rewrite andb_true_iff in *; repeat rewrite Nat.eqb_eq in *;
            destruct_conjs; subst.
          exists r; auto.
          assert (exists rtyp, NoResp = Resp rtyp).
          {
            eapply X_and_Y_wf.
            assert (List.In (tx, Inv ix, NoResp) X).
            rewrite <- HeqHX. apply in_or_app.
            right; apply in_eq.
            apply in_or_app; right; eauto.
          } destruct H as [rtyp bleh]; discriminate.
          destruct H as [rtyp bleh]; rewrite bleh; eauto.
          rewrite rev_unit; eauto.
        * solve_oracle_response.
    - unfold machine_act.
      remember (next_mode s t i) as snextmd.
      rewrite Heqsnextmd.
      unfold machine_act, next_mode in *; remember (md s) as mds; destruct mds.
      + remember (Y_copy s t) as sycpy. destruct sycpy using rev_ind; subst; simpl in *.
        * solve_oracle_response.
        * rewrite rev_unit. 
          remember (action_invocation_eq x t i) as Hacteq.
          destruct Hacteq.
          unfold get_commute_response; simpl in *. rewrite <- Heqsycpy; rewrite rev_unit; eauto.
          destruct x as [[tx [ix]] rx]; destruct i as [i]. inversion HeqHacteq.
          simpl in *. symmetry in H0; rewrite andb_true_iff in *;
                        destruct_conjs; rewrite Nat.eqb_eq in *; subst.
          destruct rx; eauto.
          assert (exists rtyp, NoResp = Resp rtyp).
          {
            eapply X_and_Y_wf.
            symmetry in Heqmds.
            pose (during_commute_state _ ((t0, i0, r)::h) Hgen Heqmds); destruct_conjs.
            assert (List.In (tx, Inv i, NoResp) Y).
            assert (List.In (tx, Inv i, NoResp) (history_of_thread
                                                   (combined_histories (Y_copy s)) tx)).
            rewrite history_of_thread_combined_is_application.
            rewrite <- Heqsycpy. apply in_or_app; right. apply in_eq.
            eauto.
            eapply reordered_in. apply H.
            apply in_or_app. left.
            eapply history_of_thread_sublist; eauto.
            apply in_or_app; left; eauto.
          }
          destruct H as [rtyp bleh]; discriminate.
          solve_oracle_response.
      + solve_oracle_response.
      + remember (X_copy s) as sxcpy. destruct sxcpy using rev_ind; simpl in *; auto.
        * solve_oracle_response.
        * rewrite rev_unit in *.         
          remember (action_invocation_eq x t i) as Hacteq. destruct Hacteq.

          destruct sxcpy using rev_ind; unfold get_replay_response, state_with_md in *; simpl in *;
          symmetry in Heqmds; pose (during_replay_state _ _ Hgen Heqmds); destruct_conjs; subst.

          rewrite <- Heqsxcpy; simpl in *.
          assert (exists rtyp, x = (t,i,Resp rtyp)).
          destruct x as [[tx [ix]] rx]; destruct rx.
          inversion HeqHacteq; destruct i as [i].
          symmetry in H8; rewrite andb_true_iff in *; repeat rewrite Nat.eqb_eq in *;
            destruct_conjs; subst.
          exists r0; auto.
          assert (exists rtyp, NoResp = Resp rtyp) as ha.
          {
            eapply X_and_Y_wf.
            assert (List.In (tx, Inv ix, NoResp) X).
            rewrite <- H7, <- Heqsxcpy.
            apply in_or_app; left; apply in_eq.
            apply in_or_app; right; eauto.
          } destruct ha as [rtyp bleh]; discriminate.
          destruct H6 as [rtyp bleh]; rewrite bleh; eauto.
          
          repeat rewrite rev_unit, <- Heqsxcpy, rev_unit.
          assert (exists rtyp, x = (t,i,Resp rtyp)).
          destruct x as [[tx [ix]] rx]; destruct rx.
          inversion HeqHacteq; destruct i as [i].
          symmetry in H8; rewrite andb_true_iff in *; repeat rewrite Nat.eqb_eq in *;
            destruct_conjs; subst.
          exists r0; auto.
          assert (exists rtyp, NoResp = Resp rtyp) as ha.
          {
            eapply X_and_Y_wf.
            assert (List.In (tx, Inv ix, NoResp) X).
            rewrite <- H7, <- Heqsxcpy.
            apply in_or_app; left. apply in_or_app; right. apply in_eq.
            apply in_or_app; right; eauto.
          } destruct ha as [rtyp bleh]; discriminate.
          destruct H6 as [rtyp bleh]; rewrite bleh; eauto.

          solve_oracle_response.
  Qed.
  
  Lemma current_state_history_response_exists :
    forall s h t i,
      current_state_history s h ->
      spec ((t,i,NoResp)::h) ->
      exists rtyp s',
        current_state_history s' ((t,i,Resp rtyp)::h).
  Proof.
    intros s h t i Hgen Hspec.
    destruct (machine_act_response_exists _ _ _ _ Hgen Hspec) as [rtyp [s' Hact]].
    exists rtyp; exists s'; eapply GenCons; eauto.
  Qed.

  Lemma response_always_exists :
    forall s h t i r,
      current_state_history s h ->
      List.In (t,i,r) h ->
      exists rtyp, r = Resp rtyp.
  Proof.
    intros s h t i r Hgen Hin.
    pose Hgen as Hgen'.
    induction Hgen'.
    inversion Hin.
    assert (exists rtyp s', current_state_history s' ((t0,i0,Resp rtyp)::h)) as Hgenexists. {
      eapply current_state_history_response_exists; eauto.
    } destruct Hgenexists as [rtyp [s' Hgenexists]].
    inversion Hgenexists; subst.

    remember (action_invocation_eq (t,i,r) t0 i0) as Heq.
    destruct Heq, i, i0, r, r0; try destruct (Nat.eq_dec r r0); unfold_action_inv_eq;
    subst; inversion Hin; try inversion H1; try (now exists r0); try (now exists r);
      try eapply IHHgen'; eauto.
    subst.
    pose (IHHgen' Hgen').

    all : subst; rewrite (current_state_history_deterministic s0 s1 h) in H5; auto.
    all : pose (machine_deterministic s1 s' s2 t (Inv n) (t, Inv n, Resp rtyp) (t, Inv n, NoResp))
      as Heq; destruct Heq as [Hseq Haeq]; auto.
    all : inversion Haeq.
  Qed.

End Existance.

  Ltac discriminate_noresp :=
    match goal with
      | [ H : (_, (?t, ?i, NoResp)) = (_, ?a'),
              Hspec : spec ((?t, ?i, NoResp) :: ?h),
                      Hact : machine_act ?s ?t ?i = (?s', ?a') |- _ ] =>
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
      | [ Hgen : current_state_history ?s2 ((?t,?i,NoResp)::?h) |- _] =>
          pose (response_always_exists s2 ((t,i,NoResp)::h) t i NoResp Hgen) as Hexists;
            assert (List.In (t, i, NoResp) ((t, i, NoResp) :: h)) as Hin; [ apply in_eq |];
            destruct (Hexists Hin) as [rtyp Ha]; inversion Ha; auto
    end.
  
Section Correctness.
  
  Lemma get_oracle_response_correct :
    forall s h t i s' rtyp,
      current_state_history s h ->
      spec ((t,i,NoResp)::h) ->
      next_mode s t i = Oracle ->
      get_oracle_response (state_with_md s Oracle) t i = (s',(t,i,Resp rtyp)) ->
      spec ((t,i,Resp rtyp)::h).
  Proof.
    intros s h t i s' rtyp Hgen Hspec Hnextmd Hact.
    pose (oracle_response_correct (get_state_history (state_with_md s Oracle)) t i);
      destruct_conjs.
    assert (spec h).
    {
      replace ((t,i,NoResp) :: h) with ([(t,i,NoResp)] ++ h) in Hspec.
      eapply spec_prefix_closed in Hspec; eauto.
      simpl; auto.
    }
    assert (current_state_history s' ((t, i, Resp e) :: h)) as Hnewgen.
    {
      assert (machine_act s t i = (s', (t,i,Resp e))).
      unfold machine_act in *. rewrite Hnextmd.
      unfold get_oracle_response in *. rewrite H in *.
      inversion Hact; subst; auto.
      eapply GenCons; eauto.
    }
    unfold get_oracle_response in *; inversion Hact; subst; auto.
    rewrite H in *.
    replace ((t, i, Resp e) :: h) with ([(t,i,Resp e)] ++ h).
    eapply correct_state_correct_current_state_history; simpl in *; eauto.
    simpl; auto.
  Qed.
  
  Lemma get_commute_response_correct :
    forall s h t i s' rtyp,
      current_state_history s h ->
      spec ((t,i,NoResp)::h) ->
      next_mode s t i = ConflictFree ->
      get_commute_response (state_with_md s ConflictFree) t i = (s',(t,i,Resp rtyp)) ->
      spec ((t,i,Resp rtyp)::h).
  Proof.
    intros s h t i s' rtyp Hgen Hspec Hnextmd Hact.
    pose Hact as Hact'.
    unfold get_commute_response in Hact'.
    pose (commute_mode_state s t i) as Hstate; destruct Hstate as [hd [tl [Hnil Heq]]]; auto.
    rewrite Hnil in Hact'.
    unfold state_with_md in Hact'; subst; simpl in *.
    assert (s.(md) = Replay \/ s.(md) = ConflictFree) as Hsmd.
    {
      unfold next_mode in *.
      destruct (md s); [right | discriminate | left]; auto.
    }
    assert (machine_act s t i = (s', (t,i,Resp rtyp))) as Hemact.
    {
      unfold machine_act. rewrite Hnextmd; auto.
    }
    assert (current_state_history s' ((t,i,Resp rtyp) :: h)) as Hgens' by now eapply GenCons; eauto.
    assert (md s' = ConflictFree) as Hmds' by now inversion Hact'; now subst.
    destruct Hsmd as [Hsmd | Hsmd];
      pose (during_commute_state s' ((t,i,Resp rtyp)::h) Hgens' Hmds') as Hstates';
      pose (reordered_Y_prefix_correct) as HY;
      destruct Hstates' as [Hreordered [[gencomm [Hrespeq Hgencommorder]] [HHistory rest]]];
      apply reordered_sym in Hgencommorder;
      pose (reordered_prefix _ _ _ _ Hreordered Hgencommorder) as HYorder;
      apply HY in HYorder;
      now rewrite Hrespeq in *.
  Qed.

  Lemma get_replay_response_correct :
    forall s h t i s' rtyp mde,
      current_state_history s h ->
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

  Theorem machine_correct :
    forall s h,
      current_state_history s h ->
      spec h.
  Proof.
    intros s h Hgen. pose Hgen as Hgen'.
    induction Hgen'.
    apply spec_nonempty.
    pose H as Hact.
    unfold machine_act in Hact.
    assert (current_state_history s2 ((t,i,r)::h)). eapply GenCons; eauto.
    destruct (next_mode_dec s1 t i) as [[Hnextmd | Hnextmd] | Hnextmd];
      rewrite Hnextmd in Hact.
    - destruct r. eapply get_commute_response_correct; eauto.
      discriminate_noresp.
    - destruct r. eapply get_oracle_response_correct; eauto.
      discriminate_noresp.
    - destruct (rev (X_copy s1)).
      destruct r; [eapply get_replay_response_correct; eauto | discriminate_noresp].
      destruct l; destruct r; try discriminate_noresp.
      all: eapply get_replay_response_correct; eauto.
  Qed.    

End Correctness.

Section Conflict_Freedom.

  Lemma machine_reads_conflict_free :
    forall s h t i r,
      current_state_history s (h ++ X) ->
      spec ((t,i,NoResp) :: h ++ X) ->
      (exists h', reordered (h' ++ (t,i,r) :: h) Y) ->
      conflict_free_reads t i s.
  Proof.
    intros. unfold conflict_free_reads; intros.
    assert (md s = ConflictFree) as Hmds. 
    { destruct H1 as [h' HY].
      eapply mode_current_state_history_commute; eauto.
    } rewrite Hmds in *.
    pose (during_commute_state s (h++X) H Hmds).
    destruct_conjs.
    unfold machine_act in *. unfold next_mode in *.
    assert (h = H11) as tmp.
    {
      apply app_inv_tail in H15; auto.
    } rewrite tmp in *; clear tmp.
    assert (Y_copy s t = history_of_thread (H1 ++ [(t, i, r)]) t).
    {
      eapply (mode_current_state_history_commute); eauto.
    }
    rewrite H18 in *.
    destruct (history_of_thread_end H1 t i r) as [dummy tmp]; rewrite tmp in *; clear tmp.
    rewrite H6, H7, H2, H3, rev_unit in *.
    unfold action_invocation_eq in *; destruct i; repeat rewrite Nat.eqb_refl in *; simpl in *.
    unfold get_commute_response in *.
    unfold state_with_md in *; simpl in *.
    rewrite H2, H3, rev_unit in *.
    inversion H8; inversion H9; subst; simpl in *. auto.
  Qed.
           
  Lemma machine_writes_conflict_free :
    forall s s' h t i r,
      current_state_history s (h ++ X) ->
      spec ((t,i,NoResp) :: h ++ X) ->
      (exists h', reordered (h' ++ (t,i,r) :: h) Y) ->
      machine_act s t i = (s', (t,i,r)) ->
      conflict_free_writes t s s'.
  Proof.
    Ltac discriminate_Y_performed :=
      match goal with
      | [ n : (?t =? ?t0) = false |- (if _ then _ else Y_performed ?s ?t) <> ?h2 :: Y_performed ?s ?t] =>
        rewrite n; intuition; assert ([] ++ Y_performed s t = [h2] ++ Y_performed s t) as mytmp;
        [now simpl | apply app_inv_tail in mytmp; discriminate]
      | [ |- Y_performed ?s ?t <> ?h2 :: Y_performed ?s ?t] =>
        intuition; assert ([] ++ Y_performed s t = [h2] ++ Y_performed s t) as mytmp;
        [now simpl | apply app_inv_tail in mytmp; discriminate]
      | [|- ?h1 :: Y_performed ?s ?t <> ?h :: ?h1 :: Y_performed ?s ?t] =>
        intuition; assert ([] ++ h1 :: Y_performed s t = [h] ++ h1 :: Y_performed s t) as mytmp;
        [ now simpl | apply app_inv_tail in mytmp; discriminate]
      end.
    Ltac solve_tid_neq_ensembles :=
      match goal with
      | [ neq : ?x <> ?t, Hinc : Union tid ?a ?b ?x|- _] =>
        rewrite <- Nat.eqb_neq in *; inversion Hinc;
        unfold In in *; rewrite neq in *; intuition
      end.
    Ltac solve_tid_ensembles :=
      match goal with
      | [ |- Union tid ?a ?b = Singleton tid ?t ] =>
        assert (Same_set tid (Union tid a b) (Singleton tid t)) as HSS; [
          unfold Same_set; unfold Included; split; unfold In; intros x Hinc;
          destruct (Nat.eq_dec x t) as [eq | neq]; subst | idtac];
        [ constructor
        | solve_tid_neq_ensembles
        | apply Union_introl; unfold In in *; try rewrite Nat.eqb_refl; try discriminate_Y_performed
        | inversion Hinc as [Hinc']; rewrite Hinc' in *; intuition
        | now apply Extensionality_Ensembles in HSS]
      end.

    intros s s' h t i r Hgen Hspec [h' Hreordered] Hact.
    unfold conflict_free_writes.

    assert (md s = ConflictFree) as Hmds. 
    { 
      eapply mode_current_state_history_commute; eauto.
    } rewrite Hmds in *.
    pose (during_commute_state s (h++X) Hgen Hmds).
    destruct_conjs.
    unfold machine_act in *. unfold next_mode in *.
    assert (h = H0) as tmp.
    {
      apply app_inv_tail in H4; auto.
    } rewrite tmp in *; clear tmp.
    assert (Y_copy s t = history_of_thread (h' ++ [(t, i, r)]) t).
    {
      eapply (mode_current_state_history_commute); eauto.
    }
    destruct (history_of_thread_end h' t i r) as [dummy tmp]; rewrite tmp in *; clear tmp.
    rewrite Hmds, H6, rev_unit in *.
    unfold action_invocation_eq in *; destruct i; repeat rewrite Nat.eqb_refl in *; simpl in *.
    unfold get_commute_response in *.
    unfold state_with_md in *; simpl in *.
    rewrite H6, rev_unit in *.
    inversion Hact; simpl in *.
    unfold step_writes, write_tid_set in *; simpl in *.
    repeat (split; auto).
    solve_tid_ensembles.
  Qed.

End Conflict_Freedom.

Theorem scalable_commutativity_rule :
  (forall s h t i r,
      current_state_history s h ->
      spec h /\
      (List.In (t,i,r) h -> exists rtyp, r = Resp rtyp)) /\
  (forall s s' h t i r,
      current_state_history s (h ++ X) ->
      spec ((t,i,NoResp) :: h ++ X) ->
      (exists h', reordered (h' ++ (t,i,r) :: h) Y) ->
      machine_act s t i = (s', (t,i,r)) ->
      conflict_free_writes t s s'
      /\ conflict_free_reads t i s).
Proof.
  intros; split. split; [eapply machine_correct | eapply response_always_exists]; eauto.
  intros; split; [eapply machine_writes_conflict_free | eapply machine_reads_conflict_free]; eauto.
Qed.



