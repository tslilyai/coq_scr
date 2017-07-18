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
          destruct (rev (Y_copy s1 t));
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
      forall s h t,
        generated s h ->
        s.(md) = Commute ->
        reordered (combined_histories s.(Y_copy) ++ combined_histories s.(commH)) Y /\
        (exists gencomm, h = gencomm ++ X /\ reordered gencomm (combined_histories s.(commH))) /\
        s.(Y_copy) t ++ s.(commH) t = history_of_thread Y t /\
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
      intros. unfold emulator_act in *. unfold next_mode in *.
      rewrite H in *.
      unfold get_emulate_response in *.
      functional induction (get_emulate_response_helper (state_with_md s Emulate)
                                                        t i 0 max_response_number); eauto.
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
      pose (during_commute_state s' ((t,i,Resp rtyp)::h) t Hgens' Hmds') as Hstates';
      pose (reordered_Y_prefix_correct) as HY;
      destruct Hstates' as [Hreordered [[gencomm [Hrespeq Hgencommorder]] [HHistory rest]]];
      apply reordered_sym in Hgencommorder;
      pose (reordered_prefix _ _ _ _ Hreordered Hgencommorder) as HYorder;
      apply HY in HYorder;
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

  Lemma history_of_thread_nonempty :
    forall h' t i r h,
      reordered (h' ++ (t, i, r) :: h) Y ->
      history_of_thread Y t = history_of_thread h' t ++ (t,i,r) :: history_of_thread h t.
  Proof.
  Admitted.    

  Lemma history_of_thread_reordered_eq :
    forall h h' t,
      reordered h h' ->
      history_of_thread h' t = history_of_thread h t.
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
        assert (action_invocation_eq x t i = true) as Heq.
        {
          pose (history_of_thread_nonempty _ _ _ _ _ Hreordered) as Hnonempty;
          simpl in *.
          rewrite Hnonempty in *; simpl in *.
          assert (rev (Yhist ++ [x]) = rev ((history_of_thread h' t) ++ [(t,i,r)])).
          rewrite HeqYhist; simpl in *; auto.
          repeat rewrite rev_unit in *. destruct x as [[t' [i']] r'].
          inversion H; subst; auto.
          unfold action_invocation_eq; simpl in *; repeat rewrite <- beq_nat_refl; auto.
        }
        rewrite Heq in *.
        unfold get_commute_response in *; unfold state_with_md in *; simpl in *.
        rewrite <- HeqYhist in *; try rewrite rev_unit in *.
        inversion Hact; subst; simpl in *; repeat (split; auto).

        (* tid stuff *)
        assert (Same_set tid
                         (Union tid (fun tid0 : tid => [] <> (if tid0 =? t then [(t, i, r)]
                                                              else []))
                                (fun tid0 : tid =>
                                   history_of_thread Y tid0 <>
                                   (if tid0 =? t then rev (rev Yhist)
                                    else history_of_thread Y tid0)))
                          (Singleton tid t)) as HSS.
        {
          unfold Same_set; unfold Included; split; unfold In;
            intros x Hinc; destruct (Nat.eq_dec x t); subst.
          - constructor. 
          - inversion Hinc; unfold In in *; rewrite <- Nat.eqb_neq in *; rewrite n in *;
            intuition.
          - apply Union_introl; unfold In in *. rewrite Nat.eqb_refl.
            intuition. discriminate.
          - inversion Hinc. rewrite H in *; intuition.
        }
        now apply Extensionality_Ensembles in HSS.

      (* X = a :: h *)
      + pose (app_cons_not_nil h h0 a). contradiction.

    (* we've generated some history a::h so far *)
    - remember X as HX. destruct h; destruct HX; try rewrite <- HeqHX in *; simpl in *;
                          unfold step_writes.
      (* h, X = [] *)
      + symmetry in H. pose (nil_cons H); discriminate.
      (* h = [], X = a :: hx *)
      + inversion H; subst.

        (* figure out the state of s *)
        assert (md s1 = Replay) as Hs1md by
              now eapply (mode_generated_replay s1 _ [] t0 i0 r0); eauto.
        destruct (during_replay_state s1 _ H3 Hs1md) as
            [Hpres1 [Hposets1 [Hcomms1 [Hycpys1 [Xend [Hh' Hxcpys1]]]]]].
        assert (Xend = [(t0, i0, r0)]) as HeqXend.
        {
          rewrite <- Hh' in HeqHX.
          assert ((t0,i0,r0) :: HX = [(t0,i0,r0)] ++ HX) as tmp by now simpl in *.
          repeat rewrite tmp in *. rewrite <- H in *.
          apply app_inv_tail in HeqHX; auto.
        }
        subst. unfold emulator_act in H0.
        unfold next_mode in H0; rewrite Hs1md in *. rewrite HeqXend in *.
        simpl in *. destruct i0; simpl in *.
        repeat rewrite Nat.eqb_refl in *; simpl in *.
        unfold get_replay_response in *.
        assert (X_copy (state_with_md s1 Commute) = X_copy s1) as Htmp
            by now eapply state_with_md_comp_eq.
        rewrite Htmp, HeqXend in *; simpl in *.
        inversion H0; subst; simpl in *.
        
        (* now figure out the state of s' *)        
        unfold emulator_act in *; unfold next_mode in *; simpl in *.
        rewrite Hycpys1 in *.
        pose (history_of_thread_nonempty _ _ _ _ _ Hreordered) as HYhist.
        rewrite HYhist in *. rewrite rev_unit in *.
        destruct i; simpl in *. repeat rewrite Nat.eqb_refl in *; simpl in *.
        unfold get_commute_response in *; simpl in *.
        rewrite HYhist in *; rewrite rev_unit in *; simpl in *.
        inversion Hact; subst; simpl in *.
        repeat (split; auto).

        unfold write_tid_set.
        assert (Same_set tid
                         (Union tid
                                (fun tid0 : tid =>
                                   commH s1 tid0 <>
                                   (if tid0 =? t then (t, Inv n0, r) :: commH s1 t
                                    else commH s1 tid0))
                                (fun tid0 : tid =>
                                   history_of_thread Y tid0 <>
                                   (if tid0 =? t then rev (rev (history_of_thread h' t))
                                    else history_of_thread Y tid0)))
                         (Singleton tid t)) as HSS.
        {
          unfold Same_set; unfold Included; split; unfold In;
            intros x Hinc; destruct (Nat.eq_dec x t); subst.
          - constructor. 
          - inversion Hinc; unfold In in *; rewrite <- Nat.eqb_neq in *; rewrite n1 in *;
            intuition.
          - apply Union_introl; unfold In in *. rewrite Nat.eqb_refl.
            intuition. assert ([] ++ commH s1 t = [(t,Inv n0, r)] ++ commH s1 t) by now simpl.
            apply app_inv_tail in H4. discriminate.
          - inversion Hinc. rewrite H2 in *; intuition.
        }
        now apply Extensionality_Ensembles in HSS.

      (* X = [], h = a :: h *)
      + rewrite app_nil_r in *; rewrite <- H in *.
        (* figure out the state of s *)
        assert (md s1 = Commute) as Hs1md.
        {
          eapply (mode_generated_commute s1 _ h0 _ t0 i0 r0); eauto.
          rewrite <- HeqHX; rewrite app_nil_r; auto.
          assert ((h' ++ [(t,i,r)]) ++ (t0,i0,r0) :: h0 = (h'++ (t,i,r)::(t0,i0,r0)::h0)) as bleh.
          rewrite <- app_assoc. simpl in *; auto.
          rewrite bleh in *. auto.
        }
        destruct (during_commute_state s1 _ t H3 Hs1md) as 
            [Hys1 [hist [HYcomm [Hpres1 [Hposts1 Hxcpys1]]]]].
        destruct hist as [gencomm [Hgencomm Hgcorder]].
        rewrite <- HeqHX in *; rewrite app_nil_r in *; rewrite Hgencomm in *.
        unfold emulator_act in H0. unfold next_mode in H0. rewrite Hs1md in *.
        assert (exists history, rev (Y_copy s1 t0) = (t0,i0,r0) :: history) as Hs1ycpyt0.
        {
          assert (reordered (h' ++ (t,i,r) :: (t0,i0,r0) :: []) (combined_histories (Y_copy s1))).
          {
            eapply reordered_app_inv_prefix; eauto. eapply ro_perm_trans; eauto.
            rewrite <- app_assoc.
            apply Hreordered.
            apply reordered_sym; auto.
          }
          assert (history_of_thread
                    (combined_histories (Y_copy s1) ++ combined_histories (commH s1)) t
                  = history_of_thread Y t) as Ht1.
          {
            eapply history_of_thread_reordered_eq; eauto. apply reordered_sym; auto.
          }
          assert (history_of_thread
                    (h' ++ (t, i, r) :: (t0, i0, r0) :: gencomm) t
                  = history_of_thread Y t) as Ht2.
          {
            eapply history_of_thread_reordered_eq; eauto. apply reordered_sym; auto.
          }
          Lemma history_of_thread_app_distributes :
            forall h h' t,
              history_of_thread (h ++ h') t = history_of_thread h t ++ history_of_thread h' t.
          Proof. Admitted.

          Lemma history_of_thread_combined_is_application :
            forall (f : state -> tid -> history) s t,
              history_of_thread (combined_histories (f s)) t = f s t.
          Proof. Admitted.

          rewrite history_of_thread_app_distributes in Ht1.
          repeat rewrite history_of_thread_combined_is_application in Ht1.
          rewrite <- Ht2 in Ht1.
          unfold history_of_thread in Ht1. simpl in *.
          
        }
          
          admit.
        }
        destruct Hs1ycpyt0 as [history Hs1ycpyt0].
        rewrite Hs1ycpyt0 in H0; simpl in *; destruct i0; simpl in *.
        repeat rewrite Nat.eqb_refl in *; simpl in *.
        unfold get_commute_response in *; simpl in *.
        rewrite Hs1ycpyt0 in *. inversion H0; subst; simpl in *.

        (* now figure out the state of s' *)
        assert (exists history', Y_copy s1 t = history' ++ [(t,i,r)]) as Hs1ycpyt.
        {
          admit.
        }
        unfold emulator_act in *; unfold next_mode in *; simpl in *.
        destruct (Nat.eq_dec t t0); subst; [rewrite Nat.eqb_refl in *
                                           | rewrite <- Nat.eqb_neq in *; rewrite n0 in *].
        (* if t = t0 *)
        * assert (exists posthist, history = (t0,i,r)::posthist) as Hhist.
          {
            admit.
          }
          destruct Hhist as [posthist Hhist].
          rewrite Hhist in Hact. rewrite rev_involutive in *; simpl in *.
          destruct i; simpl in *.
          repeat rewrite Nat.eqb_refl in *; simpl in *.
          unfold get_commute_response, state_with_md in *; simpl in *.
          rewrite Nat.eqb_refl in *; rewrite rev_unit in *. inversion Hact; subst; simpl in *.
          repeat (split; auto).

          unfold write_tid_set.
          assert (Same_set tid
                      (Union tid
                      (fun tid0 : tid =>
                         (if tid0 =? t0 then (t0, Inv n, r0) :: commH s1 t0 else commH s1 tid0) <>
                         (if tid0 =? t0 then (t0, Inv n0, r) :: (t0, Inv n, r0) :: commH s1 t0
                          else if tid0 =? t0 then (t0, Inv n, r0) :: commH s1 t0
                               else commH s1 tid0))
                      (fun tid0 : tid =>
                         (if tid0 =? t0 then rev posthist ++ [(t0, Inv n0, r)]
                          else Y_copy s1 tid0) <>
                         (if tid0 =? t0 then rev (rev (rev posthist))
                          else if tid0 =? t0 then rev posthist ++ [(t0, Inv n0, r)]
                               else Y_copy s1 tid0)))
                      (Singleton tid t0)) as HSS.
          {
            unfold Same_set; unfold Included; split; unfold In;
              intros x Hinc; destruct (Nat.eq_dec x t0); subst.
            - constructor. 
            - inversion Hinc; unfold In in *; rewrite <- Nat.eqb_neq in *; rewrite n1 in *;
                intuition.
            - apply Union_introl; unfold In in *. rewrite Nat.eqb_refl.
              intuition. assert ([] ++ (t0,Inv n, r0) :: commH s1 t0
                                 = [(t0,Inv n0, r)] ++ (t0, Inv n, r0) :: commH s1 t0) by now simpl.
              apply app_inv_tail in H4. discriminate.
            - inversion Hinc. rewrite H2 in *; intuition.
          }
          now apply Extensionality_Ensembles in HSS.
        (* if t <> t0 *)
        * destruct Hs1ycpyt as [history' Hs1ycpyt].
          rewrite Hs1ycpyt in *. rewrite rev_unit in *; simpl in *.
          destruct i; simpl in *.
          repeat rewrite Nat.eqb_refl in *; simpl in *.
          inversion Hact; subst.
           unfold get_commute_response, state_with_md in *; simpl in *.
           rewrite n0 in *. rewrite Hs1ycpyt in *. rewrite rev_unit in *.
           inversion H4; subst; simpl in *.
          repeat (split; auto).

          unfold write_tid_set.
          assert (Same_set tid
                           (Union tid (fun tid0 : tid =>
                                         (if tid0 =? t0 then (t0, Inv n, r0) :: commH s1 t0
                                          else commH s1 tid0) <>
                                         (if tid0 =? t
                                          then (t, Inv n1, r) :: commH s1 t
                                          else if tid0 =? t0 then (t0, Inv n, r0) :: commH s1 t0
                                               else commH s1 tid0))
                                  (fun tid0 : tid =>
                                     (if tid0 =? t0 then rev history else Y_copy s1 tid0) <>
                                     (if tid0 =? t then rev (rev history')
                                      else if tid0 =? t0 then rev history else Y_copy s1 tid0)))
                           (Singleton tid t)) as HSS.
          {
            unfold Same_set; unfold Included; split; unfold In;
              intros x Hinc; destruct (Nat.eq_dec x t); subst.
            - constructor. 
            - inversion Hinc; unfold In in *; rewrite <- Nat.eqb_neq in *; rewrite n2 in *; subst.
              all: destruct (Nat.eq_dec x t0); subst; [
                rewrite Nat.eqb_refl in *
              | rewrite <- Nat.eqb_neq in n3; rewrite n3 in *]; 
                intuition.
            - apply Union_introl; unfold In in *. rewrite Nat.eqb_refl.
              intuition. rewrite n0 in *.
              assert ([] ++ commH s1 t = [(t,Inv n1, r)] ++ commH s1 t) by now simpl.
              apply app_inv_tail in H5. discriminate.
            - inversion Hinc. rewrite H2 in *; intuition.
          }
          now apply Extensionality_Ensembles in HSS.

      (* X = a :: HX and h = b :: h' *)
      + inversion H; subst; clear H.
        (* figure out the state of s *)
        assert (md s1 = Commute) as Hs1md.
        {
          eapply (mode_generated_commute s1 _ h _ t0 i0 r0); eauto.
          rewrite <- HeqHX; auto.
          assert ((h' ++ [(t,i,r)]) ++ (t0,i0,r0) :: h  = (h'++ (t,i,r)::(t0,i0,r0)::h)) as bleh.
          rewrite <- app_assoc. simpl in *; auto.
          rewrite bleh in *. auto.
        }
        destruct (during_commute_state s1 _ H3 Hs1md) as 
            [Hys1 [hist [Hpres1 [Hposts1 Hxcpys1]]]].
        destruct hist as [gencomm [Hgencomm Hgcorder]].
        rewrite <- HeqHX in *; rewrite Hgencomm in *.
        unfold emulator_act in H0. unfold next_mode in H0. rewrite Hs1md in *.
        assert (exists history, rev (Y_copy s1 t0) = (t0,i0,r0) :: history) as Hs1ycpyt0.
        {
          admit.
        }
        destruct Hs1ycpyt0 as [history Hs1ycpyt0].
        rewrite Hs1ycpyt0 in H0; simpl in *; destruct i0; simpl in *.
        repeat rewrite Nat.eqb_refl in *; simpl in *.
        unfold get_commute_response in *; simpl in *.
        rewrite Hs1ycpyt0 in *. inversion H0; subst; simpl in *.

        (* now figure out the state of s' *)
        assert (exists history', Y_copy s1 t = history' ++ [(t,i,r)]) as Hs1ycpyt.
        {
          admit.
        }
        unfold emulator_act in *; unfold next_mode in *; simpl in *.
        destruct (Nat.eq_dec t t0); subst; [rewrite Nat.eqb_refl in *
                                           | rewrite <- Nat.eqb_neq in *; rewrite n0 in *].
        (* if t = t0 *)
        * assert (exists posthist, history = (t0,i,r)::posthist) as Hhist.
          {
            admit.
          }
          destruct Hhist as [posthist Hhist].
          rewrite Hhist in Hact. rewrite rev_involutive in *; simpl in *.
          destruct i; simpl in *.
          repeat rewrite Nat.eqb_refl in *; simpl in *.
          unfold get_commute_response, state_with_md in *; simpl in *.
          rewrite Nat.eqb_refl in *; rewrite rev_unit in *. inversion Hact; subst; simpl in *.
          repeat (split; auto).

          unfold write_tid_set.
          assert (Same_set tid
                      (Union tid
                      (fun tid0 : tid =>
                         (if tid0 =? t0 then (t0, Inv n, r0) :: commH s1 t0 else commH s1 tid0) <>
                         (if tid0 =? t0 then (t0, Inv n0, r) :: (t0, Inv n, r0) :: commH s1 t0
                          else if tid0 =? t0 then (t0, Inv n, r0) :: commH s1 t0
                               else commH s1 tid0))
                      (fun tid0 : tid =>
                         (if tid0 =? t0 then rev posthist ++ [(t0, Inv n0, r)]
                          else Y_copy s1 tid0) <>
                         (if tid0 =? t0 then rev (rev (rev posthist))
                          else if tid0 =? t0 then rev posthist ++ [(t0, Inv n0, r)]
                               else Y_copy s1 tid0)))
                      (Singleton tid t0)) as HSS.
          {
            unfold Same_set; unfold Included; split; unfold In;
              intros x Hinc; destruct (Nat.eq_dec x t0); subst.
            - constructor. 
            - inversion Hinc; unfold In in *; rewrite <- Nat.eqb_neq in *; rewrite n1 in *;
                intuition.
            - apply Union_introl; unfold In in *. rewrite Nat.eqb_refl.
              intuition. assert ([] ++ (t0,Inv n, r0) :: commH s1 t0
                                 = [(t0,Inv n0, r)] ++ (t0, Inv n, r0) :: commH s1 t0) as tmp by now simpl.
              apply app_inv_tail in tmp. discriminate.
            - inversion Hinc. rewrite H in *; intuition.
          }
          now apply Extensionality_Ensembles in HSS.
        (* if t <> t0 *)
        * destruct Hs1ycpyt as [history' Hs1ycpyt].
          rewrite Hs1ycpyt in *. rewrite rev_unit in *; simpl in *.
          destruct i; simpl in *.
          repeat rewrite Nat.eqb_refl in *; simpl in *.
          inversion Hact; subst.
           unfold get_commute_response, state_with_md in *; simpl in *.
           rewrite n0 in *. rewrite Hs1ycpyt in *. rewrite rev_unit in *.
           inversion H2; subst; simpl in *.
          repeat (split; auto).

          unfold write_tid_set.
          assert (Same_set tid
                           (Union tid (fun tid0 : tid =>
                                         (if tid0 =? t0 then (t0, Inv n, r0) :: commH s1 t0
                                          else commH s1 tid0) <>
                                         (if tid0 =? t
                                          then (t, Inv n1, r) :: commH s1 t
                                          else if tid0 =? t0 then (t0, Inv n, r0) :: commH s1 t0
                                               else commH s1 tid0))
                                  (fun tid0 : tid =>
                                     (if tid0 =? t0 then rev history else Y_copy s1 tid0) <>
                                     (if tid0 =? t then rev (rev history')
                                      else if tid0 =? t0 then rev history else Y_copy s1 tid0)))
                           (Singleton tid t)) as HSS.
          {
            unfold Same_set; unfold Included; split; unfold In;
              intros x Hinc; destruct (Nat.eq_dec x t); subst.
            - constructor. 
            - inversion Hinc; unfold In in *; rewrite <- Nat.eqb_neq in *; rewrite n2 in *; subst.
              all: destruct (Nat.eq_dec x t0); subst; [
                rewrite Nat.eqb_refl in *
              | rewrite <- Nat.eqb_neq in n3; rewrite n3 in *]; 
                intuition.
            - apply Union_introl; unfold In in *. rewrite Nat.eqb_refl.
              intuition. rewrite n0 in *.
              assert ([] ++ commH s1 t = [(t,Inv n1, r)] ++ commH s1 t) as tmp by now simpl.
              apply app_inv_tail in tmp. discriminate.
            - inversion Hinc. rewrite H in *; intuition.
          }
          now apply Extensionality_Ensembles in HSS.
  Admitted.

  Theorem scalable_commutativity_rule :
    (forall s h t i r,
       generated s h ->
       spec h /\
       (List.In (t,i,r) h -> exists rtyp, r = Resp rtyp)) /\
    (forall s s' h t i r,
      generated s (h ++ X) ->
      spec ((t,i,NoResp) :: h ++ X) ->
      (exists h', reordered (h' ++ (t,i,r) :: h) Y) ->
      emulator_act s t i = (s', (t,i,r)) ->
      conflict_free_step t s s').
  Proof.
    intros; split. split; [eapply emulator_correct | eapply response_always_exists]; eauto.
    eapply emulator_conflict_free; eauto.
  Qed.
  
End SCR.