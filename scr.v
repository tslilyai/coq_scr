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
        simpl in *; apply reordered_refl.
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
                                  (state_with_md s1 Emulate) t i 0 max_response_number);
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
                                        md := Emulate |} t i 0 max_response_number);
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
            simpl in *; apply reordered_refl.
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
                                        md := Emulate |} t i 0 max_response_number);
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
                                        (state_with_md s1 Emulate) t (Inv i) 0 max_response_number);
                inversion H1; subst; unfold state_with_md in *; simpl in *; try discriminate;
                  try now eapply IHp.
              functional induction (get_emulate_response_helper
                                        (state_with_md s1 Emulate) ts1 (Inv i) 0 max_response_number);
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
            simpl in *; apply reordered_refl.
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
                                    (state_with_md s1 Emulate) t i 0 max_response_number);
            inversion H1; subst; unfold state_with_md in *; simpl in *; try discriminate;
              try now eapply IHp.

          clear IHs1ycpy.
          unfold get_commute_response, state_with_md in *; simpl in *.
          rewrite <- Heqs1ycpy, rev_unit in *.
          inversion H1; subst; simpl in *.
          repeat (split; auto).
          eapply (state_combined_histories_is_reordered_Y _ _ Hgen); simpl in *; eauto.
          exists ((t,i,r) :: H0); split; auto.
          admit.
          (*
          Lemma combined_histories_thread_order_preserved :
            forall f h0 h1 i' r' t,
              (forall t t' i' r', List.In (t',i',r') (f t) -> t' = t) ->
              combined_histories f = h0 ++ f t ++ h1 ->
              ~ List.In (t,i',r') h0 /\ ~ List.In (t,i',r') h1.              
          Proof.
            intros f h0 h1 i' r' t Hin. revert h0 h1 i' r' t.
            unfold combined_histories in *.
            functional induction (combine_tid_histories f num_threads); intros.
            Focus 2.

            remember (f (S t')) as fst'. 
            destruct (fst'); simpl in *. eapply IHl; eauto.
            assert (
                (exists h0hd h0tl, combine_tid_histories f t' = h0tl ++ f t ++ h1
                                       /\ f (S t') = h0hd /\ h0hd ++ h0tl = h0)
                    \/ (exists fthd fttl, combine_tid_histories f t' = fttl ++ h1
                                          /\ f (S t') = h0 ++ fthd /\ fthd ++ fttl = f t)
                    \/ (exists h1hd h1tl, combine_tid_histories f t' = h1tl
                                          /\ f (S t') = h0++ f t ++ h1hd /\ h1hd ++ h1tl = h1))
              as tmp.
            {
              remember (length (f (S t'))) as len.
              remember (combine_tid_histories f t') as combinedt'.
              destruct combinedt'. rewrite app_nil_r in *.
              rewrite <- Heqfst' in *.
              right; right. exists h1. exists []. rewrite app_nil_r. repeat split; auto.
              
              assert (exists l1 l2,
                         h0 ++ f t ++ h1 = 
                          l1 ++ nth len (f (S t') ++ combine_tid_histories f t') (t', i', NoResp)
                             :: l2
                         /\ length l1 = len).
              {
                rewrite <- H.
                rewrite <- Heqcombinedt', <- Heqfst'.
                eapply nth_split; eauto. rewrite <- Heqfst' in *. 
                rewrite Heqlen. simpl in *. rewrite app_length. simpl in *. omega.
              }
              admit.
            } destruct tmp as [Htmp | [Htmp | Htmp]]; destruct Htmp as [front [back Htmp]];
              destruct_conjs.
            pose (IHl back h1 i' r' t H0); destruct_conjs.
            assert (t' <> t).
            
            Print combine_tid_histories_ind.

          Lemma reordered_thread_order :
            forall f t i r h h1 h2,
              f t = ((t,i,r) :: h) ->
              (forall t t' i' r', List.In (t',i',r') (f t) -> t' = t) ->
              combined_histories f = h1 ++ (t,i,r) :: h2 -> 
              reordered ((t,i,r) :: h1 ++ h2) (combined_histories f).
          Proof.
            intros.
            assert (forall t' i' r', hd_error h1 = Some (t',i',r')
                                     -> swappable (t,i,r) (t',i',r')
                                        \/ (t = t' /\ i = i' /\ r = r')).
            intros. unfold swappable.
            unfold combined_histories in *.
            remember [] as acc in *.
            functional induction (combine_tid_histories f num_threads acc).
            - rewrite app_nil_r in *.
              assert (t = 0).
              {
                eapply H0. rewrite H1. apply in_or_app; right. apply in_eq.
              } 
              assert (t' = 0).
              {
                destruct h1; inversion H2.
                eapply H0; eauto. rewrite H1. apply in_or_app; left; eauto.
                rewrite H5; apply in_eq.

              } subst.
              right. split; auto.
              induction h1. inversion H2.
              inversion H2.
              rewrite H, H4 in H1.
              inversion H1; subst; auto.
            - rewrite app_nil_r in *.
              eapply IHl; eauto.
           *)  
     Admitted.

End State_Lemmas.

Section Existance.
      
  Lemma emulator_deterministic :
    forall s1 s2 s2' t i a a',
      emulator_act s1 t i = (s2, a) ->
      emulator_act s1 t i = (s2', a') ->
      s2 = s2' /\ a = a'.
  Proof.
    intros. rewrite H in H0; inversion H0; auto.
  Qed.

  Lemma generated_deterministic :
    forall s s' h,
      generated s h ->
      generated s' h ->
      s = s'.
  Proof.
    intros. revert s s' H H0.
    induction h; intros; inversion H; inversion H0; auto; subst.
    assert (s0 = s1) by now eapply (IHh s0 s1); eauto. rewrite H1 in *.
    inversion H7; subst.
    eapply emulator_deterministic; eauto.
  Qed.

  Lemma get_emulate_response_exists :
    forall s h t i md,
      generated (state_with_md s md) h ->
      spec ((t,i,NoResp)::h) ->
      exists rtyp s',
        get_emulate_response s t i = (s', (t,i,Resp rtyp)).
  Proof. Admitted.
    
  Lemma emulator_act_response_exists :
    forall s h t i,
      generated s h ->
      spec ((t,i,NoResp)::h) ->
      exists rtyp s',
        emulator_act s t i = (s', (t,i,Resp rtyp)).
  Proof.
    intros s h t i Hgen Hspec. revert dependent s. revert dependent t.
    revert dependent i.
    induction h; intros; inversion Hgen; subst.

    Ltac solve_emulate_response :=
      match goal with
      | [ Hgen : generated ?s ?h, Heqmds : ?md = md ?s |-
          exists rtyp s', get_emulate_response ?s0 ?t ?i = _ ] =>
        eapply get_emulate_response_exists; eauto;
        assert (generated (state_with_md s0 md) h) as HAH; [
          unfold state_with_md in *; simpl in *;
          destruct s; simpl in *; rewrite <- Heqmds in *; auto
        | apply HAH]
      | [|- exists rtyp s', get_emulate_response _ _ _ = _] =>
        eapply get_emulate_response_exists; eauto
      end.
    
    - unfold start_state in *; unfold start_mode in *; simpl in *.
      unfold emulator_act, next_mode.
      remember X as HX; destruct HX using rev_ind; simpl in *.
      remember (history_of_thread Y t) as Yhist.
      destruct (Yhist) using rev_ind; [|rewrite rev_unit]; unfold state_with_md; simpl in *.
      + solve_emulate_response.
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
        * solve_emulate_response.
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
          exists n; auto.
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
          exists n; auto.
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
        * solve_emulate_response.
    - unfold emulator_act.
      remember (next_mode s t i) as snextmd.
      rewrite Heqsnextmd.
      unfold emulator_act, next_mode in *; remember (md s) as mds; destruct mds.
      + remember (Y_copy s t) as sycpy. destruct sycpy using rev_ind; subst; simpl in *.
        * solve_emulate_response.
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
            eapply reordered_in. apply H.
            apply in_or_app; left.
            eapply history_of_thread_sublist; eauto.
            apply in_or_app; left; eauto.
          }
          destruct H as [rtyp bleh]; discriminate.
          solve_emulate_response.
      + solve_emulate_response.
      + remember (X_copy s) as sxcpy. destruct sxcpy using rev_ind; simpl in *; auto.
        * solve_emulate_response.
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
          exists n; auto.
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
          exists n; auto.
          assert (exists rtyp, NoResp = Resp rtyp) as ha.
          {
            eapply X_and_Y_wf.
            assert (List.In (tx, Inv ix, NoResp) X).
            rewrite <- H7, <- Heqsxcpy.
            apply in_or_app; left. apply in_or_app; right. apply in_eq.
            apply in_or_app; right; eauto.
          } destruct ha as [rtyp bleh]; discriminate.
          destruct H6 as [rtyp bleh]; rewrite bleh; eauto.

          solve_emulate_response.
  Qed.
  
  Lemma generated_response_exists :
    forall s h t i,
      generated s h ->
      spec ((t,i,NoResp)::h) ->
      exists rtyp s',
        generated s' ((t,i,Resp rtyp)::h).
  Proof.
    intros s h t i Hgen Hspec.
    destruct (emulator_act_response_exists _ _ _ _ Hgen Hspec) as [rtyp [s' Hact]].
    exists rtyp; exists s'; eapply GenCons; eauto.
  Qed.

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
    forall h s Yend Yfront t i r,
      generated s h ->
      h = Yend ++ X ->
      reordered (Yfront ++ (t,i,r) :: Yend) Y ->
      s.(md) = Commute.
  Proof.
    induction h; intros; inversion H; subst; simpl in *.
    - unfold start_mode in *. symmetry in H0; apply app_eq_nil in H0; destruct_conjs.
      rewrite H2 in *; auto.
    - 
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
    Ltac discriminate_commH :=
      match goal with
      | [ n : (?t =? ?t0) = false |- (if _ then _ else commH ?s ?t) <> ?h2 :: commH ?s ?t] =>
        rewrite n; intuition; assert ([] ++ commH s t = [h2] ++ commH s t) as mytmp;
        [now simpl | apply app_inv_tail in mytmp; discriminate]
      | [ |- commH ?s ?t <> ?h2 :: commH ?s ?t] =>
        intuition; assert ([] ++ commH s t = [h2] ++ commH s t) as mytmp;
        [now simpl | apply app_inv_tail in mytmp; discriminate]
      | [|- ?h1 :: commH ?s ?t <> ?h :: ?h1 :: commH ?s ?t] =>
        intuition; assert ([] ++ h1 :: commH s t = [h] ++ h1 :: commH s t) as mytmp;
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
        | apply Union_introl; unfold In in *; try rewrite Nat.eqb_refl; try discriminate_commH
        | inversion Hinc as [Hinc']; rewrite Hinc' in *; intuition
        | now apply Extensionality_Ensembles in HSS]
      end.
    
    intros s s' h t i r Hgen Hspec [h' Hreordered] Hact.
    unfold conflict_free_step.
    inversion Hgen; subst; unfold step_writes, write_tid_set in *; simpl in *.

    (* we've generated [] so far *)
    - unfold start_state, start_mode in *; destruct X; simpl in *;
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
        solve_tid_ensembles; discriminate.

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
              now eapply (mode_generated_replay _ s1 [] t0 i0 r0); eauto.
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
        repeat (split; auto); solve_tid_ensembles.

      (* X = [], h = a :: h *)
      + rewrite app_nil_r in *; rewrite <- H in *.
        (* figure out the state of s *)
        assert (md s1 = Commute) as Hs1md.
        {
          eapply (mode_generated_commute _ s1 h0 _ t0 i0 r0); eauto.
          rewrite <- HeqHX; rewrite app_nil_r; auto.
          assert ((h' ++ [(t,i,r)]) ++ (t0,i0,r0) :: h0 = (h'++ (t,i,r)::(t0,i0,r0)::h0)) as bleh.
          rewrite <- app_assoc. simpl in *; auto.
          rewrite bleh in *. auto.
        }
        destruct (during_commute_state s1 _ H3 Hs1md) as 
            [Hys1 [hist [Hpres1 [Hposts1 Hxcpys1]]]].
        destruct hist as [gencomm [Hgencomm Hgcorder]].
        rewrite <- HeqHX in *; rewrite app_nil_r in *; rewrite Hgencomm in *.
        unfold emulator_act in H0. unfold next_mode in H0. rewrite Hs1md in *.

        pose (state_ycpy_nonempty s1 (h' ++ [(t,i,r)]) [] t0 i0 r0 gencomm Hys1)
          as tmp; rewrite <- app_assoc in *; simpl in *.
        pose (tmp Hreordered Hgcorder) as Hs1ycpyt0. 

        pose (state_ycpy_nonempty s1 h' [(t0, i0, r0)] t i r gencomm Hys1)
          as tmp'; simpl in *.
        pose (tmp' Hreordered Hgcorder) as Hs1ycpyt. 

        rewrite Hs1ycpyt0 in H0; rewrite rev_unit in *; 
          simpl in *; destruct i0; simpl in *.
        repeat rewrite Nat.eqb_refl in *; simpl in *.
        unfold get_commute_response in *; simpl in *.
        rewrite Hs1ycpyt0 in *; rewrite rev_unit in *; inversion H0; subst; simpl in *.
        unfold emulator_act in *; unfold next_mode in *; simpl in *.
        destruct (Nat.eq_dec t t0); subst; rewrite rev_involutive in *.

        (* t = t0 *)
        * rewrite history_of_thread_app_distributes in Hact; simpl in *;
            rewrite Nat.eqb_refl in *; rewrite rev_unit in *; simpl in *; destruct i; simpl in *;
              repeat rewrite Nat.eqb_refl in *; simpl in *.
          unfold get_commute_response, state_with_md in *; simpl in *.
          rewrite Nat.eqb_refl in *; rewrite rev_unit in *. inversion Hact; subst; simpl in *.
          repeat (split; auto).
          solve_tid_ensembles.

        (* t <> t0 *)
        * rewrite <- Nat.eqb_neq in *; rewrite n0 in *.
          rewrite Hs1ycpyt in *.
          rewrite Nat.eqb_sym in n0; rewrite n0 in *.
          rewrite rev_unit in *.
          unfold state_with_md in *; simpl in *.

          destruct i; simpl in *.
          repeat rewrite Nat.eqb_refl in *; simpl in *.
          inversion Hact; subst.
          unfold get_commute_response, state_with_md in *; simpl in *.
          rewrite Hs1ycpyt in *; rewrite Nat.eqb_sym in n0; rewrite n0, rev_unit in *.
          inversion H4; subst; simpl in *.
          repeat (split; auto).
          solve_tid_ensembles.
    
      (* X = a :: HX and h = b :: h' *)
      + inversion H; subst; clear H.
        (* figure out the state of s *)
        assert (md s1 = Commute) as Hs1md.
        {
          eapply (mode_generated_commute _ s1 h _ t0 i0 r0); eauto.
          rewrite <- HeqHX; auto.
          assert ((h' ++ [(t,i,r)]) ++ (t0,i0,r0) :: h  = (h'++ (t,i,r)::(t0,i0,r0)::h)) as bleh.
          rewrite <- app_assoc. simpl in *; auto.
          rewrite bleh in *. auto.
        }
        destruct (during_commute_state s1 _ H3 Hs1md) as [Hys1 [hist [Hpres1 [Hposts1 Hxcpys1]]]].
        destruct hist as [gencomm [Hgencomm Hgcorder]].
        rewrite <- HeqHX in *; rewrite Hgencomm in *.
        unfold emulator_act in H0. unfold next_mode in H0. rewrite Hs1md in *.
        apply app_inv_tail in Hgencomm; subst.
        pose (state_ycpy_nonempty s1 (h' ++ [(t,i,r)]) [] t0 i0 r0 gencomm Hys1)
          as tmp; rewrite <- app_assoc in *; simpl in *.
        pose (tmp Hreordered Hgcorder) as Hs1ycpyt0. 

        pose (state_ycpy_nonempty s1 h' [(t0, i0, r0)] t i r gencomm Hys1)
          as tmp'; simpl in *.
        pose (tmp' Hreordered Hgcorder) as Hs1ycpyt. 

        rewrite Hs1ycpyt0 in H0; rewrite rev_unit in *; 
          simpl in *; destruct i0; simpl in *.
        repeat rewrite Nat.eqb_refl in *; simpl in *.
        unfold get_commute_response in *; simpl in *.
        rewrite Hs1ycpyt0 in *; rewrite rev_unit in *; inversion H0; subst; simpl in *.
        unfold emulator_act in *; unfold next_mode in *; simpl in *.
        destruct (Nat.eq_dec t t0); subst; rewrite rev_involutive in *.

        (* t = t0 *)
        * rewrite history_of_thread_app_distributes in Hact; simpl in *;
            rewrite Nat.eqb_refl in *; rewrite rev_unit in *; simpl in *; destruct i; simpl in *;
              repeat rewrite Nat.eqb_refl in *; simpl in *.
          unfold get_commute_response, state_with_md in *; simpl in *.
          rewrite Nat.eqb_refl in *; rewrite rev_unit in *. inversion Hact; subst; simpl in *.
          repeat (split; auto).
          solve_tid_ensembles.

        (* t <> t0 *)
        * rewrite <- Nat.eqb_neq in *; rewrite n0 in *.
          rewrite Hs1ycpyt in *.
          rewrite Nat.eqb_sym in n0; rewrite n0 in *.
          rewrite rev_unit in *.
          unfold state_with_md in *; simpl in *.

          destruct i; simpl in *.
          repeat rewrite Nat.eqb_refl in *; simpl in *.
          inversion Hact; subst.
          unfold get_commute_response, state_with_md in *; simpl in *.
          rewrite Hs1ycpyt in *; rewrite Nat.eqb_sym in n0; rewrite n0, rev_unit in *.
          inversion H2; subst; simpl in *.
          repeat (split; auto).
          solve_tid_ensembles.
  Qed.

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

