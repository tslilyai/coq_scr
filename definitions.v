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
  Definition Y : history := [].
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
  Definition get_state_history (s : state) := s.(postH) ++ s.(preH). (*
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
           | 0 => (mkState s.(X_copy) s.(Y_copy) s.(preH)
                   s.(commH) s.(postH) Emulate, (t, i, NoResp)) (* should never reach this *)
           | S n' => get_emulate_response_helper s t i (S rtyp) n'
         end.
  Definition get_emulate_response (s : state) (t: tid) (i : invocation) : state * action :=
    get_emulate_response_helper s t i 0 max_response_number.
  Definition get_commute_response (s : state) (t: tid) (i: invocation) : state * action :=
    match rev (s.(Y_copy) t) with
      | [] => get_emulate_response s t i
      | hd::tl => if action_invocation_eq hd t i
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
      | hd::tl => if action_invocation_eq hd t i
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
      s.(postH) ++ s.(preH) = h.
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
      | [ H : (_, (?t, ?i, NoResp)) = (_, ?a'),
              Hgen : generated ?s ?h,
                     Hspec : spec _,
                           Hact : emulator_act ?s ?t ?i = (?s', ?a') |- _ ] =>
      let M := fresh "SO" in
      assert (exists rtyp, a' = (t, i, Resp rtyp)) as M; [
           now apply (response_always_exists s h t i s' a') |
          destruct M as [rtyp_new M] ; subst; discriminate ] end.

  Lemma inv_of_action_eq : forall a t i r,
    a = (t, i, r) ->
    action_invocation_eq a t i = true.
  Proof.
    intros. unfold action_invocation_eq; subst. destruct i; repeat rewrite Nat.eqb_refl. auto. 
  Qed.

  Lemma action_eq_dec : forall (a b : action), {a = b} + {a <> b}.
  Proof.
    intros [[t [i]] r] [[t' [i']] r'].
    destruct r, r', (Nat.eq_dec t t'), (Nat.eq_dec i i'); try destruct (Nat.eq_dec n n0); subst.
    all : try (right; intuition; try apply n; try apply n1;
              try inversion H2; try inversion H; auto; fail).
    all : now left.
  Qed.

  Lemma history_eq_dec : forall (h1 h2 : history), {h1 = h2} + {h1 <> h2}.
  Proof.
    apply (list_eq_dec action_eq_dec).
  Qed.

  Lemma emulator_act_replay :
    forall s0 t i s a,
      emulator_act s0 t i = (s, a) ->
      s.(md) = Replay ->
      s0.(md) = Replay.
  Proof.
    intros s0 t i s a Hact Hmd.
    unfold emulator_act in Hact.
    destruct (md s0).
    - unfold get_commute_response in Hact. admit.
    - unfold get_emulate_response in Hact.
      functional induction (get_emulate_response_helper s0 t i 0 max_response_number);
        inversion Hact; subst; simpl in *; try discriminate.
      apply IHp in H0; auto.
    - auto.
  Admitted.

  Lemma replay_state_correct : forall s h,
    generated s h ->
    md s = Replay ->
    s.(preH) = h /\
    s.(postH) = [] /\
    exists h', h' ++ h = X /\
               s.(X_copy) = h'.
  Proof.
    intros s h Hgen Hmd. generalize dependent s.
    induction h; intros; inversion Hgen; subst; auto.
    - unfold start_state; simpl; repeat (split; auto).
      exists X; split; [apply app_nil_r | ]; auto.
    - assert (md s1 = Replay) as Hmds1 by now eapply emulator_act_replay; eauto.
      pose (IHh s1 H3 Hmds1) as IH; destruct IH as [Hpres1 [Hposts1 [h' [HeqX Hxcpys1]]]].
      unfold emulator_act in H2. rewrite Hmds1 in H2.
      unfold get_replay_response in H2; simpl in *.
      rewrite Hxcpys1 in H2; simpl in *.
      induction h' using rev_ind; subst; simpl in *.
      admit.

      rewrite rev_unit in H2.
      destruct (action_invocation_eq x t i); subst; auto.
      inversion H2; simpl in *; repeat (split; auto).
      exists h'; rewrite <- H1; rewrite <- app_assoc in HeqX; split; auto.
      now rewrite rev_involutive.
      unfold get_emulate_response in H2.
      functional induction (get_emulate_response_helper s1 t i 0 max_response_number);
        inversion H2; subst; simpl in *; try discriminate.
      apply (IHp H0).
  Admitted.
    
  Lemma get_commute_response_correct : Prop. Admitted.

  Lemma get_replay_response_correct :
    forall h1 h2 s s' a' t i r,
      h1 ++ (t,i,r) :: h2 = X ->
      generated s h2 ->
      emulator_act s t i = (s', a') ->
      s.(md) = Replay /\ s.(preH) = h2 /\ s.(X_copy) = h1 ++ [(t,i,r)] /\
      s'.(md) = Replay /\ s'.(preH) = (t,i,r)::h2 /\ s'.(X_copy) = h1 /\
      a' = (t,i,r) /\ spec ((t,i,r) :: h2)
     /\ s'.(postH) = [] /\ s.(postH) = [].
  Proof.
    assert (spec X) as HspecX.
    { eapply (spec_prefix_closed (Y++X) X Y); eauto. apply X_and_Y_in_spec. }
    intros h1 h2 s s' a' t i r HX Hgen Hact.
    generalize dependent t. generalize dependent i. generalize dependent r.
    generalize dependent h1. generalize dependent s. generalize dependent s'.
    generalize dependent a'.
    remember (length h2) as Hlen. generalize dependent h2.
    induction (Hlen); intros.
    - destruct h2; try discriminate.
      inversion Hgen; subst.
      unfold emulator_act in Hact.
      unfold start_state in Hact; simpl in *.
      unfold get_replay_response in Hact. simpl in *.
      rewrite <- HX in Hact; simpl in *.
      rewrite rev_unit in Hact.
      rewrite (inv_of_action_eq (t,i,r) t i r) in Hact.

      repeat (split; auto); inversion Hact; auto; simpl.
      apply rev_involutive.
      eapply spec_prefix_closed. apply HspecX. symmetry in HX; apply HX.
      auto.

    - assert (exists a h, h2 = a :: h) as Hnotnil.
      { destruct h2. inversion HeqHlen. exists p; exists h2; auto. }
      destruct Hnotnil as [a [h Hnotnil]].
      rewrite Hnotnil in Hgen. inversion Hgen; subst.
      assert (generated s1 h) as Hgenprefix by auto.
      assert (n = length h) as Hlenh by now inversion HeqHlen.
      assert ((h1 ++ [(t, i, r)]) ++ (t0, i0, r0) :: h = X) as HX' by
            now rewrite <- app_assoc. 
      pose (IHn h Hlenh (t0, i0, r0) s s1 Hgenprefix (h1 ++ [(t,i,r)]) r0 i0 t0 HX' H2)
        as Hhyp.
      destruct Hhyp as [Hs1md [Hs1pre [Hs1cpy [Hsmd [Hspre
                                                       [Hscpy [Dumb [Hspec [Hnils Hnils1]]]]]]]]].
      unfold emulator_act in Hact. rewrite Hsmd in Hact.
      unfold get_replay_response in Hact; simpl in *.
      rewrite Hscpy in Hact; simpl in *.
      rewrite rev_unit in Hact.
      rewrite (inv_of_action_eq (t,i,r) t i r) in Hact.

      repeat (split; auto); inversion Hact; auto; simpl.
      rewrite Hspre. auto.
      apply rev_involutive.
      eapply spec_prefix_closed. apply HspecX. symmetry in HX; apply HX.
      auto. 
  Qed.

  Lemma get_diverge_response_correct :
    forall h1 h2 t t' i i' r s s' a',
      h1 ++ (t,i,r) :: h2 = X ->
      generated s h2 ->
      (t <> t' \/ i <> i') ->
      spec ((t',i',NoResp) :: h2) ->
      emulator_act s t' i' = (s', a') ->
      s.(md) = Replay /\ s.(preH) = h2
      /\ s.(X_copy) = h1 ++ [(t,i,r)]
      /\ s'.(md) = Emulate
      /\ s'.(preH) = s.(preH)
      /\ (exists rtyp, a' = (t',i',Resp rtyp))
      /\ spec (a' :: h2).
  Proof.
    intros h1 h2 t t' i i' r s s' a' HX Hgen Hdiff Hspec Hact.
    pose Hact as Hact'.
    destruct Hdiff, h2; inversion Hgen; subst;
    unfold emulator_act in Hact'; simpl in Hact'; unfold get_replay_response in Hact';
    simpl in *;

    assert (action_invocation_eq (t,i,r) t' i' = false) as Hneq;
    unfold action_invocation_eq;
    repeat (rewrite <- Nat.eqb_neq, Nat.eqb_sym in H); try rewrite H;
    destruct i, i'; try rewrite andb_false_r; try rewrite andb_false_l; auto.

    3,5: destruct (Nat.eq_dec n n0);
      [ rewrite e in H; contradiction | 
        rewrite <- (Nat.eqb_neq n n0) in n1; rewrite n1; apply andb_false_l].

    1,3 : rewrite <- HX in Hact'; rewrite rev_unit in Hact';
      rewrite Hneq in Hact'; unfold get_emulate_response in Hact';
      functional induction (get_emulate_response_helper
                              start_state t' (Inv n0) 0 max_response_number);
      repeat (split; auto); inversion Hact'; subst; auto; try discriminate_noresp;
      try apply (IHp H1);
      [ exists rtyp; auto | unfold get_state_history in e; simpl in e;
                            now apply spec_oracle_correct].

    all: assert ((h1 ++ [(t, Inv n, r)]) ++ (t0, i0, r0) :: h2 = X) as HX' by
            now rewrite <- app_assoc.
    all: pose (get_replay_response_correct (h1 ++ [(t, Inv n, r)])
                                        h2 s1 s (t0, i0, r0) t0
                                        i0 r0 HX' H4 H3) as Hprevstep;
      destruct Hprevstep as
          [Hmds1 [Hpres1 [Hxcpys1 [Hmds [Hpres [Hxcpys [Dumb [Hspecs [Hposts Hposts2]]]]]]]]].

    all: subst; rewrite Hmds in Hact'; rewrite Hxcpys in Hact'; rewrite rev_unit in Hact';
    rewrite Hneq in Hact'; unfold get_emulate_response in Hact'.

    all: functional induction (get_emulate_response_helper s t' (Inv n0) 0 max_response_number);
      repeat (split; auto); inversion Hact'; subst; auto; try discriminate_noresp;
      try apply (IHp H1);
      [ exists rtyp; auto | unfold get_state_history in e;
                 rewrite Hposts in e; simpl in e; rewrite Hpres in e;
                 now apply spec_oracle_correct].
  Qed.

  Lemma replay_done_correct :
    forall t i s s' a',
      generated s X ->
      spec ((t,i,NoResp) :: X) ->
      emulator_act s t i = (s', a') ->
      s.(md) = Replay /\
      s.(preH) = X /\
      s.(postH) = [] /\
      s'.(md) = Emulate /\
      s'.(preH) = X /\
      s'.(postH) = [a'] /\
      (exists rtyp, a' = (t,i,Resp rtyp)) /\
      spec (a' :: X).
  Proof.
    intros t i s s' a' Hgen Hspec Hact.
    pose Hact as Hact'.
    remember X as X'. 
    destruct X'; intros.
    - inversion Hgen; subst; auto.
      unfold start_state in Hact'; subst; auto.
      unfold emulator_act in Hact'; subst; simpl in *.
      unfold get_replay_response in Hact'; simpl in *.
      rewrite <- HeqX' in *; simpl in *.
      unfold get_commute_response in Hact'; simpl in *.
      unfold get_emulate_response in Hact'; simpl in *.
      repeat (split; auto);
        functional induction (get_emulate_response_helper  {|
                                  X_copy := [];
                                  Y_copy := fun _ : tid => [];
                                  preH := [];
                                  commH := fun _ : tid => [];
                                  postH := [];
                                  md := Replay |} t i 0 max_response_number); simpl in *;
        inversion Hact'; subst; simpl in *; auto; try discriminate_noresp.
      exists rtyp; auto.
      apply spec_oracle_correct; auto.
      
    - unfold emulator_act in Hact'; subst; auto.
      inversion Hgen; subst; auto.
      pose (get_replay_response_correct [] X' s1 s (t0, i0, r) t0
                                        i0 r HeqX' H3 H2) as Hprevstep;
      destruct Hprevstep as
          [Hmds1 [Hpres1 [Hxcpys1 [Hmds [Hpres [Hxcpys [Dumb [Hspecs [Hposts Hposts2]]]]]]]]].
      subst; rewrite Hmds in Hact'.
      unfold get_replay_response in Hact'. rewrite Hxcpys in Hact'; simpl in *.
      unfold get_commute_response in Hact'; simpl in *.
      (* TODO *)
      assert (Y_copy s t = []) as Hycpys by admit; rewrite Hycpys in *; simpl in *.
      unfold get_emulate_response in Hact'.

      functional induction (get_emulate_response_helper s t i 0 max_response_number);
        repeat (split; auto); inversion Hact'; subst; simpl in *; auto; try discriminate_noresp;
        try apply (IHp H0).
      rewrite Hposts; auto. exists rtyp; auto.
      unfold get_state_history in e; rewrite Hposts in e; simpl in e; rewrite Hpres in e.
      now apply spec_oracle_correct.
  Admitted.
    
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
    intros s h t i s' a' Hgen Hspec Hact. pose Hact as Hact'.
    remember (md s) as mds.
    unfold emulator_act in Hact'.
    destruct (mds); rewrite <- Heqmds in *; simpl in *.
    - admit.
    - split; eapply get_emulate_response_correct; eauto.
    - symmetry in Heqmds; pose (replay_state_correct s h Hgen Heqmds) as temp;
      destruct temp as [Hpres [Hposts [h' [Hresp Hxcpys]]]].
      induction h using rev_ind; induction h' using rev_ind; simpl in *; subst; auto.
      
      + pose (replay_done_correct t i s s' a') as Hdone. rewrite <- Hresp in *.
        eapply Hdone; eauto.
      + unfold get_replay_response in Hact'. rewrite Hxcpys in Hact'.
        rewrite rev_unit in Hact'.
        remember (action_invocation_eq x t i) as Hacteq.

        destruct (Hacteq); destruct x as [[t' [i']] r']; destruct i as [i].
        * assert (t = t' /\ i = i') as Heq. {
            unfold action_invocation_eq in HeqHacteq. symmetry in HeqHacteq.
            apply andb_prop in HeqHacteq; destruct HeqHacteq as [Heqi Heqt].
            rewrite Nat.eqb_eq in Heqi, Heqt; auto.
          } destruct Heq as [Heqi Heqt].
          rewrite Heqt, Heqi in *; rewrite app_nil_r in Hresp; auto.
          destruct r'.
          split. exists n.
          eapply (get_replay_response_correct h' [] s s' a' t' (Inv i') (Resp n)); eauto.

          inversion Hact'; subst; auto.
          assert (spec X) as HspecX by now eapply (spec_prefix_closed (Y++X) X Y X_and_Y_in_spec).
          eapply (spec_prefix_closed (h' ++ [(t', Inv i', Resp n)]) [(t', Inv i', Resp n)] h');
            eauto.
          now rewrite <- Hresp in HspecX.

          pose (X_and_Y_wf t' (Inv i') NoResp).
          assert (List.In (t', Inv i', NoResp) (Y++X)) as Hin. {
            rewrite <- Hresp.
            Search (List.In).
            repeat (apply List.in_app_iff; right). apply List.in_eq.
          } apply e in Hin; destruct Hin as [rtyp Hin]; discriminate.
        * rewrite app_nil_r in Hresp.
          assert (t <> t' \/ i' <> i) as Hneq. {
            unfold action_invocation_eq in HeqHacteq.
            symmetry in HeqHacteq.
            rewrite andb_false_iff in HeqHacteq. destruct HeqHacteq;
              rewrite Nat.eqb_neq in H; [now right | now left].
          } destruct Hneq as [Hneqt | Hneqi];
            eapply get_diverge_response_correct; eauto.
          right. intuition. inversion H; auto.
      +           
      

      Search (spec).
      symmetry in Heqmds; pose (replay_state_correct s h Hgen Heqmds) as temp;
      destruct temp as [Hpres [Hposts [h' [Hresp Hxcpys]]]]. 
      split.
      pose get_replay_response_correct.
      
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