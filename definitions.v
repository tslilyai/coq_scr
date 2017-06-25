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
           (rtyp : nat) (fuel : nat) :
    state * action :=
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
      | [] => get_emulate_response (state_with_md s Emulate) t i
      | hd::tl => if action_invocation_eq hd t i
                  then (mkState s.(X_copy) (fun tid => if tid =? t
                                                       then (rev tl)
                                                       else s.(Y_copy) t)
                                           s.(preH) (fun tid => if tid =? t
                                                                then hd::(s.(commH) t)
                                                                else s.(commH) tid)
                                                    s.(postH) Commute, hd)
                  else get_emulate_response
                         (mkState s.(X_copy) s.(Y_copy) s.(preH) s.(commH) s.(postH) Emulate)
                         t i
    end.
  Definition get_replay_response (s : state) (t: tid) (i : invocation) : state * action :=
    match rev s.(X_copy) with
      | [] => get_commute_response (state_with_md s Commute) t i (* will change to Commute... *)
      | hd::tl => if action_invocation_eq hd t i
                  then (mkState (rev tl) s.(Y_copy) (hd::s.(preH))
                                                    s.(commH) s.(postH) Replay, hd)
                          else get_emulate_response (state_with_md s Emulate) t i
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
      generated s2 ((t,i,r)::h)
  | GenEmulate : forall s h, generated s h -> generated (state_with_md s Emulate) h
  | GenCommute : forall s h,
                   generated s h ->
                   s.(md) = Replay ->
                   generated (state_with_md s Commute) h.
End Emulator.

Section Theorems.
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

    Lemma state_with_md_has_md :
      forall s s' mode,
        s' = state_with_md s mode ->
        s'.(md) = mode.
    Proof.
      intros. unfold state_with_md in *. rewrite H in *; simpl; auto.
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
    
    Lemma mode_unimportant_emulate_response :
      forall s t i md,
        get_emulate_response (state_with_md s md) t i = get_emulate_response s t i.
    Proof.
    Admitted.

    Lemma mode_unimportant_state_history :
      forall s md,
        get_state_history s = get_state_history
                             (mkState s.(X_copy) s.(Y_copy) s.(preH)s.(commH) s.(postH) md).
    Proof.
    Admitted.
    
  Lemma emulate_response_always_exists :
    forall s h t i s' a',
      generated s h ->
      spec ((t,i,NoResp) :: h) ->
      s.(md) = Emulate ->                                   
      get_emulate_response s t i = (s', a') ->
      exists rtyp, a' = (t,i,Resp rtyp).
  Proof.
    intros s h t i s' a' Hgen Hspec Hmd Hact.
    unfold emulator_act in Hact. unfold get_emulate_response in Hact;
      unfold get_emulate_response_helper in Hact.
    remember max_response_number as fuel.
    functional induction (get_emulate_response_helper s t i 0 max_response_number);
      pose (spec_resp_exists t i h Hspec) as Hrtyp;
      destruct Hrtyp as [rty [Hrtyp Hspec2]].
    - destruct fuel; simpl in *; rewrite e in *;
      inversion Hact; subst; exists rtyp; auto.
    - rewrite Heqfuel in Hact; simpl in *; rewrite e in *.
      admit. (* todo must show that rty works *)
    - Search (spec). (* TODO stuff relating fuel and rtyp *)
  Admitted.

  Lemma commute_response_always_exists :
    forall s h t i s' a',
      generated s h ->
      spec ((t,i,NoResp) :: h) ->
      s.(md) = Commute ->
      get_commute_response s t i = (s', a') ->
      exists rtyp, a' = (t,i,Resp rtyp).
  Proof.
    intros s h t i s' a' Hgen Hspec Hmd Hact.
    pose Hact as Hact'. unfold get_commute_response in *.
    remember (Y_copy s t) as ycpy.
    induction (ycpy) using rev_ind; simpl in *. 
    - apply GenEmulate in Hgen. eapply emulate_response_always_exists; eauto.
    - rewrite rev_unit in Hact'.
      remember (action_invocation_eq x t i) as Heq.
      destruct x as [[t' [i']] r]; destruct i as [i]; destruct Heq; subst;
      unfold_action_inv_eq.
      * assert (exists rtyp, r = Resp rtyp) as Hexists.
        pose X_and_Y_wf as Ywf. apply (Ywf t' (Inv i') r).
        (* TODO lemma about what Y_Copy contains *)
        admit. destruct Hexists as [rt Hexists].
        exists rt; inversion Hact'; subst; auto.
      * apply GenEmulate in Hgen; eapply emulate_response_always_exists; eauto.
      * apply GenEmulate in Hgen; eapply emulate_response_always_exists; eauto.
  Admitted.

  Lemma replay_response_always_exists : 
    forall s h t i s' a',
      generated s h ->
      spec ((t,i,NoResp) :: h) ->
      s.(md) = Replay ->
      get_replay_response s t i = (s', a') ->
      exists rtyp, a' = (t,i,Resp rtyp).
  Proof.
    intros s h t i s' a' Hgen Hspec Hmd Hact.
    pose Hact as Hact'. unfold get_replay_response in *.
    remember (X_copy s) as xcpy.
    induction (xcpy) using rev_ind; simpl in *. 
    - apply GenCommute in Hgen; auto. eapply commute_response_always_exists; eauto.
    - rewrite rev_unit in Hact'.
      remember (action_invocation_eq x t i) as Heq.
      destruct x as [[t' [i']] r]; destruct i as [i]; destruct Heq; subst;
      unfold_action_inv_eq.
      * assert (exists rtyp, r = Resp rtyp) as Hexists.
        pose X_and_Y_wf as Ywf. apply (Ywf t' (Inv i') r).
        (* TODO lemma about what Y_Copy contains *)
        admit. destruct Hexists as [rt Hexists].
        exists rt; inversion Hact'; subst; auto.
      * apply GenEmulate in Hgen. eapply emulate_response_always_exists; eauto. 
      * apply GenEmulate in Hgen; eapply emulate_response_always_exists; eauto. 
  Admitted.
    
  Lemma response_always_exists :
    forall s h t i s' a',
      generated s h ->
      spec ((t,i,NoResp) :: h) ->
      emulator_act s t i = (s', a') ->
      exists rtyp, a' = (t,i,Resp rtyp).
  Proof.
    intros s h t i s' a' Hgen Hspec Hact.
    pose (spec_resp_exists t i h Hspec) as Hrtyp;
      destruct Hrtyp as [rty [Hrtyp Hspec2]].
    remember (md s) as m.
    pose Hact as Hact'; unfold emulator_act in Hact'.
    destruct m; rewrite <- Heqm in Hact'.
    - eapply commute_response_always_exists; eauto.
    - eapply emulate_response_always_exists; eauto. 
    - eapply replay_response_always_exists; eauto.
  Qed.
  
  Lemma inv_of_action_eq : forall a t i r,
    a = (t, i, r) ->
    action_invocation_eq a t i = true.
  Proof.
    intros. unfold action_invocation_eq; subst. destruct i; repeat rewrite Nat.eqb_refl. auto. 
  Qed.

  Ltac discriminate_noresp :=
    match goal with
      | [ H : (_, (?t, ?i, NoResp)) = (_, ?a'),
              Hgen : generated ?s ?h,
                     Hspec : spec _,
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

  Lemma emulator_act_replay :
    forall s0 t i s a,
      emulator_act s0 t i = (s, a) ->
      s.(md) = Replay ->
      s0.(md) = Replay.
  Proof.
    intros s0 t i s a Hact Hmd.
    unfold emulator_act in Hact.
    destruct (md s0); auto.
    - unfold get_commute_response in Hact.
      induction (Y_copy s0 t) using rev_ind; simpl in *; simpl_actions.
      remember (action_invocation_eq x t i) as Heq.
      destruct Heq; simpl_actions; subst; simpl in *. discriminate.
    - simpl_actions.
  Qed.

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
      + unfold get_commute_response in H2.
        induction (Y_copy s1 t) using rev_ind; simpl in *; simpl_actions.
        remember (action_invocation_eq x t i) as Heq.
        destruct Heq; simpl_actions; subst; simpl in *. discriminate.
      + simpl_actions. destruct (action_invocation_eq x t i); subst; auto; simpl_actions.
        repeat (split; auto). exists h'; rewrite <- H1; split; auto.
        now rewrite rev_involutive.
  Qed.
    
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

  Lemma get_diverge_replay_response_correct :
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

    - rewrite <- HX in Hact'; rewrite rev_unit in Hact'; rewrite Hneq in Hact'.
      simpl_actions; repeat (split; auto).
      exists rtyp; auto.
      unfold get_state_history in e. unfold combined_commH in e.
      unfold start_state in e; simpl in *. unfold combine_tid_commH in e.
      admit. (* TODO combined *)
      discriminate_noresp.
    - assert ((h1 ++ [(t, Inv n, r)]) ++ (t0, i0, r0) :: h2 = X) as HX' by
            now rewrite <- app_assoc.
      pose (get_replay_response_correct (h1 ++ [(t, Inv n, r)])
                                        h2 s1 s (t0, i0, r0) t0
                                        i0 r0 HX' H4 H3) as Hprevstep;
      destruct Hprevstep as
          [Hmds1 [Hpres1 [Hxcpys1 [Hmds [Hpres [Hxcpys [Dumb [Hspecs [Hposts Hposts2]]]]]]]]].
      subst; rewrite Hmds in Hact'; rewrite Hxcpys in Hact';
      rewrite rev_unit in Hact'; rewrite Hneq in Hact'; simpl_actions;
      repeat (split; auto).
      exists rtyp; auto.
      unfold get_state_history in e; admit. (* TODO combined *)
      discriminate_noresp.
    - destruct (Nat.eq_dec n n0);
      [ rewrite e in H; contradiction | rewrite <- (Nat.eqb_neq n n0) in n1;
          rewrite n1; apply andb_false_l].
    - rewrite <- HX in Hact'; rewrite rev_unit in Hact'; rewrite Hneq in Hact'.
      simpl_actions; repeat (split; auto).
      exists rtyp; auto.
      unfold get_state_history in e; admit. (* TODO combined *)
      discriminate_noresp.
    - destruct (Nat.eq_dec n n0);
      [ rewrite e in H; contradiction | rewrite <- (Nat.eqb_neq n n0) in n1;
          rewrite n1; apply andb_false_l].
    - assert ((h1 ++ [(t, Inv n, r)]) ++ (t0, i0, r0) :: h2 = X) as HX' by
            now rewrite <- app_assoc.
      pose (get_replay_response_correct (h1 ++ [(t, Inv n, r)])
                                        h2 s1 s (t0, i0, r0) t0
                                        i0 r0 HX' H4 H3) as Hprevstep;
      destruct Hprevstep as
          [Hmds1 [Hpres1 [Hxcpys1 [Hmds [Hpres [Hxcpys [Dumb [Hspecs [Hposts Hposts2]]]]]]]]].
      subst; rewrite Hmds in Hact'; rewrite Hxcpys in Hact';
      rewrite rev_unit in Hact'; rewrite Hneq in Hact'; simpl_actions;
      repeat (split; auto).
      exists rtyp; auto.
      unfold get_state_history in e; admit. (* TODO combined *)
      discriminate_noresp.
  Admitted.
  
  Lemma get_diverge_commute_response_correct :
    forall h1 h2 t i i' r s s' a',
      h1 ++ (t,i,r) :: h2 = (history_of_thread Y t)  ->
      generated s h2 ->
      (i <> i') ->
      spec ((t,i',NoResp) :: h2) ->
      emulator_act s t i' = (s', a') ->
      s.(md) = Commute /\ s.(preH) = X
      /\ s.(commH) t = h2
      /\ s.(Y_copy) t = h1 ++ [(t,i,r)]
      /\ s'.(md) = Emulate
      /\ s'.(preH) = s.(preH)
      /\ (exists rtyp, a' = (t,i',Resp rtyp))
      /\ spec (a' :: h2).
  Proof.
  Admitted.

  Lemma commute_done_correct :
    forall t i s s' a' Y',
      generated s (Y' ++ X) ->
      spec ((t,i,NoResp) :: Y' ++ X) ->
      emulator_act s t i = (s', a') ->
      reordered Y' Y ->
      s.(md) = Commute /\
      s.(commH) = (fun tid => history_of_thread Y' tid) /\
      s.(preH) = X /\
      s.(postH) = [] /\
      s'.(md) = Emulate /\
      s'.(preH) = (Y' ++ X) /\
      s'.(postH) = [a'] /\
      (exists rtyp, a' = (t,i,Resp rtyp)) /\
      spec (a' :: Y' ++ X).
  Proof.
  Admitted.

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
      simpl_actions. admit.
      
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
      (* rewrite Hposts; auto. exists rtyp; auto.
      unfold get_state_history in e; rewrite Hposts in e; simpl in e; rewrite Hpres in e. *)
      admit. (* TODO combined 
      now apply spec_oracle_correct. *)
  Admitted.
    
  Lemma get_emulate_response_correct :
    forall s h t i s' a',
    generated s h ->
    spec ((t,i,NoResp) :: h) ->
    emulator_act (state_with_md s Emulate) t i = (s', a') ->
    (exists rtyp, a' = (t,i,Resp rtyp))
    /\ spec (a' :: h)
    /\ s'.(md) = Emulate.
  Proof.
    intros s h t i s' a' Hgen Hspec Hact.
    pose Hact as Hact'.
    split. eapply response_always_exists; eauto.
    split;
      unfold emulator_act in Hact'.
      unfold get_emulate_response in Hact';
      functional induction (get_emulate_response_helper s t i 0 max_response_number).
    2,5: discriminate_noresp.
    2,4: now apply IHp in Hact'.
    all : inversion Hact'; subst; auto. admit. (* TODO combined 
    pose (generated_history_corresponds_state_history s h Hgen) as Hh.
    unfold get_state_history in e. rewrite Hh in e.
    now rewrite (spec_oracle_correct ((t,i,Resp rtyp) :: h))*)
  Admitted.

  Lemma emulator_correct :
    forall s s' h t i a',
      generated s h ->
      spec ((t,i,NoResp) :: h) ->
      emulator_act s t i = (s', a') ->
      (exists rtyp, a' = (t,i,Resp rtyp)) /\ spec (a' :: h).
  Proof.
    intros s s' h t i a' Hgen Hspec Hact. pose Hact as Hact'.
    remember (md s) as mds.
    unfold emulator_act in Hact'.
    destruct (mds); rewrite <- Heqmds in *; simpl in *.
    - unfold get_commute_response in Hact'.
      induction (Y_copy s t) using rev_ind; simpl in *; auto.
      split; eapply get_emulate_response_correct; eauto.
      
      admit. (* TODO commute mode *)
    - split; eapply get_emulate_response_correct; eauto.
    - symmetry in Heqmds; pose (replay_state_correct s h Hgen Heqmds) as temp;
      destruct temp as [Hpres [Hposts [h' [Hresp Hxcpys]]]].
      induction h as [ | a h0] using rev_ind; induction h' as [ | b h0'] using rev_ind;
      simpl in *; subst; auto; simpl_actions.
      1,3: pose (replay_done_correct t i s s' a') as Hdone; rewrite <- Hresp in *;
        eapply Hdone; eauto.

      all: unfold get_replay_response in Hact'; rewrite Hxcpys, rev_unit in Hact'.
      all: remember (action_invocation_eq b t i) as Hacteq;
        destruct (Hacteq); destruct b as [[t' [i']] r']; destruct i as [i];
        unfold_action_inv_eq.
      + split; simpl_actions; destruct r'; [exists n; auto | discriminate_noresp].
      + eapply get_diverge_replay_response_correct; eauto.
      + eapply get_diverge_replay_response_correct; eauto.
        right; intuition; inversion H; auto.
      + split; simpl_actions; destruct r'; [exists n; auto | discriminate_noresp].
      + eapply get_diverge_replay_response_correct; eauto.
      + eapply get_diverge_replay_response_correct; eauto.
        right; intuition; inversion H; auto.
  Admitted.

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
End Theorems.