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

Definition tid : Type := nat.
Definition all_tid := 0. (* XXX probably needs to change *)
Inductive action : Type :=
| ActInv (tid : tid) : action
| ActResp (tid : tid) : action
| Continue (tid: tid) : action.
Definition history : Type := list action.

Definition thread_history_state : Type := tid -> nat.
Definition thread_commute_state : Type := tid -> nat. (* 0 or 1 *)
Definition refstate : Type := nat.
Inductive state := State : refstate -> thread_history_state -> thread_commute_state -> state.

Inductive event : Type := Event (t: tid) (s1 s2 : state) (a r : action) : event.
Definition trace : Type := list event.
Function history_of_trace (tr: trace) : history :=
  match tr with
  | [] => []
  | Event t s1 s2 a r :: tl =>
    match a,r with
             | Continue t, Continue t' => history_of_trace tl
             | Continue t, _ => r :: history_of_trace tl
             | _, Continue t => a :: history_of_trace tl
             | _,_ => a :: r :: history_of_trace tl
             end
  end.
    
Definition swappable (a1 a2 : action) :=
  match a1, a2 with
  | ActInv t, ActInv t'
  | ActInv t, ActResp t'
  | ActResp t, ActInv t'
  | ActResp t, ActResp t' => t <> t'
  | _, _ => False
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

Definition write_tid_set (ts1 ts2 : tid -> nat) : Ensemble tid :=
  fun tid => ts1 tid <> ts2 tid.
Definition step_writes (s1 s2 : state) : Ensemble tid :=
  match s1, s2 with
  | State rs1 th1 tc1, State rs2 th2 tc2 =>
    let writes_tid := Union tid (write_tid_set th1 th2) (write_tid_set tc1 tc2) in
    if rs1 =? rs2 then writes_tid
    else Add tid writes_tid all_tid
  end.
Function trace_writes (tr : trace) : Ensemble tid :=
  match tr with
  | [] => Empty_set tid
  | Event t s1 s2 a r :: tl =>
    Union tid (step_writes s1 s2) (trace_writes tl)
  end.
Function trace_conflict_free (tr : trace) : Prop :=
  match tr with
  | [] => False
  | Event t s1 s2 a r :: tl =>
    Intersection tid (step_writes s1 s2) (trace_writes tl) = Empty_set tid
    /\ trace_conflict_free tl
  end.
                                                                          
Definition sim_commutes (h : history) : Prop. Admitted.

Parameter ref_impl : (refstate * action) -> (refstate * action).
Parameter spec : list history.

Inductive ref_impl_generated_trace : trace -> state -> state -> Prop :=
| RINil : forall s, ref_impl_generated_trace [] s s
| RICons : forall rs a rs' r tr rs0 th tc, 
    ref_impl (rs, a) = (rs', r) ->
    ref_impl_generated_trace tr (State rs0 th tc) (State rs th tc) ->
    ref_impl_generated_trace ((Event all_tid (State rs th tc) (State rs' th tc) a r) :: tr)
                             (State rs0 th tc) (State rs' th tc).
Hypothesis ref_impl_correct : forall (tr : trace) (s1 s2 : state),
    ref_impl_generated_trace tr s1 s2 ->
    List.In (history_of_trace tr) spec.
Hypothesis SIM_reordered_histories_correct : forall tr0 tr1 tr2 tr1' : trace,
    List.In (history_of_trace (tr0 ++ tr1 ++ tr2)) spec ->
    sim_commutes (history_of_trace tr1) ->
    reordered (history_of_trace tr1) (history_of_trace tr1') ->
    List.In (history_of_trace (tr0 ++ tr1' ++ tr2)) spec.


Definition emulator_trace (hbase hrun : history) : trace. Admitted.

(* if we have a correct trace whose corresponding history is SIM-comm,
 * then the emulator produces a conflict-free trace for that history *)
Lemma emulator_impl_conflict_free : forall tr s0 s1,
    ref_impl_generated_trace tr s0 s1 ->
    sim_commutes (history_of_trace tr) ->
    trace_conflict_free (emulator_trace (history_of_trace tr) (history_of_trace tr)).
Proof.
Admitted.

(* if we have the emulator instantiated with a SIM-comm history,
 * and the emulator acts on some input sequence, then the emulator
 * produces a correct trace for the spec *)
Lemma emulator_impl_correct : forall tr s0 s1 h,
    ref_impl_generated_trace tr s0 s1 ->
    sim_commutes (history_of_trace tr) ->
    List.In (history_of_trace (emulator_trace (history_of_trace tr) h)) spec.
Proof.
Admitted.

Theorem scalable_commutativity_rule : forall tr s0 s1 h,
    ref_impl_generated_trace tr s0 s1 ->
    sim_commutes (history_of_trace tr) ->
    trace_conflict_free (emulator_trace (history_of_trace tr) (history_of_trace tr))
    /\
    List.In (history_of_trace (emulator_trace (history_of_trace tr) h)) spec.
Proof.
  intros; split; [eapply emulator_impl_conflict_free | eapply emulator_impl_correct]; eauto.
Qed.