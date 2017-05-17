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
Definition all_tid := 0.
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
    
Definition sim_commutes (tr : trace) : Prop.
Admitted.
Definition reordered (tr tr' : trace) : Prop.
Admitted.

Definition write_tid (ts1 ts2 : tid -> nat) (t : tid) := ts1 t <> ts2 t.
Definition write_tid_set ts1 ts2 : Ensemble tid :=
  fun tid => write_tid ts1 ts2 tid.
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
                                                                          
Parameter ref_impl : (refstate * action) -> (refstate * action).
Parameter spec : list history.
Hypothesis ref_impl_correct : forall tr : trace,
    List.In (history_of_trace tr) spec.
Hypothesis SIM_reordered_histories_correct : forall tr tr0 tr1 tr2 tr1' : trace,
    tr = tr0 ++ tr1 ++ tr2 ->
    sim_commutes tr1 ->
    reordered tr1 tr1' ->
    List.In (history_of_trace (tr0 ++ tr1' ++ tr2)) spec.

(* show that SIM-commutative region in constructive(?) implementation has no pair of  
 * events in the trace that have an access conflict *)