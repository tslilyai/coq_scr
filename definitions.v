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

Definition tid : Type := nat.
Inductive action : Type :=
| ActInv (tid : tid) : action
| ActResp (tid : tid) : action
| Continue (tid: tid) : action.
Definition history : Type := list action.

Definition thread_history_state : Type := tid -> nat.
Definition thread_commute_state : Type := tid -> bool.
Definition refstate : Type := nat.
Inductive state := striple : refstate -> thread_history_state -> thread_commute_state -> state.

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
Definition conflict_free (tr : trace) : Prop :=
  history_of_trace tr.
Admitted.
                                                                          
Parameter ref_impl : (refstate * action) -> (refstate * action).
Parameter spec : list history.
Hypothesis ref_impl_correct : forall tr : trace,
    In (history_of_trace tr) spec.
Hypothesis SIM_reordered_histories_correct : forall tr tr0 tr1 tr2 tr1' : trace,
    tr = tr0 ++ tr1 ++ tr2 ->
    sim_commutes tr1 ->
    reordered tr1 tr1' ->
    In (history_of_trace (tr0 ++ tr1' ++ tr2)) spec.

(* show that SIM-commutative region in constructive(?) implementation has no pair of  
 * events in the trace that have an access conflict *)