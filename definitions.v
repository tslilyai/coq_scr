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
| Nat : nat -> action
| Continue : action.
Definition taction : Type := tid * action.
Definition history : Type := list taction.

(* Does this work in place of memory? could also be a map *)
Definition thread_history_state : Type := tid -> nat.
Definition thread_commute_state : Type := tid -> bool.
Definition refstate : Type := nat.
Inductive state := 
| srefstate : refstate -> state
| sht : thread_history_state -> state
| scommutet : thread_commute_state -> state.

Parameter ref_impl : (refstate * taction) -> (refstate * taction).
Parameter spec : list history.

(* Definition history_wf *)
(* Definition history_reorder *)

Definition trace : Type := list ((state * taction) * (state * taction)).
Function history_of_trace (tr: trace) : history :=
  match tr with
  | [] => []
  | ((s1, a), (s2, r)) :: tl =>
             match a,r with
             | (t, Continue), (t', Continue) => history_of_trace tl
             | (t, Continue), _ => r :: history_of_trace tl
             | _, (t, Continue) => a :: history_of_trace tl
             | _,_ => a :: r :: history_of_trace tl
             end
  end.

Definition sim_commutes (tr : trace) : Prop.
Admitted.
Definition reordered (tr tr' : trace) : Prop.
Admitted.
  
Axiom ref_impl_correct : forall tr : trace,
    In (history_of_trace tr) spec.
Axiom SIM_reordered_histories_correct : forall tr tr0 tr1 tr2 tr1' : trace,
    tr = tr0 ++ tr1 ++ tr2 ->
    sim_commutes tr1 ->
    reordered tr1 tr1' ->
    In (history_of_trace (tr0 ++ tr1' ++ tr2)) spec.

(* show that SIM-commutative region in constructive(?) implementation has no pair of  
 * events in the trace that have an access conflict *)