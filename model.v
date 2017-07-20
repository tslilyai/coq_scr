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

  Parameter num_threads : tid.
  Parameter tid_le_num_threads : forall tid : tid, tid < num_threads /\ 0 < num_threads.
  
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
  Hint Constructors reordered.
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
                                          /\ spec ((t,i,Resp rtyp) :: h)
                                          /\ forall rtyp', rtyp' < rtyp -> ~spec ((t,i,Resp rtyp)::h).
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
  Definition start_mode := match X with | [] => Commute | _ => Replay end.
  Definition start_state : state :=
    mkState X (history_of_thread Y) [] (fun tid => []) [] start_mode.
                                        
  Parameter sim_commutes :
    forall hd tl tl' Z,
      reordered (hd ++ tl) Y ->
      reordered tl' tl ->
      spec (Z++tl++X) ->
      spec (Z++tl'++X).

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
  Function combine_tid_histories (histories : tid -> history) (t : tid) :=
    match t with
      | 0 => []
      | S t' => histories t' ++ combine_tid_histories histories t' 
    end.
                                                        
  Definition combined_histories (histories : tid -> history) :=
    combine_tid_histories histories num_threads.
  Definition get_state_history (s : state) :=
    s.(postH) ++ combined_histories s.(commH) ++ s.(preH).
  Definition state_with_md (s : state) (md : mode) :=
    mkState s.(X_copy) s.(Y_copy) s.(preH) s.(commH) s.(postH) md.
             
  Function get_emulate_response_helper (s : state) (t: tid) (i : invocation)
           (rtyp : nat) (fuel : nat) : state * action :=
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
      | hd::tl => (mkState s.(X_copy)
                               (fun tid => if tid =? t then (rev tl)
                                           else s.(Y_copy) tid)
                               s.(preH) (fun tid => if tid =? t then hd::(s.(commH) t)
                                                    else s.(commH) tid)
                                        s.(postH) Commute, hd)
      | _ => (s, (t,i,NoResp)) (* should never hit this *)
    end.
  Definition get_replay_response (s : state) (t: tid) (i : invocation) : state * action :=
    match rev s.(X_copy) with
    | hd::tl => (mkState (rev tl) s.(Y_copy) (hd::s.(preH)) s.(commH) s.(postH) s.(md), hd)
    | _ => (s, (t,i,NoResp)) (* should never hit this *)
    end.
  Definition next_mode (s : state) (t: tid) (i: invocation) : mode :=
    match s.(md) with
      | Emulate => Emulate
      | Commute => match rev (s.(Y_copy) t) with
                     | [] => Emulate
                     | hd :: tl => if action_invocation_eq hd t i then Commute
                                   else Emulate
                   end
      | Replay => match rev s.(X_copy) with
                  | [] => Emulate
                  | hd :: tl => if action_invocation_eq hd t i then Replay
                                else Emulate
                  end
    end.
  Definition emulator_act (s : state) (t: tid) (i : invocation) : (state * action) :=
    let mode := next_mode s t i in
    match mode with
      | Emulate => get_emulate_response (state_with_md s Emulate) t i
      | Commute => get_commute_response (state_with_md s Commute) t i
      | Replay => match rev (s.(X_copy)) with
                  | [hd] => get_replay_response (state_with_md s Commute) t i
                                                (* Changes mode to Commute *)
                  | _ => get_replay_response (state_with_md s Replay) t i
                  end
    end.

  Inductive generated : state -> history -> Prop := (* XXX: not sure about this *)
  | GenNil : generated start_state []
  | GenCons : forall s1 s2 t i r h,
                emulator_act s1 t i = (s2, (t,i,r)) ->
                spec ((t,i,NoResp) :: h) ->
                generated s1 h ->
                generated s2 ((t,i,r)::h).

End Emulator.
