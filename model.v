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
  Definition rtyp : Type := nat.
  Inductive invocation : Type :=
  | Inv : nat -> invocation.
  Inductive response : Type :=
  | Resp : rtyp -> response
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
  | Oracle : mode
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
  Definition reordered (h h' : history) :=
    forall t, history_of_thread h t = history_of_thread h' t.
  
End Histories.

Section MachineState.
  Parameter max_response_number : rtyp.
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
                                          /\ forall rtyp', rtyp' < rtyp -> ~spec ((t,i,Resp rtyp')::h).
  Parameter oracle_response : history -> tid -> invocation -> response.
  Parameter oracle_response_correct :
    forall h t i,
      exists rtyp, oracle_response h t i = Resp rtyp /\ (spec ((t,i,Resp rtyp) :: h)).
    
  Parameter X : history.
  Parameter Y : history.
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
  
Section Machine.
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

  Definition get_oracle_response (s : state) (t: tid) (i: invocation) : state * action :=
    let resp := oracle_response (get_state_history s) t i in
    (mkState (s.(X_copy)) (s.(Y_copy)) (s.(preH)) (s.(commH)) ((t,i,resp)::s.(postH)) Oracle,
     (t,i,resp)).

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
    | _ => (mkState s.(X_copy) s.(Y_copy) ((t,i,NoResp)::s.(preH)) s.(commH) s.(postH) s.(md),
           (t,i,NoResp)) (* should never hit this *)
    end.
  Definition next_mode (s : state) (t: tid) (i: invocation) : mode :=
    match s.(md) with
      | Oracle => Oracle
      | Commute => match rev (s.(Y_copy) t) with
                     | [] => Oracle
                     | hd :: tl => if action_invocation_eq hd t i then Commute
                                   else Oracle
                   end
      | Replay => match rev s.(X_copy) with
                  | [] => Oracle
                  | hd :: tl => if action_invocation_eq hd t i then Replay
                                else Oracle
                  end
    end.
  Definition machine_act (s : state) (t: tid) (i : invocation) : (state * action) :=
    let mode := next_mode s t i in
    match mode with
      | Oracle => get_oracle_response (state_with_md s Oracle) t i
      | Commute => get_commute_response (state_with_md s Commute) t i
      | Replay => match rev (s.(X_copy)) with
                  | [hd] => get_replay_response (state_with_md s Commute) t i
                                                (* Changes mode to Commute *)
                  | _ => get_replay_response (state_with_md s Replay) t i
                  end
    end.

  Inductive current_state_history : state -> history -> Prop := 
  | GenNil : current_state_history start_state []
  | GenCons : forall s1 s2 t i r h,
                machine_act s1 t i = (s2, (t,i,r)) ->
                spec ((t,i,NoResp) :: h) ->
                current_state_history s1 h ->
                current_state_history s2 ((t,i,r)::h).
End Machine.

Section Conflict.
  Definition write_tid_set {A : Type} (ts1 ts2 : tid -> A) : Ensemble tid :=
    fun tid => ts1 tid <> ts2 tid.
  Definition step_writes (s1 s2 : state) : Ensemble tid :=
    Union tid
          (write_tid_set s1.(commH) s2.(commH))
          (write_tid_set s1.(Y_copy) s2.(Y_copy)).
 Definition conflict_free_writes (t :tid) (s1 s2 : state) :=
   step_writes s1 s2 = Singleton tid t /\
   s1.(md) = s2.(md) /\
   s1.(X_copy) = s2.(X_copy) /\
   s1.(preH) = s2.(preH) /\
   s1.(postH) = s2.(postH).
 Definition conflict_free_reads t i s :=
   forall (s1 s2 s1' s2': state) (a1 a2: action),
     s1.(Y_copy) t = s.(Y_copy) t ->
     s2.(Y_copy) t = s.(Y_copy) t ->
     s1.(commH) t = s.(commH) t ->
     s2.(commH) t = s.(commH) t ->
     s1.(md) = s.(md) ->
     s2.(md) = s.(md) ->
     machine_act s1 t i = (s1', a1) ->
     machine_act s2 t i = (s2', a2) ->
     a1 = a2 /\ s1'.(md) = s.(md) /\ s2'.(md) = s.(md).
End Conflict.
