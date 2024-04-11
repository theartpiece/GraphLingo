Require Import String Arith List Lia.
Require Import Coq.FSets.FMapList.
Import ListNotations.
Module Part1.
(* ToDo: Should Node be [Definition Node] or [Notation Node]? Check HW1 to see what I am talking about *)
Definition Node := nat.
Definition Edge := (prod Node Node).
Definition EdgeList := (list Edge).
(* Type edge. *)
Definition Graph := list (prod Node (list Node)).
(* Definition Graph (n : Node) (edge_list : (list Edge) ) := list (prod Node (list Edge)). *)

(* TODO := add the check to avoid duplicated edge addition *)
Fixpoint add_edge (adj : Graph) (v1 v2: Node): Graph :=
    match adj with
    | [] => [(v1, [v2])]
    | (v, adj) :: rest => 
            if (Nat.eqb v v1) then  (v1, v2 :: adj) :: rest
            else (v, adj) :: add_edge rest v1 v2  
    end.

Fixpoint construct_empty_graph (n: nat) : Graph :=
    match n with
    | 0 => []
    | (S n1) => (n,[])::(construct_empty_graph n1)
    end.
    
Example two_nodes_empty_graph:
    construct_empty_graph 2 = [(2,[]);(1,[])].
Proof.
    simpl. auto.
Qed.



(* TODO --> check that we are not adding a node that's larger than n *)
Fixpoint construct_undir_graph (n: nat) (edge_list : list Edge): Graph := 
    match edge_list with 
    | [] => (construct_empty_graph n)
    | (u,v) :: edge_list1 => add_edge (add_edge (construct_undir_graph n edge_list1) u v) v u
    end.

Fixpoint construct_dir_graph (n: nat) (edge_list : list Edge): Graph := 
    match edge_list with 
    | [] => (construct_empty_graph n)
    | (u,v) :: edge_list1 => add_edge (construct_dir_graph n edge_list1) u v
    end.

Example null_graph:=
    construct_undir_graph 0 [].
Example null_graph_is_null:
    null_graph = [].
Proof.
    auto.
Qed.


Example two_cycle:=
    construct_undir_graph 2 [(1,2)].
Example two_cycle_is_correct:
    two_cycle = [(2,[1]);(1,[2])].
Proof.
    simpl. auto.
Qed.

Example one_line:=
    construct_dir_graph 2 [(1,2)].
Example one_line_is_correct:
    one_line = [(2,[]);(1,[2])].
Proof.
    simpl. auto.
Qed.




(* Todo  ---> Prove that construct_graph function is correct. *)


    

Fixpoint get_reachable_nodes (g: Graph) (u : Node): (list Node):=
    match g with
    | [] => []
    | (v,e)::g1 => 
                if (Nat.eqb u v) 
                    then e ++ (get_reachable_nodes g1 u)
                else
                    let n1 := (get_reachable_nodes g1 u) in 
                    if (andb (existsb (Nat.eqb u) e)  (negb (existsb (Nat.eqb v) n1)))
                        then v::n1
                    else n1
    end.

Fixpoint get_neighbors (g: Graph) (u : Node): (list Node):=
    match g with
    | [] => []
    | (v,e)::g1 => 
                if (Nat.eqb u v) 
                    then e 
                else
                    get_neighbors g1 u
    end.


Example all_nghbrs_of_1_in_two_cycle:
    get_reachable_nodes two_cycle 1 = [2].
Proof.
    simpl. auto.
Qed.

Example actual_nghbrs_of_1_in_one_line:
    get_neighbors one_line 1 = [2].
Proof.
    simpl. auto.
Qed.

Example actual_nghbrs_of_2_in_one_line:
    get_neighbors one_line 2 = [].
Proof.
    simpl. auto.
Qed.


Fixpoint is_connected (g : Graph) : Prop:=
    match g with 
    | nil => True
    | (v,e)::g1 => let n := get_reachable_nodes g v in 
                    match n with
                    | nil => False
                    | _ => is_connected g1
                    end
    end.
    
    


Example null_graph_is_connected:
    is_connected null_graph.
Proof.
    simpl. auto.
Qed.

Example one_line_is_connected:
    is_connected one_line.
Proof.
    simpl. auto.
Qed.

Example one_line_one_node:=
    construct_dir_graph 3 [(1,2)].

Example one_line_one_node_is_not_connected:
    not (is_connected one_line_one_node).
Proof.
    simpl. auto.
Qed.

Inductive Step : Graph * list Node * list Node -> Graph * list Node * list Node -> Prop :=
| StepVisited : forall g vis st v,
    ~ In v vis -> Step (g, vis, v :: st) (g, v :: vis, (get_neighbors g v) ++ st)
| StepVisit : forall g vis st v,
    In v vis -> Step (g, vis, v :: st) (g, vis, st)
| StepStart : forall g v,
    Step (g, [], []) (g, [], [v]).

Inductive StepStar : Graph * list Node * list Node -> Graph * list Node * list Node -> Prop :=
| StepRefl : forall g vis st,
    StepStar (g, vis, st) (g, vis, st)
| StepStarOnce : forall g vis1 vis2 vis3 st1 st2 st3,
    Step (g, vis1, st1) (g, vis2, st2) -> StepStar (g, vis2, st2) (g, vis3, st3) -> StepStar (g, vis1, st1) (g, vis3, st3).

(* Lemma item_in_list: forall a l node,
 In node (a :: l) -> hd node (a :: l) /\ In node l.
Proof.
    intros. simpl in H. 
    
Qed. *)

Theorem get_reachable_nodes_implies_get_neighbours: forall graph start node,
    In node (get_neighbors graph start) -> In node (get_reachable_nodes graph start).
Proof.
    intros. induction get_neighbors. inversion H. simpl in H. destruct H.
    - .
    - auto.   
    apply in_app_iff in H.
    
Qed.


Theorem dfs_correctness : forall graph start visited' stack',
    StepStar (graph, [], [start]) (graph, visited', stack') ->
    (forall node, In node visited' -> In node (get_reachable_nodes graph node) ).
Proof.
    intros. inversion H;subst. 
    - inversion H0.
    - inversion H3;subst. simpl In in H0. unfold get_reachable_nodes. 
    unfold get_neighbors in H3.
    
    inversion H2.  unfold get_reachable_nodes. simpl.
    (* Property: All visited nodes are reachable *)
    (forall node, In node visited' -> exists visited'' path, StepStar (graph, [], [start]) (graph, visited'', node :: path)).
  Proof.
    intros graph start visited stack H.
    induction H.
    - (* Base case: Term *)
      intros. econstructor. admit.
    - intros. econstructor.  eauto. eapply StepStarOnce. inversion H.
    - (* Inductive case: Step *)
      intros node H_in.
      destruct H0 as [graph' visited' stack' H_step].
      inversion H_step; subst.
      + (* Step_Pop *)
        apply in_app_iff in H_in.
        destruct H_in as [H_in_stack | H_in_adj].
        * (* Node is in stack *)
          apply IHclos_refl_trans. assumption.
        * (* Node is in adjacency list *)
          admit. (* You need to prove the existence of a path to this node *)
      + (* Step_Visit *)
        apply IHclos_refl_trans. assumption.
  Admitted.

Theorem dfs_correctness : forall graph start visited' stack',
    StepStar (graph, [], [start]) (graph, visited', stack') ->
    (* Property: All visited nodes are reachable *)
    (forall node, In node visited' -> exists visited'' path, StepStar (graph, [], [start]) (graph, visited'', node :: path)).
  Proof.
    intros graph start visited stack H.
    induction H.
    - (* Base case: Term *)
      intros. econstructor. admit.
    - intros. econstructor.  eauto. eapply StepStarOnce. inversion H.
    - (* Inductive case: Step *)
      intros node H_in.
      destruct H0 as [graph' visited' stack' H_step].
      inversion H_step; subst.
      + (* Step_Pop *)
        apply in_app_iff in H_in.
        destruct H_in as [H_in_stack | H_in_adj].
        * (* Node is in stack *)
          apply IHclos_refl_trans. assumption.
        * (* Node is in adjacency list *)
          admit. (* You need to prove the existence of a path to this node *)
      + (* Step_Visit *)
        apply IHclos_refl_trans. assumption.
  Admitted.

Inductive Term : Graph * list Node * list Node -> Prop :=
| Term_Empty : forall g, Term (g, [], []).

Inductive Eval : Graph * list Node * list Node -> Graph * list Node * list Node -> Prop :=
| Eval_Step : forall s s', Step s s' -> Eval s s'
| Eval_Term : forall s s', Term s -> Eval s s'.







(* Size of the Graph *)
Fixpoint get_size (g : Graph) : nat :=
  match g with
  | nil => 0
  | (v, _) :: g' => 1 + get_size g'
  end.

Definition example_graph1 := [(1, [2; 3]); (2, [1; 3]); (3, [1; 2])].
Example example_graph1_size : get_size example_graph1 = 3.
Proof. reflexivity. Qed.
  
Definition example_graph2 := [(1, []); (2, [1])].
Example example_graph2_size : get_size example_graph2 = 2.
Proof. reflexivity. Qed.

(* Non Connected graph *)
Definition example_graph3 := [(1, []); (3, []); (2, [3])].
Example example_graph3_size : get_size example_graph3 = 3.
Proof. reflexivity. Qed.

Definition example_graph4: Graph := nil.
Example example_graph4_size : get_size example_graph4 = 0.
Proof. reflexivity. Qed.

(* 
    TO Calculate the diameter of the graph 
    We just assume that the diameter will be calculated only for connected graphs. ??
    Diameter = longest shortest path between any 2 pair of nodes
    - need the shortest distance between all pair of nodes
    - Then need the max value among all those
*)

(* 
    BFS to find the shortest path from source to target
    Returns a nat which is the shortest distance between source and target
    or returns None if there is no path
*)

Fixpoint bfs_helper (g : Graph) (queue : list (list Node)) (visited : list Node) (distance : nat) (target : Node) : option nat :=
  match queue with
  | [] => None
  | path :: queue' =>
    let cur := hd 0 path in
    if Nat.eqb cur target then Some distance
    else if existsb (Nat.eqb cur) visited then bfs_helper g queue' visited distance target
    else let neighbors := get_all_neighbors g cur in
         let new_paths := map (fun n => n :: path) neighbors in
         let queue'' := (queue' ++ new_paths) in
         bfs_helper g queue'' (cur :: visited) (S distance) target
  end.

Definition bfs_shortest_path_distance (g : Graph) (source target : Node) : option nat :=
  bfs_helper g [[source]] [] 0 target.

