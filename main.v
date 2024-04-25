Require Import String Arith List Lia.
Import ListNotations.
(* Require Import Program.
Require Import Wf. *)
Require Import Program.Wf.
Module Part1.

(* Representation of Graph *)
Notation Node := nat.
Definition Edge := (prod Node Node).
Definition EdgeList := (list Edge).
(* Type edge. *)
Definition Graph := list (prod Node (list Node)).
Definition EdgeGraph := list (prod Node Node).
(* Definition Graph (n : Node) (edge_list : (list Edge) ) := list (prod Node (list Edge)). *)


(* TODO := add the check to avoid duplicated edge addition *)
Fixpoint add_edge (adj : Graph) (v1 v2: Node): Graph :=
    match adj with
    | nil => (cons (v1, (cons v2 nil)) nil) 
    | (cons (x,nghbrs) adj1) => 
            if (Nat.eqb x v1) 
            then  (cons (x, (cons v2 nghbrs)) adj1) 
            else (cons (x, nghbrs) (add_edge adj1 v1 v2)) 
    end.

Fixpoint construct_empty_graph (n: nat) : Graph :=
    match n with
    | 0 => nil
    | (S n1) => (n,nil)::(construct_empty_graph n1)
    end.
    
Example two_nodes_empty_graph:
    construct_empty_graph 2 = [(2,nil);(1,nil)].
Proof.
    simpl. auto.
Qed.



(* TODO --> check that we are not adding a node that's larger than n *)
Fixpoint construct_undir_graph (n: nat) (edge_list : list Edge): Graph := 
    match edge_list with 
    | nil => (construct_empty_graph n)
    | (cons (u,v) edge_list1) => add_edge (add_edge (construct_undir_graph n edge_list1) u v) v u
    end.

Fixpoint construct_dir_graph (n: nat) (edge_list : list Edge): Graph := 
    match edge_list with 
    | nil => (construct_empty_graph n)
    | (cons (u,v) edge_list1) => add_edge (construct_dir_graph n edge_list1) u v
    end.

Example null_graph:=
    construct_undir_graph 0 nil.
Example null_graph_is_null:
    null_graph = nil.
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


    

(* The following functions retreives the union of parents and children nodes. *)
Fixpoint get_all_neighbors (g: Graph) (u : Node): (list Node):=
    match g with
    | nil => nil
    | (v,e)::g1 => 
                if (Nat.eqb u v) 
                    then e ++ (get_all_neighbors g1 u)
                else
                    let n1 := (get_all_neighbors g1 u) in 
                    if (andb (existsb (Nat.eqb u) e)  (negb (existsb (Nat.eqb v) n1)))
                        then v::n1
                    else n1
    end.

(* The following functions only retreives the children nodes. *)
Fixpoint get_children (g: Graph) (u : Node): (list Node):=
    match g with
    | nil => nil
    | (v,e)::g1 => 
                if (Nat.eqb u v) 
                    then e 
                else
                get_children g1 u
    end.


Example all_nghbrs_of_1_in_two_cycle:
    get_all_neighbors two_cycle 1 = [2].
Proof.
    simpl. auto.
Qed.

Example actual_nghbrs_of_1_in_one_line:
    get_children one_line 1 = [2].
Proof.
    simpl. auto.
Qed.

Example actual_nghbrs_of_2_in_one_line:
    get_children one_line 2 = nil.
Proof.
    simpl. auto.
Qed.


Fixpoint is_connected (g : Graph) : Prop:=
    match g with 
    | nil => True
    | (v,e)::g1 => let n := get_all_neighbors g v in 
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

Definition node_in (g: Graph) (n : Node) : Prop :=
    exists edge_list, In (n, edge_list) g.

Example one_in_one_line:
    node_in one_line 1.
Proof.
    simpl. unfold node_in. unfold one_line. simpl. eauto.
Qed.

Example two_in_one_line:
    node_in one_line 2.
Proof.
    simpl. unfold node_in. unfold one_line. simpl. eauto.
Qed.

Example three_not_in_one_line:
    not (node_in one_line 3).
Proof.
    unfold not. intros. inversion H. inversion H0. easy. simpl in H1. inversion H1. easy. easy.
Qed.

(* RETURNS True if u->v in the graph g *)
Definition edge_in (g: Graph) (u : Node) (v : Node) : Prop :=
    node_in g u /\ (forall ngbhrs_list,  (In (u, ngbhrs_list) g  ->  In v ngbhrs_list)).

(* g = [(1, [2,3,4]), (3, [4,5])] *)
(* g = [(1, [2,3,4]), (3, [4,5]), (1, [5])]  -- this does not exist in our exmaplewas*) 
(* edge_in g 1 2 = True *)
(* edge_in g 2 1 = False *)

    (* exists edge_list, (In (u, edge_list) g  /\  In v edge_list). *)

Example one_two_in_one_line:
    edge_in one_line 1 2.
Proof.
    (* simpl. unfold edge_in. unfold one_line. simpl. intros. split. destruct (1, edge_list). inversion H. easy. inversion H0. inversion H1. apply in_eq. easy.  *)
    simpl. unfold edge_in. simpl. intros. split. apply one_in_one_line.  intros. inversion H. easy. inversion H0. inversion H1. apply in_eq. easy. 
Qed.

Example two_one_not_in_one_line:
    edge_in one_line 2 1 -> False.
Proof.
    intros .
    unfold edge_in in H.
    unfold one_line in H.
    simpl in H. destruct H. 
    specialize (H0 []).
    firstorder.
Qed.

Example one_three_not_in_one_line:
    edge_in one_line 1 3 -> False.
Proof.
    unfold not. simpl. unfold edge_in. unfold one_line. simpl. intros. destruct H. eauto. specialize (H0 [2]). firstorder. lia. easy.
Qed.

Fixpoint adj_graph_to_edge_list_helper (u: Node) (edge_list: list Node): EdgeGraph := 
    match edge_list with 
    | nil => nil
    | (cons v edge_list_rest) => (u,v)::(adj_graph_to_edge_list_helper u edge_list_rest)
    end.

Fixpoint adj_graph_to_edge_list (graph: Graph): EdgeGraph := 
    match graph with 
    | nil => nil
    | (cons (u,edge_list) rest_adj) => ((adj_graph_to_edge_list_helper u edge_list) ++ (adj_graph_to_edge_list rest_adj))
    end.

Compute adj_graph_to_edge_list [(1,[2;3;4]);(2,[3;4])].
Lemma adj_reprsn_has_edge_list_reprsn: 
    forall adj_graph, (exists edge_graph, (forall u v , edge_in adj_graph u v -> In (u, v) edge_graph)).
Proof.
intros.
(* exists (adj_graph_to_edge_list adj_graph). *)
intros.
induction adj_graph.
- exists (adj_graph_to_edge_list []). simpl. unfold edge_in. intros. destruct H. inversion H. firstorder.
- exists (let (u, edge_list):=a in (adj_graph_to_edge_list_helper u edge_list) ++ (adj_graph_to_edge_list adj_graph)). intros. destruct a. eapply in_app_iff. inversion H; subst; clear H. inversion H0; subst; clear H0. inversion H. inversion H0; subst; clear H0.
Admitted.

Compute max 2 3.
Fixpoint max_vertex (graph: EdgeGraph): Node :=
    match graph with
    | nil => 0
    | (u,v)::rest_edge_list => max u (max v (max_vertex rest_edge_list)) 
    end.

Compute max_vertex [(1,2);(2,4);(4,5);(1,3)].

Definition edge_list_to_adj_graph (graph: EdgeGraph): Graph := 
    construct_dir_graph (max_vertex graph) graph.

Lemma edge_reprsn_has_adj_graph_reprsn: 
    forall edge_graph, (exists adj_graph, (forall u v , In (u, v) edge_graph -> edge_in adj_graph u v)).
Proof.
Admitted.



Inductive is_reachable_ind : Graph -> Node -> Node -> Prop :=
| is_reachable_ind_base : forall v1 v2 g,edge_in g v1 v2 -> is_reachable_ind g v1 v2
| is_reachable_ind_once : forall v1 v2 v3 g , edge_in g v1 v2 -> is_reachable_ind g v2 v3 -> is_reachable_ind g v1 v3.


Example one_two_reachable_ind_in_one_line:
    is_reachable_ind one_line 1 2.
Proof.
    eapply is_reachable_ind_base. eapply one_two_in_one_line. 
Qed.

Example one_one_not_reachable_ind_in_one_line:
    is_reachable_ind one_line 1 1 -> False.
Proof.
    intros.
Admitted.

Example two_two_not_reachable_ind_in_one_line:
    is_reachable_ind one_line 2 2 -> False.
Proof.
    intros.
Admitted.


Example one_cycle:=
    construct_dir_graph 2 [(1,2);(2,1)].

Example one_loop:=
    construct_dir_graph 2 [(1,1)].

Example one_one_reachable_in_one_cycle:
    is_reachable_ind one_cycle 1 1.
Proof.
    eapply is_reachable_ind_once. unfold one_cycle. simpl. unfold edge_in. intros. inversion H. firstorder. easy. easy. firstorder.  easy. inversion H. firstorder.
    eapply is_reachable_ind_base. unfold one_cycle. simpl. unfold edge_in. intros. inversion H. firstorder. inversion H. firstorder. easy. firstorder. easy.  easy.
Qed.

Example two_two_reachable_in_one_cycle:
    is_reachable_ind one_cycle 2 2.
Proof.
    eapply is_reachable_ind_once. unfold one_cycle. simpl. unfold edge_in. intros. inversion H. firstorder. inversion H. firstorder. easy. firstorder. easy. firstorder.  easy.
    eapply is_reachable_ind_base. unfold one_cycle. simpl. unfold edge_in. intros. inversion H. firstorder. inversion H. firstorder. easy. firstorder. easy. inversion H.  firstorder.
Qed.






(* ----------------------------------------------------------------------- *)

(* Size of the Graph: Number of Nodes in the Graph *)
Fixpoint get_size (g : Graph) : nat :=
  match g with
  | nil => 0
  | (v, _) :: g' => 1 + get_size g'
  end.
Definition example_graph1 := construct_dir_graph 3 [(1, 2); (1, 3); (2, 1); (2, 3)]. 
Example example_graph1_size : get_size example_graph1 = 3.
Proof. reflexivity. Qed.
  
Definition example_graph2 := construct_dir_graph 2 [(1, 2)].
Example example_graph2_size : get_size example_graph2 = 2.
Proof. reflexivity. Qed.

(* Non Connected graph *)
Definition example_graph3 := construct_dir_graph 3 [(2, 3)].
Example example_graph3_size : get_size example_graph3 = 3.
Proof. reflexivity. Qed.

Definition example_graph4: Graph := nil.
Example example_graph4_size : get_size example_graph4 = 0.
Proof. reflexivity. Qed.

(* Implementing degrees of vertices *)
Fixpoint degree (g : Graph) (v : Node) : nat :=
  match g with
  | [] => 0
  | (u, neighbors) :: rest =>
    if Nat.eqb u v then length neighbors
    else degree rest v
  end.

(* Some example *)
Example degree_example_1 : degree [(1, [2; 3]); (2, [1; 3]); (3, [1; 2])] 1 = 2.
Proof.
    reflexivity.
Qed.

Example degree_example_2 : degree [(1, [2; 3]); (2, [1; 3; 4; 5]); (3, [1; 2])] 2 = 4.
Proof.
    reflexivity.
Qed.

(* Lemma: Degree of vertices of an empty graph is always 0 *)
Lemma degree_empty_graph : forall v, degree [] v = 0.
Proof.
    intros v. reflexivity.
Qed.

(* Lemma: Degree of vertices of a single vertex is always 0 *)
Lemma degree_single_vertex : forall v u, v <> u -> degree [(u, [])] v = 0.
Proof.
    intros v u H. 
    simpl.
    destruct (Nat.eqb_spec u v).
    - auto.
    - auto.
Qed.

(* Lemma: Degree of vertices is always positive *)
Lemma degree_positive : forall g v,
  0 <= degree g v.
Proof.
    intros.
    induction g.
    - simpl. lia.
    - simpl. destruct a as[u neighbors].
        * apply Nat.le_0_l.     
Qed.


(* The degree of vertices of a graph increases when we add an edge *)
Lemma degree_add_edge : forall g v1 v2,
  (* In v (fst (split g)) -> *)
  (~ In v2 (get_children g v1)) -> degree (add_edge g v1 v2) v1 = S (degree g v1).
Proof.
    intros.
    destruct H. destruct get_children.
    - simpl. 

Admitted.

(* Property of Graph: The sum of degrees in an undirected graph equals twice the number of edges *)

(* Helper to get sum of degrees in a graph *)
Fixpoint sum_of_degrees_undirected (g : Graph) : nat :=
  match g with
  | [] => 0
  | (n, adj) :: rest => length adj + sum_of_degrees_undirected rest
  end.
(* Helper to get number of edges in a graph *)
Fixpoint num_edges (g : Graph) : nat :=
  match g with
  | [] => 0
  | (n, adj) :: rest => length adj + num_edges rest
  end.
Definition num_edges_undirected (g : Graph) : nat :=
    num_edges g / 2.

Definition example_complex_undir_graph := 
  construct_undir_graph 4 [(1, 2); (1, 3); (2, 3); (2, 4); (3, 4)].
(* Compute(sum_of_degrees_undirected example_complex_undir_graph).
Compute(num_edges_undirected example_complex_undir_graph). *)

Theorem sum_of_degrees_equals_twice_edges : forall (g : Graph), 
    sum_of_degrees_undirected g = 2 * num_edges_undirected g.
Proof.
  intros.
  induction g.
  - simpl. reflexivity.
  - simpl. unfold num_edges_undirected in *. rewrite IHg.
    destruct num_edges.
    * simpl. 
   (* unfold sum_of_degrees_undirected in *. *)
    (* rewrite Nat.mul_add_distr_l. *)
    (* unfold num_edges in *. simpl in IHg. rewrite IHg. 
    rewrite Nat.div_add_l.
    + reflexivity.
    + apply Nat.neq_succ_0.
      apply Nat.lt_0_succ. *)
Admitted.

(* ----------------------------------------------------------------------- *)

(* For Directed Graphs: In-degree and Out-degree *)

Fixpoint in_degree (g : Graph) (v : Node) : nat :=
  match g with
  | [] => 0
  | (_, adj) :: rest => (if Nat.eq_dec (length (filter (Nat.eqb v) adj)) 0 then 0 else 1) + in_degree rest v
  end.

Fixpoint out_degree (g : Graph) (v : Node) : nat :=
  match g with
  | [] => 0
  | (n, adj) :: rest => if Nat.eqb n v then length adj else out_degree rest v
  end.

Definition example_dir_graph1 := construct_dir_graph 4 [(1, 2); (1, 3); (2, 3); (3, 4)].
Definition example_dir_graph2 := construct_dir_graph 5 [(1, 2); (1, 3); (2, 4); (3, 4); (4, 5)].

Example in_degree_example_dir_graph1:
  in_degree example_dir_graph1 3 = 2.
Proof. reflexivity. Qed.

Example out_degree_example_dir_graph1:
  out_degree example_dir_graph1 1 = 2.
Proof. reflexivity. Qed.

Example in_degree_example_dir_graph_2:
  in_degree example_dir_graph2 4 = 2.
Proof. reflexivity. Qed.

Example out_degree_example_dir_graph_2:
  out_degree example_dir_graph2 4 = 1.
Proof. reflexivity. Qed.

(* Definition sum_in_degree (g : Graph) : nat := 
Definition sum_out_degree (g : Graph) : nat := 
Lemma sum_in_out_degrees_equal : forall g, forall v,
  sum_in_degree g = sum_out_degree g.
Proof.
Admitted. *)

(* Property: Sum of in_degrees out_degs is even *)
Definition even_sum_degrees_property (g : Graph) : Prop :=
  forall v, (in_degree g v + out_degree g v) mod 2 = 0.

(* Proof Property *)
Lemma even_sum_degrees_directed_graph : forall g : Graph,
  even_sum_degrees_property g.
Proof.
  intros.
  unfold even_sum_degrees_property.
  induction g. simpl. 
  - reflexivity.
  - intros v. unfold in_degree in *. unfold out_degree in *.
    simpl. destruct a.
    (* simpl. rewrite IHg.  *)
  
  destruct (Nat.eq_dec n v) eqn:Eqn.
    + subst.
      (* apply IHg.
    + apply IHg. *)
Admitted.


(* 
    BFS Algorithm and reachability
*)

Fixpoint bfs_helper (g : Graph) (queue :  list Node) (visited : list Node)
     (termination_counter : nat) : list Node :=
    match termination_counter with
    | O => rev visited
    | S n =>
        match queue with
            | [] => rev visited
            | cur :: queue' =>
                if existsb (Nat.eqb cur) visited then bfs_helper g queue' visited n
                else 
                let neighbors := get_children g cur in
                let queue'' := queue' ++ neighbors in
                bfs_helper g queue'' (cur :: visited) n
        end
end.

Definition bfs (g : Graph) (source : Node) : list Node :=
    bfs_helper g [source] [] (get_size(g) * get_size(g)).

Definition example_bfs_graph : Graph := construct_dir_graph 5 [(1, 2); (1, 3); (2, 4); (3, 2); (3, 5); (4, 5)].

(*                    Example Graph
      1 --> 2 --> 4
      |     ^     |
      |     |     v
       ---> 3 --> 5
*)

Lemma bfs_one_visits_one:
    In 1 (bfs example_bfs_graph 1).
Proof.
    simpl. lia.
Qed.

Lemma bfs_one_visits_four:
    In 4 (bfs example_bfs_graph 1).
Proof.
    simpl. lia.
Qed.

Lemma bfs_three_does_not_visit_one:
    ~ In 1 (bfs example_bfs_graph 3).
Proof.
    simpl. unfold not. intros. 
    destruct H. lia.
    destruct H. lia.
    destruct H. lia.
    destruct H. lia.
    destruct H.
Qed.

(* see other way: bool*)
(* Fixpoint Unique (l : list Node) : Prop :=
  match l with
  | [] => True
  | x :: xs => ~ In x xs /\ Unique xs
  end. *)
(* Trying to implement as a bool so easier to proove in Coq*)
Fixpoint Unique (l : list Node) : bool :=
match l with
  | [] => true
  | x :: xs => if existsb (Nat.eqb x) xs then false else Unique xs
end.


Lemma bfs_unique_visited : forall (g : Graph) (source : Node),
    Unique (bfs g source) = true.
Proof.
  intros g source.
  unfold Unique.
  induction (bfs g source).
  - auto.
  - destruct (existsb (Nat.eqb a) l) eqn:Heq_existsb.
    * apply existsb_exists in Heq_existsb.
      destruct Heq_existsb as [x [Heq_x Hin_x]].
      apply Nat.eqb_eq in Hin_x.
      (* contradiction.
      rewrite Heq_x in Hin_x.
  fold Unique in *. eauto.  *)
  (* split.
    * induction l.
      ** simpl. auto.
      ** simpl. intros [Heq | Hin].
        *** rewrite Heq in IHl. unfold Unique in IHl. eauto.  
        admit.
        *** fold Unique in IHl0. fold Unique in IHl.  admit.
    * apply IHl. *)
Admitted.

Lemma bfs_terminates : forall (g : Graph) (source : Node),
  exists nodes : list Node, bfs g source = nodes.
Proof.
  intros. unfold bfs.
  induction (get_size g).
  - exists []. reflexivity.
  - simpl.
Admitted.
  
Lemma bfs_never_more_than_size : forall (g: Graph) (source : Node), 
  (get_size g >= 1) -> (get_size g) >= length (bfs g source).
Proof.
  intros.
  induction bfs.
  - simpl. lia.
  - destruct l.
    * apply H.
    (* * eassumption. rewrite <- IHl.   *)
Admitted.


(* Function to get all pairs of nodes *)
Fixpoint all_pairs (l : list Node) : list (Node * Node) :=
  match l with
  | nil => nil
  | x :: xs => map (pair x) xs ++ all_pairs xs
  end.

  Example example_1: all_pairs [1; 2; 3] = [(1, 2); (1, 3); (2, 3)].
  Proof. reflexivity. Qed.
  
  Example example_2: all_pairs [4; 5] = [(4, 5)].
  Proof. reflexivity. Qed.
  
  Example example_3: all_pairs [6] = [].
  Proof. reflexivity. Qed.

(* Shortest Path Definition *)
  Fixpoint shortest_path_helper (g: Graph) (srcs : list Node) (dst: Node) (visited: list Node) (fuel: nat): list Node  :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match srcs with
    | [] => []
    | src :: xsrcs => (
        let min_rest_path := (shortest_path_helper g xsrcs dst visited fuel') in
        let curr_path := src::(shortest_path_helper g (get_children g src) dst (src::visited) fuel') in
        if (Nat.eqb src dst) then
            [src]
        else if (existsb (Nat.eqb src) visited) then
            min_rest_path
        else if (Nat.eqb (length min_rest_path) 0) then
            curr_path
        else if (Nat.leb (length min_rest_path) (length curr_path)) then
            min_rest_path
        else
            curr_path
    )
    end
  end.

Definition shortest_path (g: Graph) (src: Node) (dst: Node) : list Node :=
    let path := (shortest_path_helper g [src] dst [] ((length g)*(length g))) in
    match rev path with 
    | v::l => if (Nat.eqb v dst) then   
                path
              else  
                []
    | _ => []
    end.

(* 
    TO Calculate the DIAMETER of the graph 
    We just assume that the diameter will be calculated only for connected graphs. ??
    Diameter = longest shortest path between any 2 pair of nodes
    - need the shortest distance between all pair of nodes
    - Then need the max value among all those
*)

Definition diameter (g : Graph) : nat :=
  let all_nodes := seq 1 (length g) in (* This can be done using a better helper function*)
  let pairs := all_pairs all_nodes in
  let diameters := map (fun '(src, dst) => length (shortest_path g src dst)) pairs in
  fold_right max 0 diameters.

(* Some Examples for Diameter *)
Definition example_diameter_graph : Graph := construct_dir_graph 7 [(1, 2); (2, 3); (2, 4); (2, 5); (2, 6); (6, 7)].

Example diameter_longest_path : 
 diameter example_diameter_graph = 3. 
Proof. reflexivity. Qed.


(* Additional Properties and some extensions for Graph *)

(* Walk in a graph *)   
Inductive is_walk: Graph -> list Node -> Prop :=
| walkOne : forall  g v, node_in g v -> is_walk g [v]
| walkOneStep : forall g u v l, edge_in g u v -> is_walk g (v::l) -> is_walk g (u :: v :: l).

Inductive has_no_duplicates: list Node -> Prop :=
| emptyNoDuplicates : has_no_duplicates []
| nonEmptyNoDuplicates: forall v l, not (In v l) -> has_no_duplicates (v::l).

Fixpoint tail_elem (l : list Node) :=
  match l with
  | [] => error
  | [x] => Some x
  | _ :: xs => tail_elem xs
  end.


Goal tail_elem [2;3;4] = Some 4.
Proof.
firstorder.
Qed.

Goal head [2;3;4] = Some 2.
Proof.
firstorder.
Qed.

(* Inductive head_tail_same : list Node -> Prop :=
| emptyHeadTailSame : head_tail_same []
| nonEmptyHeadTailSame: forall a l, head_tail_same (a::(l++[a])).

Compute (1::([2;3;4]++[5])).

Goal head_tail_same [1;2;1].
(* Goal head_tail_same (1::([2]++[1])). *)
Proof.
eapply nonEmptyHeadTailSame. *)

Fixpoint has_duplicates (l:list Node): Prop :=
    match l with 
    | nil => False
    | a::l1 => In a l1 \/ (has_duplicates l1)
    end.

    Goal not (has_duplicates [1;2;3]).
    Proof.
    unfold not. firstorder. easy. easy. easy.
    Qed.
    
    Goal has_duplicates [1;2;1;3].
    Proof.
    firstorder. 
    Qed.
    
        

Definition head_tail_same (l : list Node) :=
    (length l >=2) /\ (head l) = (tail_elem l).

    Goal head_tail_same [2;3;2].
    Proof.
    firstorder. simpl. lia.
    Qed.
    
    Goal not (head_tail_same [2]).
    Proof.
    unfold head_tail_same. firstorder. simpl. lia.
    Qed.

    Goal not( head_tail_same []).
    Proof.
    unfold not. unfold head_tail_same. firstorder. simpl in H. lia.
    Qed.

            
Definition is_path (g:Graph) (l: list Node) : Prop :=
    is_walk g l /\ (not (has_duplicates l)).


Definition is_cycle (g:Graph) (l: list Node) : Prop :=
        length l>=2 /\ is_walk g l /\ head_tail_same l.

Lemma head_tail_same_implies_duplicates:
    forall l, head_tail_same l -> has_duplicates l.
Proof.
intros. inversion H; subst;clear H. 
(* assert (exists a l1, a::l1=l). inversion H0. inversion H2. 
induction l.
- unfold head_tail_same. intros. simpl in H. firstorder. easy.
- intros. firstorder. simpl in H. inversion H; subst; clear H. destruct l. simpl in H. lia. simpl in H1. assert (In a (n::l)). simpl in H0.  *)
Admitted.


Lemma path_is_not_cycle: 
    forall g l, is_path g l -> not (is_cycle g l).
Proof.
    intros. unfold not, is_path, is_cycle. destruct H. intros. destruct H1. destruct H2. apply head_tail_same_implies_duplicates in H3. contradiction.
Qed.
Lemma cycle_is_not_path: 
    forall g l, is_cycle g l -> not (is_path g l).
Proof.
    intros. unfold not, is_path, is_cycle. destruct H. intros. destruct H1. destruct H0. apply head_tail_same_implies_duplicates in H3. contradiction.
Qed.


Definition is_reachable_walk (g:Graph) (u:Node) (v:Node): Prop :=
 exists walk, (length walk >=2) /\ is_walk g walk /\ ((head walk) = Some u) /\ ((tail_elem walk) = Some v).

Definition is_cyclic (g: Graph) : Prop :=
    exists l, is_cycle g l.
    (* The following does not work because false is difficult to prove *)
    (* exists v, node_in g v -> is_reachable_ind g v v. *)

Definition is_dag (g:Graph) : Prop :=
    is_cyclic g -> False.

Lemma in_dag_no_node_is_reachable_to_itself:
    forall g v, is_dag g -> node_in g v -> (not (is_reachable_walk g v v)).
Proof.
intros. unfold not. firstorder. (*Assuming a walk exists that starts and ends at the same node*)
 assert (is_cycle g x). firstorder. rewrite H4. firstorder. (* Proving that the walk should be a cycle*)  
 specialize (H x). simpl in H. firstorder. (*Proving that presence of a cylce contradicts that the graph is a DAG*)
Qed. 
    
(* Lemma no_node_is_reachable_to_itself_implies_dag:
    forall g v, node_in g v /\ (not (is_reachable_walk g v v)) -> is_dag g.
Proof.
 unfold is_dag.  firstorder. specialize (H1 x0). simpl in H1. firstorder. destruct H1. destruct x0. easy. simpl. inversion H2. easy. (*Assuming a walk exists that starts and ends at the same node*)
 assert (is_cycle g x). firstorder. rewrite H4. firstorder. (* Proving that the walk should be a cycle*)  
 specialize (H x). simpl in H. firstorder. (*Proving that presence of a cylce contradicts that the graph is a DAG*)
Qed.  *)

(* Example one_line_is_not_cyclic:
    ~ (is_cyclic one_line).
Proof.
    unfold is_cyclic. unfold not. firstorder. inversion H; subst; clear H. apply two_two_not_reachable_ind_in_one_line in H0. firstorder. inversion H; subst; clear H. apply one_one_not_reachable_ind_in_one_line in H0. firstorder.
Qed. *)


Example one_cycle_is_cyclic:
    is_cyclic one_cycle.
Proof.
    unfold is_cyclic. exists [1;2;1]. firstorder. simpl. lia. eapply walkOneStep. firstorder. unfold one_cycle. simpl. unfold node_in. exists [2]. firstorder.
    inversion H. inversion H. firstorder.
    eapply walkOneStep. firstorder. unfold one_cycle. simpl. unfold node_in. exists [1]. firstorder.
    inversion H. inversion H. firstorder.
    inversion H. eapply walkOne. unfold one_cycle. simpl. unfold node_in. exists [2]. firstorder. simpl. lia.
Qed.




Definition no_parent (g:Graph) (v:Node) : Prop :=
    forall v1, node_in g v1 -> ~ edge_in g v1 v.

Definition is_root (g:Graph) (v:Node) : Prop :=
    no_parent g v.

Example one_has_noparent_in_one_line:
    no_parent one_line 1.
Proof.
    unfold no_parent. firstorder. inversion H; subst; clear H. unfold not. intros. unfold one_line in H. unfold edge_in in H. simpl in H. destruct H. specialize (H0 []). firstorder.
    inversion H; subst; clear H.
    unfold not. intros. unfold one_line in H. unfold edge_in in H. destruct H. simpl in H. specialize (H0 [2]). firstorder. easy. lia.
Qed.


Lemma maximal_path_exists_in_dag:
    forall g , is_dag g -> (exists max_path, forall l, (is_path g max_path) /\ ((is_path g l) -> (length l <= length max_path ))).
Proof.
Admitted.


    
        
(* The following theorem requires knowledge that a path of maximum length occurs in a dag *)
Theorem dag_has_atleast_one_root: 
    forall g, is_dag g -> (exists v, node_in g v /\ no_parent g v).
Proof.
    intros.  apply  maximal_path_exists_in_dag in H. destruct H. 
Admitted.

(* Forest *)

Definition is_forest (g:Graph) : Prop :=
    is_dag g /\ (forall p1 p2 v, node_in g v -> (edge_in g p1 v -> edge_in g p2 v  -> p1 = p2)).
    
Example is_line_is_forest:
    is_forest one_line.
Proof.
    split.
    unfold is_dag. 
    (* apply one_line_is_not_cyclic. *)
    unfold one_line. simpl. unfold edge_in. intros. firstorder. inversion H; subst; clear H. unfold edge_in in H1. 
    (* destruct p1. *)
Admitted.

Definition is_connected_ind (g: Graph) : Prop :=
 forall u v, not (u = v) -> (is_reachable_walk g u v).


(* Is Graph a Tree *)

Definition is_tree (g: Graph):
    is_forest g /\ is_connected_ind g.



Definition is_leaf (g:Graph) (v: Node) :Prop :=
    (node_in g v) /\ (In (v, []) g).

(* The following theorem requires knowledge that a path of maximum length occurs in a dag *)
Theorem dag_has_atleast_one_leaf: 
    forall g, is_dag g -> (exists v, is_leaf g v).
Proof.
    (* Proof.
    intros.  apply  maximal_path_exists_in_dag in H. destruct H. 
Admitted. *)

Proof.
Admitted.

