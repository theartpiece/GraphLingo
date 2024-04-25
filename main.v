Require Import String Arith List Lia.
Import ListNotations.
(* Open Scope string_scope. *)
Module Part1.
(* ToDo: Should Node be [Definition Node] or [Notation Node]? Check HW1 to see what I am talking about *)
Notation Node := nat.
Definition Edge := (prod Node Node).
Definition EdgeList := (list Edge).
(* Type edge. *)
Definition Graph := list (prod Node (list Node)).
(* Definition Graph (n : Node) (edge_list : (list Edge) ) := list (prod Node (list Edge)). *)

(* TODO := add the check to avoid duplicated edge addition *)
Fixpoint add_edge (adj : Graph) (v1 v2: Node): Graph :=
      match adj with
      | nil => (cons (v1, (cons v2 nil)) nil) 
      | (cons (x,nghbrs) adj1) => 
                  if (Nat.eqb x v1) 
                  then    (cons (x, (cons v2 nghbrs)) adj1) 
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




(* Todo ---> Prove that construct_graph function is correct. *)


      

Fixpoint get_all_neighbors (g: Graph) (u : Node): (list Node):=
      match g with
      | nil => nil
      | (v,e)::g1 => 
                        if (Nat.eqb u v) 
                              then e ++ (get_all_neighbors g1 u)
                        else
                              let n1 := (get_all_neighbors g1 u) in 
                              if (andb (existsb (Nat.eqb u) e)    (negb (existsb (Nat.eqb v) n1)))
                                    then v::n1
                              else n1
      end.

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

(* Fixpoint is_reachable_in_k_steps (u v: Node) (k: nat): Prop :=
      match k with
      | 0 => if (Nat.eqb u v) then True else False
      | S => 
Fixpoint get_reachable_nodes_helper (g:Graph) (list_u: list Node) (list_seen : list Node): (list Node) :=
      match list_u with 
      | nil => nil
      | v::l => if (existsb (Nat.eqb v) list_seen)
                              then (get_reachable_nodes_helper g l list_seen)
                        else v::(get_reachable_nodes_helper g ((get_actual_neighbors g v) ++ l ) (v::list_seen))
      end.

Fixpoint is_cyclic_direc (g: Graph) : Prop := *)

(* --------------------------------------------- *)

(* Size of the Graph: Number of Nodes in the Graph *)
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
      intros v u H. simpl. destruct (Nat.eqb_spec u v); auto.
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
Lemma degree_add_edge : forall g v1 v2 v,
    In v (fst (split g)) ->
    (v = v1 \/ v = v2) -> degree (add_edge g v1 v2) v = S (degree g v).
Proof.
Admitted.

(* NOTE Can add more such lemmas like adding an edge does not disconnect the graph, ... *)
(* Property: The sum of degrees in an undirected graph equals twice the number of edges *)


(* //////////////////////// BFS and Diameter below //////////////////////*)

(* 
      TO Calculate the DIAMETER of the graph 
      We just assume that the diameter will be calculated only for connected graphs. ??
      Diameter = longest shortest path between any 2 pair of nodes
      - need the shortest distance between all pair of nodes
      - Then need the max value among all those
*)

(* Random Notes for BFS 
      do the fuel implementation: 
      1. can just do if it returns x then x is the right answer --> so can do that 
      fuel is at a certain equal to the number of nodes in the graph 
      if I am showing that they are very specific element then would have to deal with the case 
      and prove for completeness where if it returns None then what is it because the fuel runs out 
      or just when fuel is empty why this can never be the case
*)

(* Fixpoint bfs_helper_measure (g : Graph) (queue : list (list Node)) (visited : list Node) (distance : nat) (target : Node) : nat :=
    length queue.

Lemma bfs_helper_measure_decreasing : forall g queue visited distance target,
    length (queue) > length (queue ++ []) ->
    bfs_helper_measure g queue visited distance target > bfs_helper_measure g (queue ++ []) visited distance target.
Proof.
    intros.
    rewrite app_length in H.
    simpl in H.
    lia.
Qed. *)


(* 
      BFS to find the shortest path from source to target
      Returns a nat which is the shortest distance between source and target
      or returns None if there is no path
*)

(* Fixpoint bfs_helper (g : Graph) (queue : list (list Node)) (visited : list Node) (distance : nat) 
(target : Node): option nat :=
    match queue with
    | [] => None
    | path :: queue' =>
      let cur := hd 0 path in
      if Nat.eqb cur target then Some distance
      else if existsb (Nat.eqb cur) visited then bfs_helper g queue' visited distance target
      else let neighbors := get_children g cur in
             let new_paths := map (fun n => n :: path) neighbors in
             let queue'' := (queue' ++ new_paths) in
             bfs_helper g queue'' (cur :: visited) (S distance) target
    end. *)

(* Fixpoint bfs_helper (g : Graph) (queue : list (list Node)) (visited : list Node)
    (distance : nat) (target : Node) (termination_counter : nat): option nat :=
      match termination_counter with
      | O => None
      | S n =>
            match queue with
                  | [] => None
                  | path :: queue' =>
                        let cur := hd 0 path in
                        (* let num_nodes_visited := length path in *)
                        if Nat.eqb cur target then Some distance
                        else if existsb (Nat.eqb cur) visited then bfs_helper g queue' visited distance target (S n)
                        else let neighbors := get_all_neighbors g cur in
                        let new_paths := map (fun n => n :: path) neighbors in
                        let queue'' := queue' ++ new_paths in
                        bfs_helper g queue'' (cur :: visited) (S distance) target n
            end
end. *)


(* Definition bfs_shortest_path_distance (g : Graph) (source target : Node) : option nat :=
      bfs_helper g [[source]] [] 0 target get_size(g). *)

(* Fixpoint termination_helper (v: valuation) (c: cmd) (counter: nat) : valuation * cmd :=
match counter with
      | O => (v, c)
      | S counter =>
            match eval_cmd_once v c with
                  | Some (v', c') => eval_cmd_n v' c' fuel
                  | None => (v, c)
            end
end. *)

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


(* Definition diameter (g : Graph) (nodes : list Node) : nat :=
      match nodes with
      | nil => None
      | _ =>
          let distances := map (fun p => bfs_shortest_path_distance g (fst p) (snd p)) (all_pairs nodes) in
          let max_distance := fold_left (fun d opt_dist => match opt_dist with Some dist => max d dist | None => d end) distances 0 in
          Some max_distance
      end. *)


(* Function to calculate the diameter of a graph *)
(* Definition diameter (g : Graph) : nat :=
      let dist_from_source (source : Node) :=
          let rec bfs (queue : list (Node * nat)) (visited : list Node) : nat :=
            match queue with
            | [] => O
            | (cur, d) :: queue' =>
                if existsb (Nat.eqb cur) visited then bfs queue' visited
                else let neighbors := get_all_neighbors g cur in
                       let new_queue := queue' ++ map (fun n => (n, S d)) neighbors in
                       bfs new_queue (cur :: visited)
            end
          in bfs [(source, O)] []
      in let all_nodes := map fst g in
           let distances := map dist_from_source all_nodes in
           fold_right max 0 distances. *)
    
    (* Some Examples to start with *)
    
    (* Example one_line :=
      construct_undir_graph 2 [(1, 2)].
    
    Example null_graph :=
      construct_undir_graph 0 nil.

    Compute (diameter one_line). (* Output: 1 *)
    Compute (diameter null_graph). (* Output: 0 *)
     *)
    (* Add some proofs for bfs and diameter *)






(*=============== DFS ==================*)

(*  Small Step Semantics Definition of DFS *)

(* 
      Defines 3 different kinds of steps
      -   A node that has already been visited
      -   A node that has not yet been visited
      -   DFS Initialization
*)
Inductive DfsStep : Graph * list Node * list Node -> Graph * list Node * list Node -> Prop :=
| DfsStepVisited : forall g vis st v,
      ~ In v vis -> DfsStep (g, vis, v :: st) (g, v :: vis, (get_children g v) ++ st)
| DfsStepVisit : forall g vis st v,
      In v vis -> DfsStep (g, vis, v :: st) (g, vis, st)
| DfsStepStart : forall g v,
      DfsStep (g, [], []) (g, [], [v]).

(* 
      Defines the properties of the small step semantics
      -   Reflexivity
      -   Transitivity
*)
Inductive DfsStepStar : Graph * list Node * list Node -> Graph * list Node * list Node -> Prop :=
| DfsStepRefl : forall g vis st,
      DfsStepStar (g, vis, st) (g, vis, st)
| DfsStepStarOnce : forall g vis1 vis2 vis3 st1 st2 st3,
      DfsStep (g, vis1, st1) (g, vis2, st2) -> DfsStepStar (g, vis2, st2) (g, vis3, st3) -> DfsStepStar (g, vis1, st1) (g, vis3, st3).
      
(* 
      Now let us verify that the small step semantics defined above works on some sample graphs

      Consider a graph with the following adjacency list. The graph has been illustrated below for further clarity.
            1: 2, 5
            2: 3, 7
            3: 4
            4: 9
            5: 7
            6: 8
            7:
            8:
            9:

            1 --> 2 --> 3 --> 4 --> 9
            |     |     ^               
            v     v     |               
            5 --> 7 ----+               
                  
            6 --> 8
*)

Definition sample_graph := 
      construct_dir_graph 9 [(1,2); (1,5); (2,3); (2,7); (3,4); (4,9); (5,7); (7,3); (6,8)].

Example dfs_step_identity:
      DfsStep(sample_graph,[],[1])(sample_graph,[1],[2;5]).
Proof.
      econstructor. auto.
Qed.

Example dfs_identity_step_star:
      DfsStepStar(sample_graph,[],[1])(sample_graph,[1],[2;5]).
Proof.
      repeat econstructor. auto.
Qed.

Lemma dfs_step_from_one_to_four:
      exists vis st, DfsStepStar(sample_graph, [], [1])(sample_graph, 4::vis, st).
Proof.
      repeat econstructor. 
      - auto.
      - unfold not. simpl. intros. destruct H. lia. lia.
      - unfold not. simpl. intros. destruct H. lia. lia.
      - unfold not. simpl. intros. destruct H. lia. lia.
Qed.

Lemma dfs_step_from_five_to_nine:
      exists vis st, DfsStepStar(sample_graph, [], [5])(sample_graph, 9::vis, st).
Proof.
      repeat econstructor. 
      - auto.
      - unfold not. simpl. intros. destruct H. lia. lia.
      - unfold not. simpl. intros. destruct H. lia. lia.
      - unfold not. simpl. intros. destruct H. lia. lia.
      - unfold not. simpl. intros. destruct H. lia. lia.
Qed.



(* 
      Next we define a fuel based implementation of the dfs algorithm
*)

Fixpoint dfs_helper (g : Graph) (start: Node) (fuel : nat) (visited : list Node) : list Node :=
    match fuel with
    | 0 => visited
    | S fuel' =>
          if (existsb (Nat.eqb start) visited)
			then visited
			else 
			let visited' := start :: visited in 
			let children := get_children g start in
			fold_left (fun acc v => dfs_helper g v fuel' acc) children visited'
    end.

Definition dfs (g : Graph) (start : Node) : list Node :=
      dfs_helper g start (length g) [].

(* 
      Again, let us verify the behaviour of the fuel based definition of DFS
      Consider the sample graph from above.

            1 --> 2 --> 3 --> 4 --> 9
            |     |     ^               
            v     v     |               
            5 --> 7 ----+               
                  
            6 --> 8
*)

Lemma dfs_from_one_visits_one:
      In 1 (dfs sample_graph 1).
Proof.
      simpl. lia.
Qed.

Lemma dfs_from_one_visits_four:
      In 4 (dfs sample_graph 1).
Proof.
      simpl. lia.
Qed.

Lemma dfs_from_five_visits_nine:
      In 5 (dfs sample_graph 1).
Proof.
      simpl. lia.
Qed.

Lemma dfs_from_five_does_not_visit_nine:
      ~ In 6 (dfs sample_graph 5).
Proof.
      simpl. unfold not. intros. 
      destruct H. lia.
      destruct H. lia.
      destruct H. lia.
      destruct H. lia.
      destruct H. lia.
      destruct H.
Qed.

(* 
      Here, we prove that our step semantics for DFS only visits a node one time.

      First, we define a helper lemma that helps us reason about lists.
*)

Lemma not_cons_self : forall (A : Type) (x : A) (l : list A), l <> x :: l.
Proof.
intros A x l.
intro H.
induction l as [| y l' IHl].
- discriminate H. 
- injection H as H1 H2. rewrite H1 in H2.
    apply IHl in H2.
    contradiction.
Qed.


(* 
      The below theorem shows that any step dfs takes must result in only new values being added to visited.
*)

Theorem dfs_step_has_unique_values_in_visited:
      forall g v visited stack stack', DfsStep(g, visited, stack)(g, v::visited, stack') -> ~ In v visited.
Proof.
      intros. repeat econstructor. 
      intro. inversion H. subst. 
      - contradiction. 
      - apply not_cons_self in H5. contradiction. 
Qed.


(* Definition only_one_occurrence (x : Node) (lst : list Node) : Prop :=
  forall y, In y lst -> x = y -> forall z, In z lst -> x = z.


  Fixpoint fold_right_concat (l : list (nat * list nat)) : list nat :=
      match l with
      | nil => nil
      | (x, ys) :: l' => ys ++ fold_right_concat l'
      end.
      Lemma in_concat_list_both_directions : forall v y l,
      (exists l', In (v, l') l) ->
      (exists l', In y l') ->
      In y (fold_right_concat l).
    Proof.
      intros v y l H1 H2.
      induction l as [| (x, ys) l' IH]; simpl in *.
      - destruct H1 as [l' H].
        contradiction.
      - destruct H1 as [l'' H].
        destruct H as [H | H].
        + inversion H; subst.
          apply in_or_app.
          left; assumption.
        + apply IH; assumption.
    Qed. *)
  

(* 
      Shortest Path Between nodes A and B
      
      We now define a function that computes the shortest path between 2 nodes A nd B in a graph
      
      It does this by iteratively checking the shortest path to the destination from all of 
      the neighbour's of the source and choosing the minimum of those paths. 

      It does this recursively until it gets the shortes path if such a path exists

*)

Fixpoint shortest_path_helper (g: Graph) (srcs : list Node) (dst: Node) (visited: list Node) (fuel: nat): list Node :=
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

(* Compute shortest_path_helper another_sample_graph (get_children another_sample_graph 3) 8 [3] 99. *)
(* Compute shortest_path_helper another_sample_graph [1] 8 [] 99. *)

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
      We verify the working of the shortest path computation using the following sample graph
      1---2---3
      |\  |    |
      | \ |    |
      4    5    |
      |    |    |
      6---7---8
            |    
            9
*)

Definition another_sample_graph := 
      construct_dir_graph 9 [(1,2); (1,5); (1,4); (2,3); (2,5); (3,8); (4,6); (5,7); (6,7); (7,8); (7,9)].

Lemma shortest_path_from_one_to_one:
      (shortest_path another_sample_graph 1 1) = [1].
Proof.
      auto.
Qed.

Lemma shortest_path_from_one_to_three:
      (shortest_path another_sample_graph 1 3) = [1;2;3].
Proof.
      auto.
Qed.

Lemma shortest_path_from_one_to_seven:
      (shortest_path another_sample_graph 1 7) = [1;5;7].
Proof.
      auto.
Qed.

Lemma shortest_path_from_one_to_eight:
      (shortest_path another_sample_graph 1 8) = [1;5;7;8].
Proof.
      auto.
Qed.

(* 
	Here we try to prove that the shortest path from a node to itself uses only one node
*)

Lemma shortest_path_from_five_to_one:
      (shortest_path another_sample_graph 5 1) = [].
Proof.
      auto.
Qed.

Lemma a_greater_than_1_implies_a_star_a_greater_than_1:
    forall (a: nat), a >= 1 -> (a*a) >= 1.
Proof.
    intros. assert (1 = 1*1) as Hx. auto. rewrite Hx. 
    apply Nat.mul_le_mono. auto. auto.
Qed.

Lemma equality_of_decidable_nat:
    forall (n: nat), (n =? n) = true.
Proof.
    intros. destruct (n =? n) eqn:Heq.
    - reflexivity.
    - rewrite Nat.eqb_neq in Heq.
      exfalso. apply Heq.
      reflexivity.
Qed.

Theorem shortest_path_helper_to_self_is_of_length_one:
    forall g v fuel, fuel >= 1 -> (shortest_path_helper g [v] v [] fuel) = [v].
Proof. 
    intros. destruct fuel.
    - inversion H.
    - simpl. destruct (v =? v) eqn:Hx. auto. 
    specialize (equality_of_decidable_nat v). intro. 
    rewrite Hx in H0. inversion H0.
Qed.

Theorem shortest_path_to_self:
    forall g v, (length g) >= 1 -> length(shortest_path g v v) = 1.
Proof.
    intros. simpl. unfold shortest_path. assert (length g * length g >= 1). 
    apply a_greater_than_1_implies_a_star_a_greater_than_1. auto.
    destruct (length g * length g) eqn:Hx.
    - inversion H0.
    - specialize (shortest_path_helper_to_self_is_of_length_one   g v (S n)). 
    intro. assert (shortest_path_helper g [v] v [] (S n) = [v]).
    apply H1. apply H0. rewrite H2. simpl. 
    specialize (equality_of_decidable_nat v). intro. rewrite H3. auto.
Qed.

(* 
	Identifying Bipartite Graphs
	Below is a function that decides whether a graph is bipartite
*)

(* 
      This is bipartite helper function that splits a single connected component
      nto left and right sets.
*)
Fixpoint bipartite_helper (g : Graph) (start: Node) (args: (list Node * list Node * list Node)) (fuel : nat) (which: bool) : (list Node * list Node * list Node) :=
  match fuel with
    | 0 => args
    | S fuel' =>
          let '(visited,l,r) := args in
          if (existsb (Nat.eqb start) visited)
          then args
          else
          let visited' := start :: visited in 
          let children := get_children g start in
          if which then
          let left' := start :: l in 
          let right' := (get_children g start) ++ r in 
          fold_right (fun v a => bipartite_helper g v a fuel' (negb which) ) (visited',left',right') children
          else 
          let left' := (get_children g start) ++ l in 
          let right' := start::r in 
          fold_right (fun v a => bipartite_helper g v a fuel' (negb which) ) (visited',left',right') children
    end.


(* 
      This function performs the left-right split for each component
*)
Fixpoint bipartite_components (g : Graph) (lg: Graph) (args: (list Node * list Node * list Node)) : (list Node * list Node * list Node):=
  match lg with
  | [] => args
  | (v,e)::x => 
    let '(visited,l,r) := (bipartite_helper g v args (length g) true) in
    bipartite_components g x (visited,l,r)
  end.
  
(* 
      This function checks whether the final sets are disjoint
*)
Fixpoint bipartite_checker (g: Graph) (l: list Node) (r: list Node) : bool :=
  match g with
  | [] => true
  | (v,e)::x => if (existsb (Nat.eqb v) l)
               then if ((existsb (Nat.eqb v) r))
               then false
               else (bipartite_checker x l r)
               else (bipartite_checker x l r)
  end.
    
(* 
      This function is the wrapper that checks whether a graph is bipartite
*)
Definition is_bipartite (g: Graph) : (bool * list Node * list Node) :=
  let '(visited,l,r) := (bipartite_components g g ([],[],[])) in
  match (bipartite_checker g l r) with 
  | true => (true, l, r)
  | false => (false, [], [])
  end.
  
Definition a_bipartite_graph := 
	construct_undir_graph 9 [(1,4); (2,4); (2,5); (3,5); (3,6); (7,8)].


Lemma a_bipartite_graph_is_bipartite :
      let '(i,l,r) := (is_bipartite a_bipartite_graph) in
      i = true .
Proof.
      simpl. auto.
Qed.

Definition not_a_bipartite_graph := 
	construct_undir_graph 9 [(1,4); (2,4); (2,5); (3,5); (3,6); (7,8); (5,6)].

Lemma not_a_bipartite_graph_is_bipartite :
      let '(i,l,r) := (is_bipartite not_a_bipartite_graph) in
      i = false .
Proof.
      simpl. auto.
Qed.

(* 
      Function that counts the components in a graph.
*)

Fixpoint number_components_helper (g: Graph) (lg: Graph) (visited: list Node) : nat :=
  match lg with
  | [] => 0
  | (v,e)::x =>
    if (existsb (Nat.eqb v) visited)
    then (number_components_helper g x visited)
    else 
    S (number_components_helper g x (dfs_helper g v (length g) visited))
  end.
  
Definition number_components (g: Graph) : nat :=
  number_components_helper g g [].
  

Definition two_component_graph := 
	construct_undir_graph 8 [(1,2); (2,3); (1,4); (3,4); (5,8); (5,7); (6,8) ].

Lemma check_two_component_graph: 
      number_components two_component_graph = 2.
Proof.
      auto.
Qed.

Definition three_component_graph := 
	construct_undir_graph 10 [(1,2); (2,3); (1,4); (3,4); (5,8); (5,7); (6,8);  (9,10)].

Lemma check_three_component_graph: 
      number_components three_component_graph = 3.
Proof.
      auto.
Qed.
