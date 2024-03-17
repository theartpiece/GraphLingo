Require Import String Arith List Lia.
Import ListNotations.
Open Scope string_scope.
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

Fixpoint construct_bidir_graph (n: nat) (edge_list : list Edge): Graph := 
    match edge_list with 
    | nil => (construct_empty_graph n)
    | (cons (u,v) edge_list1) => add_edge (construct_bidir_graph n edge_list1) u v
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
    construct_bidir_graph 2 [(1,2)].
Example one_line_is_correct:
    one_line = [(2,[]);(1,[2])].
Proof.
    simpl. auto.
Qed.




(* Todo  ---> Prove that construct_graph function is correct. *)


    

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

Fixpoint get_actual_neighbors (g: Graph) (u : Node): (list Node):=
    match g with
    | nil => nil
    | (v,e)::g1 => 
                if (Nat.eqb u v) 
                    then e 
                else
                    get_actual_neighbors g1 u
    end.


Example all_nghbrs_of_1_in_two_cycle:
    get_all_neighbors two_cycle 1 = [2].
Proof.
    simpl. auto.
Qed.

Example actual_nghbrs_of_1_in_one_line:
    get_actual_neighbors one_line 1 = [2].
Proof.
    simpl. auto.
Qed.

Example actual_nghbrs_of_2_in_one_line:
    get_actual_neighbors one_line 2 = nil.
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
    construct_bidir_graph 3 [(1,2)].

Example one_line_one_node_is_not_connected:
    not (is_connected one_line_one_node).
Proof.
    simpl. auto.
Qed.

Fixpoint get_reachable_nodes_helper (g:Graph) (list_u: list Node): (list Node) :=
    match list_u with 
    | nil => nil
    | v::l => let rest := (get_reachable_nodes_helper g l ) in 
                match get_actual_neighbors g v with
                    | nil => v::rest
                    | nl => (v::(get_reachable_nodes_helper g nl))++rest
                end
    end.

Fixpoint is_cyclic_bidirec (g: Graph) : Prop :=





