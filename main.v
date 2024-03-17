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
Fixpoint construct_graph (n: nat) (edge_list : list Edge): Graph := 
    match edge_list with 
    | nil => (construct_empty_graph n)
    | (cons (u,v) edge_list1) => add_edge (construct_graph n edge_list1) u v
    end.

Example null_graph:=
    construct_graph 0 nil.
Example null_graph_is_null:
    null_graph = nil.
Proof.
    auto.
Qed.


Example two_cycle:
    construct_graph 2 [(1,2);(2,1)] = [(2,[1]);(1,[2])].
Proof.
    simpl. auto.
Qed.

(* Todo  ---> Prove that construct_graph function is correct. *)


Fixpoint is_connected (g : Graph) : Prop:=
    match g with 
    | nil => True
    | (v,e)::g1 => match e with
                    | nil => False
                    | _ => is_connected g1
                    end
    end.


Example null_graph_is_connected:
    is_connected null_graph.
Proof.
    simpl. auto.
Qed.

Example null_graph_is_not_connected:
    is_connected null_graph.
Proof.
    simpl. auto.
Qed.



