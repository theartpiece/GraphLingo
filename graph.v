Require Import String Arith List Lia.
Import ListNotations.

Definition Node := nat.

Inductive Edge : Type :=
| E : Node -> Node -> Edge.

(* Define a type for graphs *)
Definition EdgeListGraph := list Edge.

(* Function to check if an edge already exists *)
Fixpoint edge_exists (graph : EdgeListGraph) (n1 n2 : Node) : bool :=
  match graph with
  | [] => false
  | (E u1 u2) :: rest =>
    (n1 =? u1) && (n2 =? u2) || (n1 =? u2) && (n2 =? u1) || edge_exists rest n1 n2
  end.

(* Function to add an edge to the graph if it doesn't already exist *)
Definition add_edge (graph : EdgeListGraph) (n1 n2 : Node) : EdgeListGraph :=
  if edge_exists graph n1 n2 then graph
  else (E n1 n2) :: graph.

  Definition example_graph : EdgeListGraph :=
    add_edge [] 1 2.

Definition empty_graph : EdgeListGraph := [].

(* Breadth-First Search *)
Definition bfs (graph : Graph) (start : Node) : list Node :=
  let fix bfs_helper (queue visited : list Node) : list Node :=
      match queue with
      | [] => visited
      | v :: rest =>
          if (In_dec Nat.eq_dec v visited) then bfs_helper rest visited
          else bfs_helper (rest ++ graph v) (visited ++ [v])
      end
  in bfs_helper [start] [].

Definition example_adj_list_graph : Graph :=
  add_edge (add_edge (add_edge empty_graph 1 2) 2 3) 3 1.

Compute (bfs example_adj_list_graph 1).
