Require Import String Arith List Lia.
Import ListNotations.
Module Part1.
Definition node := nat.
Definition edge := (node , node).
Type edge.
Definition graph (n : node) (edge_list : (list edge) ) : list (node * list edge).

(* TODO := add the check to avoid duplicated edge addition *)
Fixpoint add_edge (adj : graph) (v1 v2: node): graph :=
match adj with
| nil => (cons (v1 (cons v2 nil)) nil) 
| (cons (x,edge_list) adj1) => if (Nat.eqb x v1) then  (cons (x,(cons v1 edge_list))) else (cons (x,edge_list) (add_edge adj1 (v1 v2))) 
end.
