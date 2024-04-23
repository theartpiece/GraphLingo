Require Import String Arith List Lia Logic.
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

Definition node_in (g: Graph) (n : Node) : Prop :=
    exists edge_list, In (n, edge_list) g.

Example one_in_one_line:
    node_in one_line 1.
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
    forall ngbhrs_list, In (u, ngbhrs_list) g  ->  In v ngbhrs_list.

(* g = [(1, [2,3,4]), (3, [4,5])] *)
(* g = [(1, [2,3,4]), (3, [4,5]), (1, [5])]  -- this does not exist in our exmaplewas*) 
(* edge_in g 1 2 = True *)
(* edge_in g 2 1 = False *)

    (* exists edge_list, (In (u, edge_list) g  /\  In v edge_list). *)

Example one_two_in_one_line:
    edge_in one_line 1 2.
Proof.
    (* simpl. unfold edge_in. unfold one_line. simpl. intros. split. destruct (1, edge_list). inversion H. easy. inversion H0. inversion H1. apply in_eq. easy.  *)
    simpl. unfold edge_in. unfold one_line. simpl. intros. inversion H. easy. inversion H0. inversion H1. apply in_eq. easy. 
Qed.

Example two_one_not_in_one_line:
    edge_in one_line 2 1 -> False.
Proof.
    intros .
    unfold edge_in in H.
    unfold one_line in H.
    simpl in H.
    specialize (H []).
    firstorder.
Qed.

Example one_three_not_in_one_line:
    edge_in one_line 1 3 -> False.
Proof.
    unfold not. simpl. unfold edge_in. unfold one_line. simpl. intros. eauto. specialize (H [2]). firstorder. easy.
Qed.


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




Definition is_cyclic_ind (g: Graph) : Prop :=
    exists v, node_in g v /\ is_reachable_ind g v v.
    (* The following does not work because false is difficult to prove *)
    (* exists v, node_in g v -> is_reachable_ind g v v. *)

Example one_line_is_not_cyclic:
    ~ (is_cyclic_ind one_line).
Proof.
    unfold is_cyclic_ind. unfold not. firstorder. inversion H; subst; clear H. apply two_two_not_reachable_ind_in_one_line in H0. firstorder. inversion H; subst; clear H. apply one_one_not_reachable_ind_in_one_line in H0. firstorder.
Qed.


Example one_cycle_is_cyclic:
    is_cyclic_ind one_cycle.
Proof.
    exists 1. split. 
    unfold node_in. unfold one_cycle. simpl. exists [2]. firstorder.
    apply one_one_reachable_in_one_cycle.
Qed.

Definition is_dag (g:Graph) : Prop :=
    is_cyclic_ind g -> False.



Definition no_parent (g:Graph) (v:Node) : Prop :=
    forall v1, node_in g v1 -> ~ edge_in g v1 v.

Example one_has_noparent_in_one_line:
    no_parent one_line 1.
Proof.
    unfold no_parent. firstorder. inversion H; subst; clear H. unfold not. intros. unfold one_line in H. unfold edge_in in H. simpl in H. specialize (H []). firstorder.
    inversion H; subst; clear H.
    unfold not. intros. unfold one_line in H. unfold edge_in in H. simpl in H. specialize (H [2]). firstorder. easy.
Qed.


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


Definition head_tail_same (l : list Node) :=
    length l >= 2 /\ ((head l) = (tail_elem l)).

Goal head_tail_same [2;3;2].
Proof.
unfold head_tail_same. split. unfold length. lia. firstorder.
Qed.

    
Definition is_path (g:Graph) (l: list Node) : Prop :=
    is_walk g l /\ has_no_duplicates l.


Definition is_cycle (g:Graph) (l: list Node) : Prop :=
        is_walk g l /\ head_tail_same l.

Lemma head_tail_same_implies_duplicates:
    forall l, head_tail_same l -> not ( has_no_duplicates l).
Proof.
induction l.
- unfold head_tail_same. intros. destruct H. simpl in H. firstorder. easy.
-intros. destruct H. 
Admitted.

Lemma path_is_not_cycle: 
    forall g l, is_path g l -> not (is_cycle g l).
Proof.
    (* induction l.
    - unfold not. intros. inversion H; subst; clear H. inversion H0; subst; clear H0. unfold head_tail_same in H3. inversion H3. simpl in H0. lia.
    - intros. unfold not.  intros. inversion H . eapply walkOneStep in H1. inversion H2. simpl in H. *)
    intros. unfold not, is_path, is_cycle. destruct H. intros. destruct H1. eapply head_tail_same_implies_duplicates in H0. easy. easy.
Qed.

Lemma maximal_path_exists_in_dag:
    forall g l , is_dag g -> (exists max_path, (is_path g max_path) /\ ((is_path g l) -> (length l <= length max_path ))).
Proof.
Admitted.


    
        
(* The following theorem requires knowledge that a path of maximum length occurs in a dag *)
Theorem dag_has_atleast_one_root: 
    forall g, is_dag g -> (exists v, node_in g v /\ no_parent g v).
Proof.
    intros. firstorder. 
Admitted.



Definition is_forest (g:Graph) : Prop :=
    is_dag g /\ (forall p1 p2 v, node_in g v -> (edge_in g p1 v -> edge_in g p2 v  -> p1 = p2)).
    
Example is_line_is_forest:
    is_forest one_line.
Proof.
    split.
    unfold is_dag. apply one_line_is_not_cyclic.
    unfold one_line. simpl. unfold edge_in. intros. firstorder. inversion H; subst; clear H. unfold edge_in in H1. destruct p1.
Admitted.

Definition is_connected_ind (g: Graph) : Prop :=
 forall u v, (not (u = v) /\ node_in g u /\ node_in g v) -> (is_reachable_ind g u v  \/ is_reachable_ind g v u).



Definition is_tree (g: Graph):
    is_forest g /\   g.



Definition is_leaf (g:Graph) (v: Node) :Prop :=
    (node_in g v) /\ (In (v, []) g).

Proof.
Admitted.


Theorem tree_has_1_less_internal_nodes_than_leaves:
    True.


