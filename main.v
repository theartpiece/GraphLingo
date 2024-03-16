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


(**
Let's define the semantics for our language. This will be mostly the same as in lecture, but we need
to decide how to define the [Var] case. This will require a digression to talk about equality.

So far, we have talked mostly about equality as a *proposition*---a logical sentence that might be
known to be true (if it's a hypothesis, or a theorem proven elsewhere), or might be a goal we need
to prove to be true. We saw that we can use [rewrite] to exploit equality propositions to transform
our goals, and tactics like [reflexivity] to prove trivial equality propositions. But in many real
programs, we want to talk about equality as a *value*---a boolean we can compute by comparing two
values.

The reason to make this distinction is that Coq *does not assume* that equality is *decidable*. In
other words, Coq does not assume that it is always possible to compute a boolean that compares two
values for equality.
*)

(***************************************************************************************************
PROBLEM 1 [2 points]: In a sentence or two, give an example of a equality relation you can think of
(from anywhere, not necessarily in Coq) that is not decidable.

ANSWER: 



*)

(**
That discussion aside, it's often convenient to be able to talk about decidable equality over types
we use every day, like [nat] and [string]. Luckily, Coq's standard library already specifies that
equality over these types and others is decidable. Let's define [var] as a string, and write down a
[var_eq] function that can compare two [var]s for equality:
*)

Definition var_eq : forall (v1 v2 : var), {v1 = v2} + {v1 <> v2} := string_dec.

(**
We won't talk too much about what this type means, but there is no magic going on here. You should
think about [var_eq] as a function that takes as input two [var]s and either returns a proof that
they are equal or a proof that they are not equal. It does this by using the [string_dec] function
to *compute* whether the two are equal, which is why this function does not exist for every type. In
practice, this means we can use [var_eq] in function definitions as the condtitional part of an
if/then/else expression. Take a look at the definition of [string_dec] in the standard library if
you're curious about this.

Let's get a little experience with this notion of equality using a somewhat silly example.

Here is a function that computes the "goodness" score of a variable name, as a natural number. It's
a completely subjective function that enforces my personal opinion about the best variable names.
The ["i"%string] syntax just tells Coq to interpret the quotes as a [string]; you might need to use
this same syntax in Problem 2 below.
*)
Definition var_name_goodness (v: var) : nat :=
    if var_eq v "i"%string
    then 0
    else if var_eq v "james"%string
    then 50
    else 10.

(***************************************************************************************************
PROBLEM 2 [4 points]: prove the following lemma about the values [var_name_goodness] can return.

HINT: You can write [destruct (var_eq a b)] to split the proof into two cases, one where [a] equals
[b] and one where [a] does not equal [b]. You might also find the [unfold x] tactic useful to force
Coq to expand a definition [x].
*)
Lemma var_name_goodness_is_not_42:
    forall v, var_name_goodness v <> 42.
Proof.
    (* TODO *)
    intro v.
    unfold var_name_goodness.
    destruct var_eq.
    auto.
    destruct var_eq.
    lia.
    lia.
Qed.

(**
To give a semantics for the [expr] language, we need a way to evaluate the [Var] case. We'll do this
by providing our semantics with a *variable map* that takes as input a [var] and returns the [nat]
it evaluates to. We'll encode variable maps as functions.
*)

Definition var_map := var -> nat.

(* Update a variable map with a new mapping *)
Definition set_map (m : var_map) (var : var) (value : nat) : var_map :=
    fun v => if var_eq var v then value else m v.

(* A variable map that assigns the same value to every variable *)
Definition const_map (value : nat) : var_map :=
    fun _ => value.