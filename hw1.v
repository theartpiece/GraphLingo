(** * CS 345H: Homework 1 *)

(**
There are a total of 106 points available in this file across 18 problems. There is also one extra
credit problem (Problem 11) worth 6-12 points.
*)

(**
A quick reminder about the rules for Coq homework in this class:
- You cannot use any Coq libraries beyond the ones imported below.
- You can use any tactic available in these libraries, including ones we haven't seen in lecture.
- You must not edit any theorems or definitions that are already provided, unless a problem
  explicitly asks you to. This rule holds even if the edit seems "trivial", like changing "1 + x" to
  "x + 1".
- You can add new theorems and definitions if you want to.
*)

Require Import String Arith List Lia.
Import ListNotations.

(* This file is in two parts because we're studying two slightly different languages. [Module] just
lets us contain our definitions to one part of the homework. *)
Module Part1.

(**
In this part we're going to revisit the [expr] language we saw in lecture, but this time extended
with variables. Our language still won't have assignment, so variables will always be constant, but
adding variables will give us a chance to get some practice with *equality* in Coq. Let's start by
just declaring a new type for variables, which we'll just represent as strings:
*)

Definition var := string.

(**
Here's the syntax for our [expr] language, like we saw in class but with an extra case for
variables:
*)

Inductive expr :=
| Const (n : nat)
| Var (v : var)
| Plus (e1 e2 : expr)
| Times (e1 e2 : expr).

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

(**
With this definition, "reading" a variable is just applying the variable map function to the
variable name.
*)
Example read_var:
    (const_map 5) "x"%string = 5.
Proof. auto. Qed.

(***************************************************************************************************
PROBLEM 3 [4 points]: prove the following lemma about [set_map]'s effect on other variables.
*)
Lemma set_map_unchanged:
    forall map var1 var2 value, var1 <> var2 -> (set_map map var1 value) var2 = map var2.
Proof.
    (* TODO *)
    intros. unfold set_map. destruct var_eq. contradiction. auto.
Qed.

(**
Now we have everything we need to define a denotational semantics for [expr].
*)

Fixpoint eval_expr (e : expr) (m : var_map) : nat :=
match e with
| Const n => n
| Var v => m v
| Plus e1 e2 => eval_expr e1 m + eval_expr e2 m
| Times e1 e2 => eval_expr e1 m * eval_expr e2 m
end.

(**
Let's do some proofs about [expr]. Recall this [flip] functions from class:
*)

Fixpoint flip (e: expr) : expr :=
match e with
| Const n => Const n
| Var v => Var v
| Plus e1 e2 => Plus (flip e2) (flip e1)
| Times e1 e2 => Times (flip e2) (flip e1)
end.

(***************************************************************************************************
PROBLEM 4 [4 points]: Prove the following lemma about [flip] being its own inverse.
*)
Lemma flip_involutive:
    forall e, flip (flip e) = e.
Proof.
    (* TODO *)
    intros.
    induction e.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. rewrite IHe1. rewrite IHe2. reflexivity.
    - simpl. rewrite IHe1. rewrite IHe2. reflexivity.
    
Qed.

(**
Here's another function about [expr] syntax that just counts the number of [Var] expressions in a
program.
*)

Fixpoint count_vars (e: expr) : nat :=
match e with
| Const n => 0
| Var v => 1
| Plus e1 e2 => count_vars e1 + count_vars e2
| Times e1 e2 => count_vars e1 + count_vars e2
end.

(***************************************************************************************************
PROBLEM 5 [4 points]: Prove the following lemma about the relationship between [flip] and
[count_vars].
*)
Lemma flip_preserves_count_vars:
    forall e, count_vars e = count_vars (flip e).
Proof.
    (* TODO *)
    induction e.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. rewrite IHe1. rewrite IHe2. lia.
    - simpl. rewrite IHe1. rewrite IHe2. lia.
Qed.

(**
Here's the [size] function from lecture:
*)

Fixpoint size (e: expr) : nat :=
match e with
| Const n => 1
| Var v => 1
| Plus e1 e2 => 1 + size e1 + size e2
| Times e1 e2 => 1 + size e1 + size e2
end.

(***************************************************************************************************
PROBLEM 6 [4 points]: Prove the following relantionship between [count_vars] and [size].
*)
Lemma count_vars_bounded_by_size:
    forall e, count_vars e <= size e.
Proof.
    (* TODO *)
    induction e.
    - simpl. auto.
    - simpl. auto.
    - simpl. Search ( _ + _ <= S _ ). rewrite Nat.le_succ_diag_r. apply -> Nat.succ_le_mono. lia.
    - simpl. Search ( _ + _ <= S _ ). rewrite Nat.le_succ_diag_r. apply -> Nat.succ_le_mono. lia.
Qed.

(***************************************************************************************************
PROBLEM 7 [6 points]: Prove the following lemma about how expressions without variables evaluate.

HINT: The [destruct H] tactic can split a conjunctive hypothesis [H: a /\ b] into two hypotheses [a]
and [b].
*)
Lemma zero_vars_independent:
    forall e, count_vars e = 0 -> (forall m1 m2, eval_expr e m1 = eval_expr e m2).
Proof.
    (* TODO *)
    induction e.
    - simpl. auto.
    - simpl. lia.
    - simpl. Search (_ + _ = 0). rewrite Nat.eq_add_0. intuition.
    - simpl. Search (_ + _ = 0). rewrite Nat.eq_add_0. intuition. 
Qed.

(**
Here is a function that renames a variable in a program. Renaming variables (sometimes called alpha
conversion) is a surprisingly difficult problem in general, as we'll discover later in the semester
when we study the lambda calculus, but for our simple [expr] language it's pretty easy.
*)

Fixpoint rename (e : expr) (from to : var) : expr :=
match e with
| Const _ => e
| Var n => if var_eq from n then Var to else e
| Plus e1 e2 => Plus (rename e1 from to) (rename e2 from to)
| Times e1 e2 => Times (rename e1 from to) (rename e2 from to)
end.

(***************************************************************************************************
PROBLEM 8 [6 points]: Prove the following lemma showing that [rename] preserves the semantics of
[expr] programs so long as the old and new variables have the same value.
*)
Theorem rename_preserves_semantics:
    forall e m from to, m from = m to -> eval_expr e m = eval_expr (rename e from to) m.
Proof.
    (* TODO *)
    (* intros. destruct rename. simpl. *)

    simpl. intros. simpl. induction e.
    - simpl. auto.
    - simpl. destruct var_eq. simpl. rewrite <- e. auto. simpl. auto. 
    - simpl. auto.
    - simpl. auto.
Qed.

(**
Let's do something fancier with [expr] now. A common optimization that compilers perform is
*constant folding*: computing expressions at compile time when they are entirely constant. The
important thing here is that constant folding does not know the value of any variables.

Here's a constant folding implementation for [expr]:
*)
Fixpoint constant_fold (e : expr) : expr :=
match e with
| Const _ => e
| Var _ => e
| Plus e1 e2 =>
  let e1' := constant_fold e1 in
  let e2' := constant_fold e2 in
  match e1', e2' with
  | Const n1, Const n2 => Const (n1 + n2)
  | Const 0, _ => e2'
  | _, Const 0 => e1'
  | _, _ => Plus e1' e2'
  end
| Times e1 e2 => 
  let e1' := constant_fold e1 in
  let e2' := constant_fold e2 in
  match e1', e2' with
  | Const n1, Const n2 => Const (n1 * n2)
  | Const 0, _ => Const 0
  | _, Const 0 => Const 0
  | Const 1, _ => e2'
  | _, Const 1 => e1'
  | _, _ => Times e1' e2'
  end
end.

(**
For example, we can simplify an expression like [x + (1 + 1)] to just [x + 2]. However, note that
our constant fold implementation isn't quite smart enough to simplify [(x + 1) + 1)] to [x + 2]
because it doesn't understand associativity.
*)
Example constant_fold_example:
    constant_fold (Plus (Var "x"%string) (Plus (Const 1) (Const 1))) = Plus (Var "x"%string) (Const 2).
Proof. auto. Qed.

(***************************************************************************************************
PROBLEM 9 [10 points]: Prove the following theorem showing that constant folding is effective, in
the sense that it does not make programs increase in [size].

HINTS: 
1. You probably need to do case analysis on the results of [constant_fold] on some subexpressions.
   The [destruct] tactic can do that for you.
2. There are a lot of cases to manage here. Don't worry about making your proof short or elegant
   (see the extra credit below the next problem for that).
*)
Theorem constant_fold_is_effective:
    forall e, size (constant_fold e) <= size e.
Proof.
    induction e.
    - simpl. auto.
    - simpl. auto.
    - simpl. destruct (constant_fold e1). simpl. destruct n. simpl. destruct (constant_fold e2). simpl. lia. simpl.
    lia. simpl. 
    replace (S (size e3 + size e4)) with (size (Plus e3 e4)). apply (Nat.le_le_succ_r). Search ( _ <= _ + _).  replace (size e1 + size e2) with (size e2+size e1). apply Arith_prebase.le_plus_trans_stt. apply IHe2. apply Nat.add_comm. simpl. auto.
    simpl. simpl. replace (S (size e3 + size e4)) with (size (Plus e3 e4)). apply (Nat.le_le_succ_r). Search ( _ <= _ + _).  replace (size e1 + size e2) with (size e2+size e1). apply Arith_prebase.le_plus_trans_stt. apply IHe2. apply Nat.add_comm. simpl. auto.
    simpl. destruct (constant_fold e2). simpl. lia. 
    replace (size (Plus (Const (S n)) (Var v)) ) with (S ( (size (Const (S n)))+ (size (Var v)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Plus (Const (S n)) (Plus e3 e4)) ) with (S ( (size (Const (S n)))+ (size (Plus e3 e4)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Plus (Const (S n)) (Times e3 e4)) ) with (S ( (size (Const (S n)))+ (size (Times e3 e4)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    destruct (constant_fold e2). destruct n. simpl. lia. 
    replace (size (Plus (Var v) (Const (S n)) )) with (S ( (size (Const (S n)))+ (size (Var v)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Plus (Var v) (Var v0) )) with (S ( (size (Var v0))+ (size (Var v)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Plus (Var v) (Plus e3 e4)) ) with (S ( (size (Var v))+ (size (Plus e3 e4)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Plus (Var v) (Times e3 e4)) ) with (S ( (size (Var v))+ (size (Times e3 e4)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    destruct (constant_fold e2). simpl. destruct n. 
    apply Nat.le_le_succ_r. lia.
    replace (size (Plus (Plus e3 e4) (Const (S n))) ) with (S ( (size (Plus e3 e4)) + (size (Const (S n))))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Plus (Plus e3 e4) (Var v)) ) with (S ( (size (Plus e3 e4)) + (size (Var v)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Plus (Plus e3 e4) (Plus e5 e6)) ) with (S ( (size (Plus e3 e4)) + (size (Plus e5 e6)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Plus (Plus e3 e4) (Times e5 e6)) ) with (S ( (size (Plus e3 e4)) + (size (Times e5 e6)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    destruct (constant_fold e2).
    destruct n. 
    apply Nat.le_le_succ_r. lia.
    replace (size (Plus (Times e3 e4) (Const (S n))) ) with (S ( (size (Times e3 e4)) + (size (Const (S n))))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Plus (Times e3 e4) (Var v)) ) with (S ( (size (Times e3 e4)) + (size (Var v)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Plus (Times e3 e4) (Plus e5 e6)) ) with (S ( (size (Times e3 e4)) + (size (Plus e5 e6)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Plus (Times e3 e4) (Times e5 e6)) ) with (S ( (size (Times e3 e4)) + (size (Times e5 e6)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    - simpl. destruct (constant_fold e1). simpl. destruct n. simpl. destruct (constant_fold e2). simpl. lia. simpl.
    lia. simpl. lia. simpl. lia.
    destruct n. 
    destruct (constant_fold e2).
    simpl. lia.
    apply Nat.le_le_succ_r. lia.
    apply Nat.le_le_succ_r. lia.
    apply Nat.le_le_succ_r. lia.
    destruct (constant_fold e2).
    simpl. lia.
    replace (size (Times (Const (S (S n))) (Var v)) ) with (S ( (size (Const (S (S n))))+ (size (Var v)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Times (Const (S (S n))) (Plus e3 e4)) ) with (S ( (size (Const (S (S n))))+ (size (Plus e3 e4)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Times (Const (S (S n))) (Times e3 e4)) ) with (S ( (size (Const (S (S n))))+ (size (Times e3 e4)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    destruct (constant_fold e2).
    destruct n.
    simpl. lia.
    destruct n.
    simpl. lia.
    replace (size (Times (Var v) (Const (S (S n))) )) with (S ((size (Var v))+ (size (Const (S (S n)))))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Times (Var v) (Var v0) )) with (S ((size (Var v))+ (size (Var v0)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Times (Var v) (Plus e3 e4) )) with (S ((size (Var v))+ (size (Plus e3 e4)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Times (Var v) (Times e3 e4) )) with (S ((size (Var v))+ (size (Times e3 e4)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    destruct (constant_fold e2).
    destruct n. 
    simpl. lia.
    destruct n.
    apply Nat.le_le_succ_r. lia.
    replace (size (Times (Plus e3 e4) (Const (S (S n))) )) with (S ((size (Plus e3 e4))+ (size (Const (S (S n)))))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Times (Plus e3 e4) (Var v) )) with (S ((size (Plus e3 e4))+ (size (Var v)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Times (Plus e3 e4) (Plus e5 e6) )) with (S ((size (Plus e3 e4))+ (size (Plus e5 e6)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Times (Plus e3 e4) (Times e5 e6) )) with (S ((size (Plus e3 e4))+ (size (Times e5 e6)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    destruct (constant_fold e2).
    destruct n.
    simpl. lia.
    destruct n. 
    apply Nat.le_le_succ_r. lia.
    replace (size (Times (Times e3 e4) (Const (S (S n))) )) with (S ((size (Times e3 e4))+ (size (Const (S (S n)))))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Times (Times e3 e4) (Var v) )) with (S ((size (Times e3 e4))+ (size (Var v)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Times (Times e3 e4) (Plus e5 e6) )) with (S ((size (Times e3 e4))+ (size (Plus e5 e6)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
    replace (size (Times (Times e3 e4) (Times e5 e6) )) with (S ((size (Times e3 e4))+ (size (Times e5 e6)))). Search ( S _ <= S _). apply le_n_S . lia. simpl. lia.
Qed.


(***************************************************************************************************
PROBLEM 10 [10 points]: Prove the following theorem showing that constant folding is correct, in the
sense that it preserves the semantics of [expr]s.

HINT: Again, there are a lot of cases to manage here. Don't worry about making your proof short just
yet. We'll tackle that below.
*)
Theorem constant_fold_preserves_semantics:
    forall e m, eval_expr e m = eval_expr (constant_fold e) m.
Proof.
    (* TODO *)
Admitted.

(***************************************************************************************************
PROBLEM 11 [EXTRA CREDIT, 6-12 points -- I suggest skipping this until you finish the rest of the
homework.]

Let's run a little competition to have some fun playing code golf on the above proof. Here's what to
do if you want to play:
* Do the proof of [constant_fold_preserves_semantics] again, but this time, write the shortest or
  most elegant proof you can.
* Rules: 
  * Do not import any additional Coq libraries beyond the ones at the top of this file.
  * Do not write any Ltac.
  * You're free to write additional helper lemmas if you think they would be useful, but the entire
    length of any additional sentences (Definitions, Lemmas, etc) will count towards your character
    count.
  * You can't use the [constant_fold_preserves_semantics] theorem you just proved above (so, for
    example, you can't just do [apply constant_fold_preserves_semantics]).
* We'll give 6 points for any proof we think is better than your original proof above. The two
  shortest proofs by number of characters, and the two proofs we think are the most elegant, will
  receive another 6 points, as well as a prize :-)
*)
Theorem constant_fold_preserves_semantics':
    forall e m, eval_expr e m = eval_expr (constant_fold e) m.
Proof.
    (* TODO *)
Admitted.

End Part1.

(* In this part we'll study a simplified version of [expr] but do more complicated stuff with it.
There's nothing preventing us from using our original [expr], it would just be more tedious. *)
Module Part2.

(**
This time our [expr] just has two cases -- we've removed [Var] and [Times] from the language.
*)
Inductive expr :=
| Const (n : nat)
| Plus (e1 e2 : expr).

Fixpoint eval_expr (e : expr) : nat :=
match e with
| Const n => n
| Plus e1 e2 => eval_expr e1 + eval_expr e2
end.

(**
We are going to study a second language with a very different style. Our language [instr] models a
simple register machine (like the computer architectures you're probably used to). The machine has
infinite registers whose names are just [nat]s.
*)

Notation reg := nat.
Definition reg_eq : forall r1 r2 : nat, {r1 = r2} + {r1 <> r2} := Nat.eq_dec.

(**
Here is the instruction syntax for our register machine.
- The ADD instruction adds the values from two source registers and stores the result in a
  destination register.
- The LDI instruction loads an immediate value (a [nat]) and stores it in a destination register.
- The MOV instruction copies a value from a source register to a destination register.
*)

Inductive instr :=
| ADD (src1 src2 dest: reg)
| LDI (n: nat) (dest: reg)
| MOV (src dest: reg)
.

(**
And *programs* in our register machine are just lists of instructions.
*)

Definition prog := list instr.

(**
Similar to what we did in Part 1 with variables, we model the state of the machine as a function
that maps each register to its current value.
*)

Definition state := reg -> nat.

Definition set_register (st: state) (r: reg) (v: nat) : state :=
    fun (r': reg) => if reg_eq r r' then v else st r'.

(**
Our machine will start in a state where all registers have the value 0.
*)

Definition initial_state : state := fun _ => 0.


(***************************************************************************************************
PROBLEM 12 [6 points]: Fill in the denotational semantics for [instr] as a function [eval_instr].
See the comment on [instr] to understand the intended semantics. The finished semantics should make
the below examples pass when you replace Admitted with Qed.
*)
Definition eval_instr (i: instr) (st: state) : state := 
    match i with
    | (ADD x y z) => (set_register st z ((st x)+(st y)) )
    | (LDI n z) => (set_register st z n)
    | (MOV s d) => (set_register st d (st s))
    end.

Definition example_state := set_register (set_register initial_state 1 5) 2 7.

Example eval_instr_add: 
    let final_state := eval_instr (ADD 1 2 0) example_state in
    final_state 1 = 5 /\ final_state 2 = 7 /\ final_state 0 = 12.
Proof. auto. Qed.

Example eval_instr_ldi:
    let final_state := eval_instr (LDI 17 0) example_state in
    final_state 1 = 5 /\ final_state 2 = 7 /\ final_state 0 = 17.
Proof. auto. Qed.

Example eval_instr_mov:
    let final_state := eval_instr (MOV 1 0) example_state in
    final_state 1 = 5 /\ final_state 2 = 7 /\ final_state 0 = 5.
Proof. auto. Qed.

(***************************************************************************************************
PROBLEM 13 [4 points]: Fill in the denotational semantics for [prog] as an auxiliary function
[eval_prog'] that executes a program on a given input state and returns the final state. The
finished semantics should make the below examples pass when you replace Admitted with Qed.
*)
Fixpoint eval_prog' (p : list instr) (st: state) : state := 
    match p with
    | [] => st
    | (cons instr_ rest) => eval_prog' rest (eval_instr instr_ st)
    end (* TODO provide a real definition *).

Example eval_prog'_ldi_add:
    let final_state := eval_prog' [LDI 17 1; ADD 1 2 0] example_state in
    final_state 1 = 17 /\ final_state 2 = 7 /\ final_state 0 = 24.
Proof. auto. Qed.

Example eval_prog'_add_ldi:
    let final_state := eval_prog' [ADD 1 2 0; LDI 13 1] example_state in
    final_state 1 = 13 /\ final_state 2 = 7 /\ final_state 0 = 12.
Proof. auto. Qed.

Example eval_prog'_add_mov:
    let final_state := eval_prog' [ADD 1 2 0; MOV 0 1] example_state in
    final_state 1 = 12 /\ final_state 2 = 7 /\ final_state 0 = 12.
Proof. auto. Qed.

(**
We define the semantics of an entire [prog] as just running the program and returning the value in
register 0. In other words, we define register 0 to hold the "return value" of a [prog].
*)

Definition eval_prog (p: list instr) : nat := (eval_prog' p initial_state) 0.

(**
Now let's build a *compiler* from [expr]s to [prog]s and prove it correct. Our compiler will take as
input an [expr] and return a [prog] that, when evaluated, returns the same value.
*)

(***************************************************************************************************
PROBLEM 14 [8 points]: Fill in the function [compile'], which takes as input an [expr] and a
destination register [dest_reg], and returns a [prog] that implements the [expr] on the register
machine.

The returned program should make two guarantees about its final state:
1. The [dest_reg] register holds the same value as [eval_expr e] would compute.
2. In the final state, no registers [n] with [n < dest_reg] have been modified from the initial
   state.

These guarantees mean the progam is free to modify registers *higher* than the destination register,
but must leave registers *lower* than the destination register unchanged, and must store its
computed result in the destination register.

The finished implementation of [compile'] should make the below examples pass when you replace
Admitted with Qed.
*)
Fixpoint compile' (e: expr) (dest_reg: reg) : prog := 
    match e with
    | (Const n) => [LDI n (dest_reg)]
    | (Plus e1 e2) =>  (compile' e1 (dest_reg)) ++ (compile' e2 (dest_reg+1)) ++ [ADD (dest_reg) (dest_reg+1) (dest_reg)]
    (* ; MOV (dest_reg+2) (dest_reg) ] *)
    (* TODO provide a real definition *)
    end.

(**
To compile an [expr], we just use [compile'] with a destination register of 0, which is where our
semantics says return values should be stored.
*)
Definition compile (e: expr) := compile' e 0.

Example compile_const:
    eval_prog (compile (Const 10)) = 10.
Proof. auto. Qed.

Example compile_plus:
    eval_prog (compile (Plus (Const 7) (Const 9))) = 16.
Proof. auto. Qed.

Example compile_nested_plus:
    eval_prog (compile (Plus (Plus (Const 7) (Const 8)) (Plus (Const 9) (Const 11)))) = 35.
Proof. auto. Qed.

Example compile'_plus_0_is_unmodified:
    let example_state := set_register initial_state 0 12 in
    let final_state := eval_prog' (compile' (Plus (Const 7) (Const 8)) 1) example_state in
    (* reg 0 is unmodified since we called [compile'] with dest_reg = 1 *)
    final_state 0 = 12 /\ final_state 1 = 15.
Proof. auto. Qed.

(***************************************************************************************************
PROBLEM 15 [6 points]: Prove the following helpful lemma about how we can compose the evaluation of
two [prog]s.
*)
Lemma eval_prog_append:
    forall (p1 p2: prog) (st: state) (r: reg),
        eval_prog' (p1 ++ p2) st r = eval_prog' p2 (eval_prog' p1 st) r.
Proof.
    induction p1.
    - simpl. lia.
    - intros. simpl. apply IHp1 with (st := eval_instr a st).
Qed.

(**
Compilers are tricky to get right. But denotational semantics gives us the tools we need to *prove*
our compiler does the right thing! Let's give that a shot.

The idea is that we will state and prove a correctness theorem: that for any expression [e],
executing the compiled program [compile e] returns the same value as evaluating the expression
directly.
*)

(***************************************************************************************************
PROBLEM 16 [4 points]: Attempt to complete the following correctness proof about our compiler. Do
not remove the initial [induction e] tactic, and do not write any helper lemmas (yet!).

You won't be able to complete this proof, but get as far as you can before you get stuck.

HINTS:
1. You should be able to complete the base case.
2. The [unfold] tactic can help expand the definitions of [eval_prog] and [compile].
3. If you do somehow manage to complete this proof, either you've outsmarted me or you have a bug in
   your semantics somewhere :-)

Do not modify the [Abort] at the end of this proof. We'll attempt it again in a moment.
*)
Theorem compile_correct:
    forall e, eval_prog (compile e) = eval_expr e.
Proof.
    induction e. (* keep this line as the first tactic. *)
    (* TODO *)
    - simpl. auto.
    - simpl. unfold eval_prog. simpl.
Abort.

(***************************************************************************************************
PROBLEM 17 [4 points]: Although the [compile_correct] theorem is in fact true, the proof approach
above was doomed to fail. In a sentence or two, explain *why* the proof is impossible unless we do
something different.

ANSWER: This is because to prove the correctness of the compiler we will need a stronger statement to hold true. Specifically, we will need to prove that we are not modifying any registers below the destination register which ultimately preserves computation stack.



*)

(**
Now let's try to make our [compile_correct] proof go through. First, let's prove a helper lemma that
might be helpful in completing the correctness proof.
*)

(***************************************************************************************************
PROBLEM 18 [10 points]: Prove the following lemma showing that the program [compile' e dest_reg]
does not modify any register [r] with [r < dest_reg]. (Recall that this was a guarantee we placed on
[compile'] when we defined it -- if this isn't true for your implementation of [compile'], you need
to go back and fix it before doing this proof.)

HINTS:
1. You might find the earlier [eval_prog_append] lemma useful.
2. Be careful with how you use [intro] and/or [induction] at the start of the proof, so that you get
   an inductive hypothesis strong enough to make the proof work.
*)
Lemma compile'_registers_untouched:
    forall (e: expr) (dest_reg: reg) (st: state) (r: reg),
        r < dest_reg ->
        (eval_prog' (compile' e dest_reg) st) r = st r.
Proof.
    (* TODO *)
    induction e.
    - simpl. intros. unfold set_register. destruct reg_eq. simpl. lia. lia.
    - simpl.  intros.
    replace (eval_prog'
    (compile' e1 dest_reg ++
     compile' e2 (dest_reg + 1) ++
     [ADD dest_reg (dest_reg + 1) dest_reg]) st) with 
     (eval_prog' 
     ([ADD dest_reg (dest_reg + 1) dest_reg]) 
     (eval_prog' (compile' e2 (dest_reg + 1)) (eval_prog'
     (compile' e1 dest_reg) st))). simpl. unfold set_register. destruct reg_eq. lia. replace  (eval_prog' (compile' e1 dest_reg) st) with st. apply IHe2. lia.
    (* apply eval_prog_append with (p1:= (compile' e1 dest_reg)) (p2:= (compile' e2 (dest_reg + 1) ++
    [ADD dest_reg (dest_reg + 1) dest_reg])).  *)
    (* replace (eval_prog' (compile' e1 dest_reg ++
    compile' e2 (dest_reg + 1) ++
    [ADD dest_reg (dest_reg + 1) (dest_reg + 2);
     MOV (dest_reg + 2) dest_reg]) st) with 
     (eval_prog' [ADD dest_reg (dest_reg + 1) (dest_reg + 2);
     MOV (dest_reg + 2) dest_reg] (eval_prog' (compile' e2 (dest_reg + 1)) (eval_prog' (compile' e1 dest_reg) st))). *)
Abort.

(***************************************************************************************************
PROBLEM 19 [10 points]: Define and prove a helper lemma [compile_correct'], and then use it to prove
the below theorem [compile_correct].

HINTS:
1. Your proof should probably use [compile'_registers_untouched]. Think about how this fact would be
   useful to prove the compiler correct before you start video gaming the Coq proof out.
2. The proof of [compile_correct] should not use induction, but [compile_correct'] should.
*)
Lemma compile_correct':
    forall (e: expr) (st: state), 
    (eval_prog' (compile' e 0) st) 0 = (eval_expr e).
Proof.
    (* TODO *)
Admitted.

Theorem compile_correct:
    forall e, eval_prog (compile e) = eval_expr e.
Proof.
    intros.
    apply compile_correct' with (st:=initial_state) (e:=e).
Qed.

End Part2.

(** Now continue to Part 3 in Homework.rkt! *)