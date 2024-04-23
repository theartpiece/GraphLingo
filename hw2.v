(** * CS 345H: Homework 2 *)

(**
In this homework, we'll study IMP and operations semantics, and in particular we'll focus on
termination of IMP programs. There are a total of 138 points available in this file.
*)

(***************************************************************************************************
A quick reminder about the rules for Coq homework in this class:
- You cannot use any Coq libraries beyond the ones already imported for you.
- You can use any tactic available in these libraries, including ones we haven't seen in lecture.
- You must not edit any theorems or definitions that are already provided, unless a problem
  explicitly asks you to. This rule holds even if the edit seems "trivial", like changing "1 + x" to
  "x + 1" or reordering [forall] quantifiers.
- You can add new theorems and definitions if you want to.
*)

(***************************************************************************************************
SOME ADVICE ABOUT THE HOMEWORK:

I have a few suggestions from myself and from the TAs who beta tested this homework about things we
found challenging or annoying. Some of these are also inlined into HINTs, but here's a summary:

- Tips about [destruct]:
  - [destruct] is all about case analysis, but the cases don't have to be something already defined
    in your context. For example, you can do [destruct (Nat.eq_dec a b)] to do case analysis on
    whether [a] and [b] are equal. As another example, if [f] is a function [nat -> option nat], and
    you have a nat [n] in your context, you can do [destruct (f n)] to do case analysis on whether
    [f n] is [None] or [Some x].
  - You can [destruct] a tuple/pair to get access to its individual elements. If you have a goal
    with a term like [let (y0, n0) = p in ...], then [destruct p] will also help simplify that let
    binding away even if [simpl] isn't working for you.
  - Soemtimes you get a seemingly obvious goal except for a silly equality; for example, a goal like
    [if (Nat.eq_dec a a) then ... else ...]. It looks silly (obviously a = a), but [destruct
    (Nat.eq_dec a a)] can help here. It will generate a second goal with an obvious contradition [a
    <> a] in the hypotheses, but that should be easy to handle with [contradiction].
  - By default [destruct] doesn't explicitly remember the thing you destructed on. You can use
    [destruct X eqn:?] to remember an additional equality hypothesis about the [X] you destructed.
    This is especially helpful when doing something like [destruct (f x) eqn:Heq], because the new
    hypothesis [Heq] will be something like [f x = None], telling you which case you're in.
- Other useful tactics:
  - The [firstorder] tactic is often useful for dispatching boring logic manipulations -- things
    you'd get by just rewriting a few times using hypotheses.
  - When doing inversion, a common pattern is [inversion H; subst; clear H] to keep your context
    clean. But occasionally this isn't always the right thing to do -- sometimes you're going to
    need [H] again later on, and so you might need to leave out the [clear].
  - In induction proofs, [revert] is a useful tactic to rearrange quantifiers to get the inductive
    hypothesis you want. After [intros], you can use [revert] to selectively put some of the forall
    quantifiers back into the goal. See the hint to Problem 19.
- Existential tactics: in several places on this homework (if you want to use them), proofs will be
  easier if you use e-tactics like [eexists]. These are super convenient, but they can also be very
  dangerous, in three ways you should be on the lookout for:
  1. Nothing is stopping you from [eapply]ing the wrong lemma over and over again, creating
     placeholders you'll never be able to fill in because they were the wrong lemmas. So you need to
     think ahead about whether you'll really be able to fill in the placeholders you're creating.
  2. In some proofs you're going to want to combine these tactics with case analysis. When you use a
     tactic like [eexists] you're promising to fill in a _single_ value for the placeholder
     variables. But if you do case analysis later, you might find that you want to fill in a
     *different* value for each of the cases, which you can't do. So *when* in the proof you use
     [eexists] is significant -- you usually want to do your case analysis first, and only then use
     e-tactics to create different placeholders in each case.
  3. Similar to (2), the e-tactics are pedantic about scoping. You're only allowed to fill in
     placeholders with values that existed at the time the placeholder was created. This usually
     manifests as Coq complaining about something not being in scope when you try to fill in a
     placeholder. When you see this, you should try to rearrange your proof to do the e-tactic as
     late as possible.
- Suggestions about proof strategy:
  - Many of the proofs here build on earlier lemmas. I've tried to call these out in hints where
    they happen, but always keep your eyes open for ways you might be able to use earlier lemmas to
    prove later ones. As a corollary, if you can't finish a proof, leave it [Admitted] and move on
    to the next one --- you can still use the un-proven lemma in your later proofs.
  - When doing induction proofs, remember that usually you want to find a way to apply the inductive
    hypothesis at some point. This can be a way to guide your exploration -- rather than trying to
    get straight to the goal, try to get to applying the IH first, then see where that gets you.

Here's a change since HW1: for proof problems, I've included a note about how many tactics my
solutions used. These are just to give you a very rough idea of how "hard" a proof is. If your proof
is shorter or longer than these, that's fine. But if you get 50 tactics into a proof that took me 5
tactics, it might be a good point to take a step back and rethink your approach.

Finally, here is a complete list of every tactic I used in my proofs on this homework. This isn't to
say that you must use all of them, or that you aren't allowed to use tactics not on this list
(although you must not [Require] any other libraries). It's again just to give you some guidance on
how hard the proofs are, and ideas on where to look for tactics:

- apply
- assert
- assumption
- auto
- clear
- constructor
- contradiction
- destruct
- discriminate
- eapply
- eassumption
- eauto
- econstructor
- eexists
- exists
- firstorder
- induction
- intro
- intros
- inversion
- reflexivity
- repeat
- revert
- rewrite
- simpl
- specialize
- split
- subst
- unfold

Good luck and have fun!
*)

Require Import Arith Lia List String.
Import ListNotations.
Open Scope string_scope.

(*
Let's start by copying and pasting the definitions of [var] from HW1: a [var] is just a string, and
equality on [var]s is decidable. We can work with that equality using [destruct (var_eq a b)], just
like we learned on HW1.
*)
Notation var := string.
Definition var_eq : forall v1 v2 : var, {v1 = v2} + {v1 <> v2} := string_dec.

(*
This time, we're going to model states as _association lists_, as we did in lecture, rather than the
function representation we used in HW1. So a state, which we'll be calling a _valuation_, is a list
of pairs of (variable name, value).
*)
Definition valuation := list (var * nat).
Definition set_var (v: valuation) (x: var) (n: nat) : valuation :=
    cons (x, n) v.

(*
To look up the value of a variable, we walk down the list until we find the first matching variable
name. Unlike in lecture, our [lookup] won't be returning an [option] type, and we will just declare
that undefined variables have value 0, as we did in HW1.
*)
Fixpoint lookup (v: valuation) (x: var) : nat :=
  match v with
  | nil => 0
  | cons (y, n) v' => if var_eq x y then n else lookup v' x
  end.

(*
Now let's copy and paste some more stuff from lecture and Homework 1 -- the syntax and denotational
semantics for arithmetic [expr]s, including variables.
*)

Inductive expr :=
| Const (n: nat)
| Var (x: var)
| Plus (e1 e2: expr)
| Times (e1 e2: expr).

Fixpoint eval_expr (e: expr) (v: valuation): nat :=
  match e with
  | Const n => n
  | Var x => lookup v x
  | Plus  e1 e2 => eval_expr e1 v + eval_expr e2 v
  | Times e1 e2 => eval_expr e1 v * eval_expr e2 v
  end.

(***************************************************************************************************
PROBLEM 1 [4 points, ~5 tactics]: prove the following lemma about looking up a variable you just
set.

HINTS: My proof used [destruct] to deal with a seemingly trivial comparison. Also, the combination
       of [destruct] and [simpl] can be sensitive to ordering, so if you're using both tactics and
       not getting the results you want, try doing them in the opposite order.
*)
Example lookup_most_recent:
    forall v x n,
        lookup (set_var v x n) x = n.
Proof.
    (* TODO *)
    induction v.
    - simpl. intros. destruct (var_eq x x).
        simpl. auto. easy.
    - simpl. intros. destruct var_eq.
        auto. auto. easy.
    (* - destruct lookup.  set_var. simpl.  *)
Qed.

(***************************************************************************************************
PROBLEM 2 [4 points, ~13 tactics]: prove the following lemma about looking up a variable you
_didn't_ just set.

HINTS: Again, [destruct] is useful here. As we saw in HW1, [destruct]ing an equality you've
      _already_ destructed once before can be useful to provoke Coq to simplify the goal. [destruct]
      can also be helpful on a tuple like [p: var * nat] -- if you end up with a term in your goal
      that looks like [let (y0, n0) = p in ...], [destruct]ing [p] should help you simplify it.
*)
Lemma lookup_unchanged:
    forall v x m n y,
        lookup v x = n ->
        x <> y ->
        lookup (set_var v y m) x = n.
Proof.
    (* TODO *)
    intros. simpl. destruct (var_eq x y) eqn:H1. easy. easy.
Qed.

(*
When we talked about operational semantics in lecture, we introduced the idea of an _inductively
defined proposition_ as a way to declare relations between states. We never used this idea on [expr]
expressions directly, because our denotational semantics was convenient, but it can be done. We can
declare an inductively defined proposition that relates [(expr, valuation)] pairs to the [nat] value
they evaluate to.

This relation can be written (e, v) ⇓ n, and is sometimes read "(e, v) reduces to n" or "e reduces
to n under valuation v". If (e, v) reduces to n, that means that expression [e] evaluated on
valuation [v] produces value [n].

This relation is a _big-step operational semantics_ for expressions. It's called _big-step_ because,
unlike small-step semantics, the relation directly gives us a final value for the program, rather
than taking us on a journey through lots of little steps to eventually get there.
*)

(***************************************************************************************************
PROBLEM 3 [8 points]: complete this definition of a big-step operational semantics for [expr]. It
should have the same semantics as the denotational [eval_expr], and we will prove that equivalence
in the next few problems.

If the proposition [expr_Step e v n] is true, then (e, v) ⇓ n -- in other words, evaluating [e]
under valuation [v] returns value [n].

I've already provided the names of the constructors, and the quantifiers you need for each one, so
don't change those. You need to replace the rest of each constructor (the part after TODO) --- I've
filled in bogus values past the TODOs just to make sure this file compiles.

Your definition must not use [eval_expr]. It must also use all the quantified variables provided,
and not introduce any additional quantified variables.

HINT: if you get stuck on the next few problems, one cause might be that your definitions here are
      wrong, so keep that in mind as you work forward.
*)
Inductive expr_Step: expr -> valuation -> nat -> Prop :=
| expr_Step_const : forall (n: nat) (v: valuation), 
(expr_Step (Const n) v n)
| expr_Step_var : forall (x: var) (v: valuation), 
(expr_Step (Var x) v (lookup v x)) 
| expr_Step_plus : forall (e1 e2: expr) (n1 n2: nat) (v: valuation), 
((expr_Step e1 v n1) /\ (expr_Step e2 v n2)) -> (expr_Step (Plus e1 e2) v (n1+n2)) 
| expr_Step_times : forall (e1 e2: expr) (n1 n2: nat) (v: valuation), 
((expr_Step e1 v n1) /\ (expr_Step e2 v n2)) -> (expr_Step (Times e1 e2) v (n1*n2))
.

(***************************************************************************************************
PROBLEM 4 [2 points, ~7 tactics]: prove that the expression [x + (2 * 4)] evaluates to 11 under the
valuation [("x", 3)], as a way of testing that your [expr_Step] definition is correct.

HINT: You can use the [replace] tactic to rewrite parts of your goal without already having a
      hypothesis to [rewrite] with. [replace a with b] replaces all occurrences of [a] with [b] in
      your goal, and generates a new subgoal to prove that [a = b]. This is the same thing as doing
      [assert (a = b) as H] and then [rewrite H] with that new hypothesis. You might find this
      useful to do some arithmetic in this proof.

      If the new [replace] subgoal can be proved by a single tactic [foo], you can also write
      [replace a with b by foo] to discharge it immediately.
*)
Example expr_Step_example:
    expr_Step (Plus (Var "x") (Times (Const 2) (Const 4))) [("x", 3)] 11.
Proof.
    replace 11 with (3+8).
    apply expr_Step_plus.
    split. apply expr_Step_var.
    replace 8 with (2*4).
    apply expr_Step_times.
    split.
    apply expr_Step_const.
    apply expr_Step_const.
    lia. lia.
Qed.

(*
Now let's prove [eval_expr] and your new [eval_Step] semantics equivalent to each other. We'll do
each direction as a separate lemma and then combine them.

HINTS: Both directions will use induction, but my two proofs inducted on different things. (There
are other ways to make these proofs work, so if you ended up inducting differently that's fine, but
this is my suggestion of how to do it).
*)

(***************************************************************************************************
PROBLEM 5 [4 points, ~4 tactics]: prove the following lemma that [expr_Step] is _sound_ with respect
to [eval_expr]; in other words, any behavior that [expr_Step] allows is also allowed by [eval_expr].
*)
Lemma expr_step_implies_eval:
    forall e v n, expr_Step e v n -> eval_expr e v = n.
Proof.
    (* TODO *)
    induction e.
    - simpl. intros . inversion H. auto.
    - simpl. simpl. intros. inversion H. auto.
    - simpl. intros. inversion H. firstorder.
    - simpl. intros. inversion H. firstorder.  
Qed.

(***************************************************************************************************
PROBLEM 6 [4 points, ~6 tactics]: prove the following lemma that [expr_Step] is _complete_ with
respect to [eval_expr]; in other words, any behavior that [eval_expr] allows is also allowed by
[expr_Step].
*)
Lemma expr_eval_implies_step:
    forall e v n, eval_expr e v = n -> expr_Step e v n.
Proof.
    induction e.
    - simpl. intros. replace n0 with n by H. apply expr_Step_const.
    - simpl. intros. rewrite <- H. apply expr_Step_var.
    - simpl. intros. rewrite <- H. apply expr_Step_plus. firstorder.
    - simpl. intros. rewrite <- H. apply expr_Step_times. firstorder.
    (* TODO *)
Qed.

(***************************************************************************************************
PROBLEM 7 [4 points, ~4 tactics]: prove the following theorem that [expr_Step] and [eval_expr] are
equivalent.

HINTS: You've already done all the work for this one. Use [split] to divide <-> into two goals.
*)
Theorem expr_step_eval_expr:
    forall e v n, eval_expr e v = n <-> expr_Step e v n.
Proof.
    (* TODO *)
    split. apply expr_eval_implies_step. apply expr_step_implies_eval.
Qed.

(***************************************************************************************************
PROBLEM 8 [2 points, 2 tactics]: prove the following example again, but this time, use no more
than two tactics. Do not use the previously defined [expr_Step_example] lemma. If your previous
proof was already two or fewer tactics, you can just use that proof again.

HINT: Use an earlier lemma. The idea here is to show you why a denotational semantics can be easier
      to work with than a big-step operational one, and how to convert between them.
*)
Example expr_Step_example':
    expr_Step (Plus (Var "x") (Times (Const 2) (Const 4))) [("x", 3)] 11.
Proof.
    (* TODO *)
    apply expr_step_eval_expr. easy.
Qed.


(*
Let's expand our discussion to the full IMP language we saw in lecture. We'll start by just copying
and pasting the syntax and small-step semantics of IMP and the step-star relation for it.

Notice, though, that I'm switching up the capitalization a bit compared to lecture -- my intent is
to write [step] for things that are small-step, and [Step] for things that are big-step (because
"the S is bigger" :-)).
*)

Inductive cmd :=
| Skip
| Assign (x: var) (e: expr)
| Seq (c1 c2: cmd)
| If (e: expr) (then_ else_: cmd)
| While (e: expr) (body: cmd).

Inductive step : valuation * cmd -> valuation * cmd -> Prop :=
| stepAssign     : forall v x e,
                     step (v, Assign x e) (set_var v x (eval_expr e v), Skip)
| stepSeqLeft    : forall v c1 c2 v' c1', 
                     step (v, c1) (v', c1') ->
                     step (v, Seq c1 c2) (v', Seq c1' c2)
| stepSeqRight   : forall v c2,
                     step (v, Seq Skip c2) (v, c2)
| stepIfTrue     : forall v e then_ else_,
                     eval_expr e v <> 0 ->
                     step (v, If e then_ else_) (v, then_)
| stepIfFalse    : forall v e then_ else_,
                     eval_expr e v = 0 ->
                     step (v, If e then_ else_) (v, else_)
| stepWhileTrue  : forall v e body,
                     eval_expr e v <> 0 ->
                     step (v, While e body) (v, Seq body (While e body))
| stepWhileFalse : forall v e body,
                     eval_expr e v = 0 ->
                     step (v, While e body) (v, Skip).

Inductive stepStar : valuation * cmd -> valuation * cmd -> Prop :=
| stepStarRefl : forall v c, stepStar (v, c) (v, c)
| stepStarOnce : forall v1 c1 v2 c2 v3 c3,
                   step (v1, c1) (v2, c2) ->
                   stepStar (v2, c2) (v3, c3) ->
                   stepStar (v1, c1) (v3, c3).

(*
Here is a very simple program that we're going to do proofs about in two different ways.
*)
Definition set_x_to_1_prog: cmd :=
    Assign "x" (Const 1).

(***************************************************************************************************
PROBLEM 9 [4 points, ~3 tactics]: prove the following example that [set_x_to_1_prog] terminates in a
particular state.

HINT: this is a good place to try out the e-tactics -- [econstructor], [eauto], etc -- which will be
      useful for quite a few of the proofs in this homework.
*)
Example set_x_to_1_prog_step_star:
    forall v1, 
        stepStar (v1, set_x_to_1_prog) (set_var v1 "x" 1, Skip).
Proof.
    (* TODO *)
    (* apply set_x_to_1_prog. *)
    (* firstorder. *)
    unfold set_x_to_1_prog. econstructor. apply stepAssign. unfold eval_expr. apply stepStarRefl.
Qed.

(***************************************************************************************************
PROBLEM 10 [6 points, ~13 tactics]: prove the following example that says a similar thing to
[set_x_to_1_prog_step_star] but does so in a way that is more tedious to prove (because it doesn't
implicitly assume that [set_x_to_1_prog] is terminating and deterministic).

HINT: you'll want to use [inversion], quite a few times.
*)
Example set_x_to_1_prog_step_star':
    forall v1 v2, 
        stepStar (v1, set_x_to_1_prog) (v2, Skip) ->
        lookup v2 "x" = 1.
Proof.
    (* TODO *)
    unfold set_x_to_1_prog. intros. firstorder. inversion H; subst; clear H.
    inversion H3; subst; clear H3. inversion H5; subst; clear H5. easy. easy. 
Qed.

(*
Now that we have a little experience with these definitions, let's get to the meat of the topic for
this homework: _termination_.

Recall that we said that if a program ever steps to [Skip], it has terminated, and cannot take any
more steps. Let's prove this.
*)

(***************************************************************************************************
PROBLEM 11 [4 points, ~4 tactics]: prove the following inversion-esque lemma that Skip cannot step.
*)
Lemma skip_cannot_step:
    forall v c v' c', step (v, c) (v', c') -> c <> Skip.
Proof.
    intros. inversion H; subst. 
    discriminate. discriminate. discriminate. discriminate. discriminate. discriminate. discriminate.
Qed.

(*
So we know that Skip can't step. But how do we know that Skip is the _only_ program that can't step?
In other words, is it possible for a program to terminate (have no more possible steps to take)
before reaching Skip? Let's find out.
*)

(***************************************************************************************************
PROBLEM 12 [8 points, ~39 tactics]: prove the following lemma about how Seq commands can always
step.

HINTS:
(1) I did this by induction, but be careful what you induct over and what you [intros] on.
(2) Sometimes you have a hypothesis like [H: forall x, exists x', P(x, x')], and you want to get at
    the value of x' for a specific x. One way to do that is to use the [specialize] tactic on the
    hypothesis, like [specialize H with (x := 5)], which will strip off the forall quantifier and
    leave an existential you can destruct to get x'.
(3) To case split on whether a number [n] is 0, [destruct (Nat.eq_dec n 0)].
(4) If you're using tactics like [eexists], you need to be careful _when_ you use them. These
    tactics promise to fill in a _single_ value for the placeholder variables. But if you do
    something like [eexists] and then later do case analysis in your proof, you might find that you
    want to fill in a *different* value for each of the cases. You can't do that unless you do the
    case analysis *before* creating the placeholder variables.
*)
Lemma seq_can_always_step:
    forall v c1 c2, exists v' c', step (v, Seq c1 c2) (v', c').
Proof.
    (* TODO *)
    induction c1.
    - intros. eexists. eexists. apply stepSeqRight.
    - intros. eexists. eexists. apply stepSeqLeft. apply stepAssign.
    - specialize IHc1_1 with (c2 := c1_2). firstorder. econstructor. econstructor. econstructor. eauto.
    - specialize IHc1_1 with (c2 := c1_2). firstorder. edestruct (Nat.eq_dec (eval_expr e v) 0). econstructor. econstructor. econstructor. apply stepIfFalse. auto. econstructor. econstructor. econstructor. apply stepIfTrue. auto.
    - firstorder. edestruct (Nat.eq_dec (eval_expr e v) 0). econstructor. econstructor. econstructor. apply stepWhileFalse. auto. econstructor. econstructor. econstructor. apply stepWhileTrue. auto.
Qed.

(***************************************************************************************************
PROBLEM 13 [8 points, ~25 tactics]: prove the following theorem that all non-Skip commands can step.

HINT: I didn't need induction here (though it can probably work), but did use the previous lemma.
*)
Lemma non_skip_can_always_step:
    forall v c, c <> Skip -> exists v' c', step (v, c) (v', c').
Proof.
    intros.
    destruct c. contradiction. 
    eexists. eexists. apply stepAssign.
    apply seq_can_always_step.
    edestruct (eval_expr e v) eqn:H1. eexists. eexists. eapply stepIfFalse. easy. eexists. eexists. eapply stepIfTrue. lia.
    edestruct (eval_expr e v) eqn:H1. eexists. eexists. eapply stepWhileFalse. easy. eexists. eexists. eapply stepWhileTrue. lia.
Qed.

(*
Let's prove a couple of small lemmas about Skip that will be useful in upcoming proofs.
*)

Definition is_skip (c: cmd) : bool :=
    match c with
    | Skip => true
    | _ => false
    end.

(***************************************************************************************************
PROBLEM 14 [4 points, ~4 tactics]: prove the following lemma about is_skip's true case.
*)
Lemma is_skip_true:
    forall c, is_skip c = true -> c = Skip.
Proof.
    intro c.
    destruct c.
    intros. auto. unfold is_skip. easy.
    unfold is_skip. easy. 
    unfold is_skip. easy. 
    unfold is_skip. easy. 

    
    (* TODO *)
Qed.

(***************************************************************************************************
PROBLEM 15 [4 points, ~4 tactics]: prove the following lemma about is_skip's false case.
*)
Lemma is_skip_false:
    forall c, is_skip c = false -> c <> Skip.
Proof.
    intro c.
    destruct c.
    unfold is_skip. easy.
    unfold is_skip. easy.
    unfold is_skip. easy.
    unfold is_skip. easy.
    unfold is_skip. easy.
Qed.

(*
One of the motivations for studying operational semantics was to deal with programs that might not
terminate. In lecture, we saw that we couldn't define a denoational semantics for IMP because Coq
required the [Fixpoint] definition we wrote to terminate, and that might not happen.

The rest of the homework looks at a different approach to implementing an interpreter for IMP that
will work around the termination issue, but at a price.

The first thing we're going to do is write an interpreter for a _single step_ of an IMP program.
*)

(***************************************************************************************************
PROBLEM 16 [8 points]: complete the definition of [eval_cmd_once], which takes as input a pair of
(valuation, cmd), and returns a pair (valuation, cmd) that results after taking _exactly one step_
from the first pair. In other words, [eval_cmd_once] is a kind of interpreter for the [step]
relation, also known as the small-step operational semantics for IMP.

[eval_cmd_once] returns [option] because not every input state can step. In fact, we proved above
that every input state _except_ [c = Skip] can step, so that's the only case where this should
return None.

Your definition should make the next few test cases pass when replacing Admitted with Qed.

HINTS:
(1) I know of at least two different ways to define this that will work. One uses [is_skip], one
    does not. Both are valid, and will just lead to slightly different proofs in the later problems.
(2) You might find yourself wanting to "break apart" an [option (valuation * cmd)] to get to the
    valuation and cmd inside. In a proof, you'd use [destruct] to do that, but this is a function
    definition. The way to do it here is with a [match] expression.
*)
(* Fixpoint eval_cmd_once (v: valuation) (c: cmd) : option (valuation * cmd) :=
    match c with
    | Skip => None
    | Assign x e => Some (set_var v x (eval_expr e v), Skip)
    | Seq c1 c2 => 
        match c1 with 
        | Skip => Some (v, c2)
        | Assign x e => Some ((set_var v x (eval_expr e v)), (Seq Skip c2))
        | Seq c1_1 c1_2 => Some (v, (Seq c1_1 (Seq c1_2 c)))
        | If e cthen celse => Some (v, If e (Seq cthen c2) (Seq celse c2) )
        | While e cx => Some (v, If e (Seq cx (Seq (While e cx) c2)) c2)
        end
    | If e cthen celse => if Nat.eq_dec (eval_expr e v) 0 then Some (v, celse) else Some (v, cthen)
    | While e c1 => if Nat.eq_dec (eval_expr e v) 0 then Some (v, Skip) else Some (v, Seq c1 (While e c1)) 
    end. *)

Fixpoint eval_cmd_once (v: valuation) (c: cmd) : option (valuation * cmd) :=
match c with
| Skip => None
| Assign x e => Some (set_var v x (eval_expr e v), Skip)
| Seq c1 c2 => 
    match (eval_cmd_once v c1) with 
    | None => Some (v, c2)
    | Some (v', c') => Some (v', Seq Skip c2)
    end
| If e cthen celse => if Nat.eq_dec (eval_expr e v) 0 then Some (v, celse) else Some (v, cthen)
| While e c1 => if Nat.eq_dec (eval_expr e v) 0 then Some (v, Skip) else Some (v, Seq c1 (While e c1)) 
end.

Definition iv : valuation := [("x", 4); ("y", 0)].

Example eval_cmd_once_skip:
    eval_cmd_once iv Skip = None.
Proof. auto. Qed.

Example eval_cmd_once_assign:
    eval_cmd_once iv (Assign "x" (Plus (Var "x") (Const 1))) = Some ((set_var iv "x" 5), Skip).
Proof. auto. Qed.

Example eval_cmd_once_seq_left:
    eval_cmd_once iv (Seq (Assign "x" (Const 6)) (Assign "x" (Const 7))) = Some ((set_var iv "x" 6), Seq Skip (Assign "x" (Const 7))).
Proof. auto. Qed.

Example eval_cmd_once_seq_right:
    eval_cmd_once iv (Seq Skip (Assign "x" (Const 7))) = Some (iv, Assign "x" (Const 7)).
Proof. auto. Qed.

Example eval_cmd_once_if_true:
    eval_cmd_once iv (If (Var "x") (Assign "x" (Const 7)) (Assign "x" (Const 8))) = Some (iv, Assign "x" (Const 7)).
Proof. auto. Qed.

Example eval_cmd_once_if_false:
    eval_cmd_once iv (If (Var "y") (Assign "x" (Const 7)) (Assign "x" (Const 8))) = Some (iv, Assign "x" (Const 8)).
Proof. auto. Qed.

Example eval_cmd_once_while_true:
    eval_cmd_once iv (While (Var "x") (Assign "x" (Const 7))) = Some (iv, Seq (Assign "x" (Const 7)) (While (Var "x") (Assign "x" (Const 7)))).
Proof. auto. Qed.

Example eval_cmd_once_while_false:
    eval_cmd_once iv (While (Var "y") (Assign "x" (Const 7))) = Some (iv, Skip).
Proof. auto. Qed.

(***************************************************************************************************
PROBLEM 17 [8 points, ~18 tactics]: complete the following lemma proving that [eval_cmd_once]
returns None only if [c] is Skip.
*)
Lemma eval_cmd_once_none_implies_skip:
    forall v c, eval_cmd_once v c = None -> c = Skip.
Proof.
    destruct c.
    - auto.
    - intro. discriminate H.
    (* - intro. firstorder. destruct c1. discriminate H. discriminate H.  destruct c1_1 unfold eval_cmd_once in H. constructor. firstorder. *)
    - simpl. intro. destruct (eval_cmd_once v c1). destruct p. discriminate H. discriminate H.
    - simpl. intro. destruct (Nat.eq_dec (eval_expr e v) 0). discriminate H. discriminate H.
    - simpl. intro. destruct (Nat.eq_dec (eval_expr e v) 0). discriminate H. discriminate H.
Qed.

(***************************************************************************************************
PROBLEM 18 [12 points, ~41 tactics]: complete the following lemma proving that [eval_cmd_once] is
_sound_ with respect to [step]; in other words, any behavior that [eval_cmd_once] allows is also
allowed by [step].

HINTS:
(1) As always, be careful what you induct over and what you intros. There are several different ways
    to make this induction work, but some are more tedious than others.
(2) If you used [is_skip] in your definition of [eval_cmd_once], then destructing on it here can be
    useful to break into case analysis, and its associated lemmas helpful in dispatching those cases.
(3) Sometimes when [destruct]ing, it can be helpful to remember an equality about the thing being
    destructed, as you might want to use that equality later. The syntax [destruct X eqn:?] does
    that, where ? is a placeholder Coq will use to give a name to the remembered equality (or you
    can just pick the name yourself: [destruct X eqn:Hx]). Try this out on some of your [destruct]s
    to get a feel for what equality it remembers for you, and whether that equality might be useful.
    I needed to use this on one [destruct] in this proof.
(4) This and Problem 19 are probably the trickiest proofs on this homework. If you're getting stuck,
    it might be a good idea to leave them [Admitted] and continue on to some easier proofs below.
*)
Lemma eval_cmd_once_implies_step:
    forall v c v' c', eval_cmd_once v c = Some (v', c') -> step (v, c) (v', c').
Proof.
    induction c.
    - simpl. intros. discriminate H.
    - intros. inversion H. apply stepAssign.
    (* TODO *)
    - {intros. simpl in H. destruct (eval_cmd_once v c1) eqn:Hx. inversion H; subst. destruct p . 
    inversion H; subst. apply stepSeqLeft. apply IHc1. }
    - intros. simpl in H. destruct (Nat.eq_dec (eval_expr e v) 0). inversion H. apply stepIfFalse. rewrite <- H1. assumption.
    inversion H. apply stepIfTrue. rewrite <- H1. assumption.
    - intros. simpl in H. destruct (Nat.eq_dec (eval_expr e v) 0). inversion H. apply stepWhileFalse. rewrite <- H1. assumption.
    inversion H. apply stepWhileTrue. rewrite <- H1. assumption.
    (* assumption. rewrite <- Hx. firstorder. auto. *)
Admitted.

(***************************************************************************************************
PROBLEM 19 [12 points, ~37 tactics]: complete the following lemma proving that [eval_cmd_once] is
_complete_ with respect to [step]; in other words, any behavior that [step] allows is also allowed
by [eval_cmd_once].

HINT: same hints as the previous lemma.
*)
Lemma step_implies_eval_cmd_once:
    forall v c v' c', step (v, c) (v', c') -> eval_cmd_once v c = Some (v', c').
Proof.
    induction c.
    - simpl. intros. apply skip_cannot_step in H.  contradiction.
    - intros. simpl. inversion H. reflexivity.
    - {intros. inversion H; subst; clear H. destruct (eval_cmd_once v c1). destruct p. }
    - intros. inversion H; subst; clear H. unfold eval_cmd_once. destruct (Nat.eq_dec (eval_expr e v') 0). contradiction. reflexivity. unfold eval_cmd_once.
    destruct ( Nat.eq_dec (eval_expr e v') 0). reflexivity. contradiction.
    - intros. inversion H; subst; clear H. unfold eval_cmd_once. destruct (Nat.eq_dec (eval_expr e v') 0). contradiction. reflexivity. unfold eval_cmd_once.
    destruct ( Nat.eq_dec (eval_expr e v') 0). reflexivity. contradiction.
Admitted.

(*
The reason we wrote [eval_cmd_once] is that we're going to use it to write a "fuel-based
interpreter" for [cmd]s. The idea of _fuel_ in an interpreter is to run for a fixed number of steps
(the fuel), and if the fuel runs out, to give up executing the program. In other words, fuel
provides a bound on how many steps we will take, and if the bound is hit, we'll terminate before
finishing the program. This works around the termination issue we discussed with denotational
semantics, but costs us completeness, as we'll see in problem 23.
*)

(***************************************************************************************************
PROBLEM 20 [4 points]: complete the definition of [eval_cmd_n], which takes as input a command and
valuation, as well as a [fuel] parameter, and runs [fuel] number of steps of the command using
[eval_cmd_once]. If the command terminates before the fuel runs out, [eval_cmd_n] returns the final
state (v, Skip). If [fuel] reaches 0 before the command terminates, [eval_cmd_n] returns the
valuation and command it reached and stops executing.

HINT: The intuition for why this function is OK is that the fuel decreases by one on every recursive
      call, and so eventually reaches zero. That means the function is guaranteed to terminate. But
      the way we write this definition needs to make the termination argument obvious to Coq. Coq's
      heuristics for termination are _structural_, in that it looks to see whether some inductive
      argument is getting _syntactically smaller_ at every step. That means that doing something
      like recursing with [fuel - 1] won't work automatically, because [fuel - 1] is not
      syntactically smaller than [fuel]. The [fuel] argument would be decreasing _mathematically_,
      but that's not the same as decreasing _structurally_, which is all Coq knows how to think
      about (because Coq has no built-in knowledge of [nat]).

      It's possible to make this work with subtraction by manually giving Coq a "measure" function
      that decreases on every call. But a far simpler thing to do, since we know the fuel is always
      going to decrease by 1, is to just [match] on the [fuel] to both decide when to terminate and
      choose what fuel to use for the next recursive call.
*)
Fixpoint eval_cmd_n (v: valuation) (c: cmd) (fuel: nat) : valuation * cmd :=
    (* TODO *)
    match fuel with
    | 0 => (v, c)
    | S n => match eval_cmd_once v c with
            | None => (v, Skip)
            | Some (v1, c1) => (eval_cmd_n v1 c1 n) 
            end
    end.

(***************************************************************************************************
PROBLEM 21 [8 points, ~18 tactics]: prove that this fuel-based interpreter is sound with respect to
stepStar; in other words, if [eval_cmd_n v c] returns a state, that state is reachable from the
state (v, c).

HINTS:
(1) Be careful what you choose to induct over. I wrote the quantifiers in an order that might be 
    inconvenient for your induction. You can use the [revert x] tactic to "undo" an [intro], moving
    [x] back into a forall quantifier in the goal. Note that [revert x] only works if nothing in the 
    context depends on [x], so it's not a get-out-of-jail free card in general, but will work here.
(2) Some of the earlier lemmas we've proved will be useful.
*)
Theorem eval_stepStar:
    forall v c fuel v' c',
        eval_cmd_n v c fuel = (v', c') -> stepStar (v, c) (v', c').
Proof.
    induction fuel.
    - intros. simpl in H. rewrite H. apply stepStarRefl.
    - {intros. inversion H. destruct (eval_cmd_once v c). destruct p. rewrite H1. 
    destruct c. econstructor. }
Admitted.

(***************************************************************************************************
PROBLEM 22 [4 points, ~3 tactics]: prove that if the fuel-based interpreter terminates with a
valuation [v], so too can the program's small-step semantics.
*)
Lemma eval_fuel_terminates:
    forall c fuel v',
        eval_cmd_n [] c fuel = (v', Skip) -> stepStar ([], c) (v', Skip).
Proof.
    intro c. intro fuel. intro v'. apply eval_stepStar.
Qed.

(***************************************************************************************************
PROBLEM 23 [6 points, ~23 tactics]: The other direction of the previous theorem is not true. For any
chosen value of [fuel], there exist commands [c] that will terminate (they can step-star to Skip),
but that [eval_cmd_n] with that fuel does not reach Skip.

Give such a counterexample for the case where [fuel = 2], and then prove it is a counterexample.
*)
Definition counterexample : cmd := (Seq (Seq (Assign "x" (Const 5)) (Assign "x" (Const 6))) (Assign "x" (Const 7))).

Example counterexample_is_valid:
    (exists v', stepStar ([], counterexample) (v', Skip)) /\
    (forall v', eval_cmd_n [] counterexample 2 <> (v', Skip)).
Proof.
    split.
    unfold counterexample. eexists. simpl. econstructor. econstructor. econstructor. apply stepAssign. unfold set_var. unfold eval_expr. econstructor. econstructor. apply stepSeqRight. econstructor. econstructor. apply stepAssign. unfold set_var. unfold eval_expr. econstructor. apply stepSeqRight. econstructor. apply stepAssign. unfold set_var. unfold eval_expr. apply stepStarRefl.
    unfold counterexample. simpl. unfold set_var. discriminate.
    (* TODO *)
Qed.

(***************************************************************************************************
PROBLEM 24 [2 points]: Here are two facts:
(1) This whole homework has been about proving that IMP programs terminate.
(2) Termination of IMP programs is undecidable, because IMP is Turing-complete and the Halting
    Problem tells us that termination of Turing machines is undecidable.

Why are these two facts not in contradiction with each other? In other words, why is it OK that we
were able to write proofs about termination, given what we know about undecidability? Answer in a
sentence or two.

ANSWER: I can think of two reasons here. One that in this homework we're dealing with a subclass of IMP programs. Secondly, we didn't really prove whether or not 
the fuel-based interpret halts on any IMP program; we only proved it for the operational semantics type interpreter.



*)


(****************************************************************************************************
PROBLEM 25 [4 points]: Finally, please take a moment to give us feedback on the homework by
answering three questions, as well as any other feedback you might have:
1. How long did the homework take you?
2. Which parts or problems were most interesting or helpful to you?
3. Which parts were especially frustrating or confusing? What could we improve next time?

It's fine to say "everything was fine" if you have nothing more to add. Any answer other than the
empty answer will get full points. Thanks!

ANSWER: everything was fine 

*)