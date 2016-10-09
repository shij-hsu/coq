(** * BasicTactics: Additional Basic Coq Tactics *)

Require Export Poly.

(* SOONER: (SCW) This and earlier chapters could use a few WORKINCLASS
   tags... *)

(** FULL: This chapter introduces several more proof strategies and
    tactics that, together, allow us to prove theorems about the
    functional programs we have been writing. In particular, we'll
    reason about functions that work with natural numbers and
    lists. We will see:

    - how to use auxiliary lemmas, in both forwards and backwards reasoning;
    - how to reason about data constructors, which are injective and disjoint;
    - how to create a strong induction hypothesis (and when
      strengthening is required); and
    - how to reason by case analysis.
 *)

(* ###################################################### *)
(** * The [apply] Tactic *)

(** FULL: We often encounter situations where the goal to be proved is
    exactly the same as some hypothesis in the context or some
    previously proved lemma. *)
(** TERSE: We can use [apply] when some hypothesis or an earlier
    lemma matches the goal: *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with 
     "[rewrite -> eq2. reflexivity.]" as we have 
     done several times above. But we can achieve the
     same effect in a single step by using the 
     [apply] tactic instead: *)
  apply eq2.  Qed.

(* SOONER: This is the first time we've seen a theorem with
multiple hypotheses.  Say a few words about how -> is right-associative
and perhaps tie in to currying. *)

(** FULL: The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)
(** TERSE: [apply] also works with _conditional_ hypotheses: *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2. 
  apply eq2. apply eq1.  Qed.

(** FULL: You may find it instructive to experiment with this proof
    and see if there is a way to complete it using just [rewrite]
    instead of [apply]. *)
(* HIDEFROMADVANCED *)
(* HIDE *)
(* SOONER: The following quiz is ambiguous, since you can solve it without apply, 
   by using "rewrite with (r:=m)". *)
(* QUIZ *)
(** Could we have completed this proof without [apply]?  

    (1 for yes, 2 for no) *)
(* /QUIZ *)
(* /HIDE *)

(** FULL: Typically, when we use [apply H], the statement [H] will
    begin with a [forall] binding some _universal variables_.  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)
(** TERSE: Observe how Coq picks appropriate values for the universal
    variables of the hypothesis here: *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(* FULL *)
(* EX2? (silly_ex) *)
(** Complete the following proof without using [simpl]. *)

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  (* ADMITTED *)
  intros H1 H2.
  apply H1. apply H2.  Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** FULL: To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal _exactly_ -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)
(** TERSE: The goal must match the hypothesis _exactly_ for [apply] to
    work: *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* Here we cannot use [apply] directly *)
Abort.

(** In this case we can use the [symmetry] tactic, which switches the
    left and right sides of an equality in the goal. *)

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this [simpl] is unnecessary, since 
            [apply] will perform simplification first. *)
  apply H.  Qed.         

(* FULL *)
(* EX3 (apply_exercise1) *)
(** Hint: you can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [SearchAbout] is
    your friend. *)
(* QUIETSOLUTION *)

(** For the slick solution to this exercise, we can use the fact that
    [rev] is involutive. *)

(* /QUIETSOLUTION *)
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  (* ADMITTED *)
  intros l l' eq. rewrite -> eq. 
  symmetry. 
  apply rev_involutive.   Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: rev_exercise1 *)
(** [] *)

(* EX1? (apply_rewrite) *)
(** Briefly explain the difference between the tactics [apply] and
    [rewrite].  Are there situations where both can usefully be
    applied?
  (* SOLUTION *) 
    The [rewrite] tactic is used to apply a known equality (a hypothesis
    from the context or a previously proved lemma) to modify the goal,
    replacing all occurrences of one side by the other.  The [apply]
    tactic uses a known implication (a hypothesis from the context, a
    previously proved lemma, or a constructor) to replace a goal that
    matches the conclusion of the implication with subgoals, one for
    each premise of the implication.  If the known fact is itself an
    equality (with no premises), then either tactic can be used.  (We
    will see below that each tactic can also be used to modify a
    hypothesis rather than the goal.)
(* /SOLUTION *)
*)
(** [] *)
(* /FULL *)
(* /HIDEFROMADVANCED *)


(* ###################################################### *)
(** * The [apply ... with ...] Tactic *)

(* HIDE: Does this belong with [apply] earlier? APT:
   Yes, after moving a couple of not-very-relevant exercises
   to the end section. 
   *)
(** FULL: The following silly example uses two rewrites in a row to
    get from [[a,b]] to [[e,f]]. *)
(** TERSE: Examples like this one use two rewrites to exploit the
    transitivity of equality.  We can abstract this into its own
    lemma. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** FULL: Since this is a common pattern, we might
    abstract it out as a lemma recording once and for all
    the fact that equality is transitive. *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. 
  reflexivity.  Qed.

(** FULL: Now, we should be able to use [trans_eq] to
    prove the above example.  However, to do this we need
    a slight refinement of the [apply] tactic. *)
(** TERSE: But applying this lemma requires a slight
    variation on [apply]: *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
(* FULL *)
  (* If we simply tell Coq [apply trans_eq] at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate [X]
     with [[nat]], [n] with [[a,b]], and [o] with [[e,f]].
     However, the matching process doesn't determine an
     instantiation for [m]: we have to supply one explicitly
     by adding [with (m:=[c,d])] to the invocation of
     [apply]. *)
(* /FULL *)
(* TERSE *)
  (* Doing [apply trans_eq] doesn't work!  But... *)
(* /TERSE *)
  apply trans_eq with (m:=[c;d]). apply eq1. apply eq2.   Qed.

(** FULL:  Actually, we usually don't have to include the name [m]
    in the [with] clause; Coq is often smart enough to
    figure out which instantiation we're giving. We could
    instead write: [apply trans_eq with [c,d]]. *)
(** TERSE: In practice, often Coq can figure out the correct variable
    and we can omit the "[m :=]" part. *)

(* FULL *)
(* EX3? (apply_with_exercise) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o). 
Proof.
  (* ADMITTED *)
  intros n m o p eq1 eq2. 
  apply trans_eq with m. apply eq2. apply eq1.   Qed.
(* /ADMITTED *)
(** [] *)

(* /FULL *)

(* ###################################################### *)
(** * The [inversion] tactic *)
(* SOONER: We're going to wind up admitting that inversion and
   destruct are similar, although here they look completely different.
   Be careful not to say anything that will turn out to be false
   later!  In fact, it would surely be possible to phrase the
   discussion here in terms that will extend naturally, in particular
   by talking explicitly about unification. *)

(** FULL: Recall the definition of natural numbers:
[[
     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.
]]
    It is clear from this definition that every number has one of two
    forms: either it is the constructor [O] or it is built by applying
    the constructor [S] to another number.  But there is more here than
    meets the eye: implicit in the definition (and in our informal
    understanding of how datatype declarations work in other
    programming languages) are two other facts:

    - The constructor [S] is _injective_.  That is, the only way we can
      have [S n = S m] is if [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n]. *)

(** FULL: Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the [cons] constructor is
    injective and [nil] is different from every non-empty list.  For
    booleans, [true] and [false] are unequal.  (Since neither [true]
    nor [false] take any arguments, their injectivity is not an issue.) *)
(** TERSE: In Coq, the constructors of inductive types are _injective_
    and _disjoint_.  

    E.g., for [nat]...

    - the only way we can have [S n = S m] is if [n = m] (that is, [S]
      is _injective_)

    - [O] is not equal to [S n] for any [n] (that is, [O] and [S] are
      _disjoint_) 
*)

(** Coq provides a tactic called [inversion] that allows us to exploit
    these principles in proofs.
 
    The [inversion] tactic is used like this.  Suppose [H] is a
    hypothesis in the context (or a previously proven lemma) of the
    form
[[
      c a1 a2 ... an = d b1 b2 ... bm
]]
    for some constructors [c] and [d] and arguments [a1 ... an] and
    [b1 ... bm].  Then [inversion H] instructs Coq to "invert" this
    equality to extract the information it contains about these terms:

    - If [c] and [d] are the same constructor, then we know, by the
      injectivity of this constructor, that [a1 = b1], [a2 = b2],
      etc.; [inversion H] adds these facts to the context, and tries
      to use them to rewrite the goal.

    - If [c] and [d] are different constructors, then the hypothesis
      [H] is contradictory.  That is, a false assumption has crept
      into the context, and this means that any goal whatsoever is
      provable!  In this case, [inversion H] marks the current goal as
      completed and pops it off the goal stack. *)

(** FULL: The [inversion] tactic is probably easier to understand by
    seeing it in action than from general descriptions like the above.
    Below you will find example theorems that demonstrate the use of
    [inversion] and exercises to test your understanding. *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.  Qed.

(* HIDEFROMADVANCED *)
Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity.  Qed.

(** FULL: As a convenience, the [inversion] tactic can also
    destruct equalities between complex values, binding
    multiple variables as it goes. *)

Theorem silly5 : forall (n m o : nat),
     [n;m] = [o;o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(* FULL *)
(* EX1 (sillyex1) *) 
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  (* ADMITTED *)
  intros X x y z l j eq1 eq2.
  inversion eq1. inversion eq2. symmetry. apply H0. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: sillyex1 *)
(** [] *)
(* /FULL *)

(* /HIDEFROMADVANCED *)
(* SOONER: Text needed for FULL version *)
Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.
(* HIDEFROMADVANCED *)

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra.  Qed.

(* /HIDEFROMADVANCED *)
(* FULL *)
(* EX1 (sillyex2) *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  (* ADMITTED *)
  intros X x y z l j eq1 eq2. inversion eq1. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: sillyex2 *)
(** [] *)
(* /FULL *)

(** FULL: While the injectivity of constructors allows us to reason
    [forall (n m : nat), S n = S m -> n = m], the reverse direction of
    the implication is an instance of a more general fact about
    constructors and functions, which we will often find useful: *)

(** TERSE: A useful theorem in the reverse direction: *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A), 
    x = y -> f x = f y. 
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed. 




(* SOONER: Also: "There should be more discussion and practice with
   how to deal with subexpressions that do not allow application of
   hypotheses, for example how to deal with the [S m] in [m + (S m)].
   Again, I sort of understand what to do with [destruct] and
   induction, but it would help to have more exercises that break down
   the process of making this connection." *)

(* EX2? (practice) *)
(** A couple more nontrivial but not-too-complicated proofs to work
    together in class, or for you to work as exercises. *)
(* HIDE: They may
    involve applying lemmas from earlier lectures or homeworks. 
   APT: Not true of what's left. *)
 
(* HIDE *)
(* HIDE: Not sure whether this is worth showing.  The chapter is
   getting long.  In any case, it doesn't belong here!*)
(** A slightly different way of making the same assertion
    as above. *)

(* SOONER: Danger! This is actually somewhat tricky.  In particular,
   it's important not to introduce [n] before the induction, which is
   something we may not have discussed at this point.  (BCP: We have,
   I guess, but perhaps this should be moved later anyway?) *)
Theorem length_snoc'' : forall (X : Type) (v : X)
                             (l : list X) (n : nat),
     S (length l) = n ->
     length (snoc l v) = n.
Proof.
  intros X v l. induction l as [| v' l'].
    - (* l = [] *) intros n eq. rewrite <- eq. reflexivity.
    - (* l = v' :: l' *) 
      intros n eq. simpl.
      (* Note the care we take here: first we introduce n
         and the equality, then we simplify.  This leaves
         the equation about length UN-simplified, which
         means our context will make a little bit more
         sense.  (The proof will work either way.) *)
      destruct n as [| n'].
      (* Now we destruct n; if it's 0, we have a
         contradiction immediately. *)
      + (* n = 0 *) inversion eq.
      + (* n = S n' *)
      (* We use the IH and the inversion of eq to prove the 
         equation we want about length. *)
        apply f_equal. apply IHl'. inversion eq. 
        reflexivity. Qed.
(* /HIDE *)

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  (* ADMITTED *)
  intros n. intros Heq.
  destruct n as [| n'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    inversion Heq. Qed.
(* /ADMITTED *)

Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  (* ADMITTED *)
  intros n. intros Heq.
  destruct n as [| n'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    inversion Heq. Qed.
(* /ADMITTED *)
(** [] *)

(* QUIZ *)
(** Suppose Coq's proof state looks like 
[[
    1 subgoals, subgoal 1

      H : false = true
      ============================
       negb true = negb false
]]
    and we apply the tactic [inversion H].  What will happen?

    (1) No new information available in the context

    (2) Substitute [true] with [false] in the conclusion, leaving 
        [negb false = negb false]

    (3) "No more subgoals"

*)
(* HIDE *)
Theorem quiz1 : false = true -> negb true = negb false.
Proof. intros H. inversion H. Qed.
(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** Suppose Coq's proof state looks like 
[[
    1 subgoals, subgoal 1

  x : bool
  y : bool
  H : x = y
  ============================
   y = x
]]
    and we apply the tactic [inversion H].  What will happen?

    (1) No new information available in the context

    (2) Substitute [x] with [y] in the conclusion, leaving 
        [y = y]

    (3) "No more subgoals"

*)
(* HIDE *)
Theorem quiz3 : forall x y : bool, x = y -> y = x.
Proof. intros x y H. inversion H. Abort.
(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** Suppose Coq's proof state looks like 
[[
    1 subgoals, subgoal 1

      H : negb false = negb true
      ============================
       true = false
]]
    and we apply the tactic [inversion H].  What will happen?

    (1) No new information available in the context

    (2) Substitute [true] with [false] in the conclusion, leaving 
        [false = false]

    (3) "No more subgoals"

*)
(* HIDE *)
Theorem quiz2 : negb true = negb false -> false = true.
Proof. intros H. inversion H. Qed.
(* /HIDE *)
(* /QUIZ *)

(* ###################################################### *)
(** * Using Tactics on Hypotheses *)

(** FULL: By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic [simpl in H] performs simplification in
    the hypothesis named [H] in the context. *)
(** TERSE: Tactics often come with "[...in...]" variants that can be
    used on hypotheses instead of goals. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b. 
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** FULL: Similarly, the tactic [apply L in H] matches some
    conditional statement [L] (of the form [L1 -> L2], say) against a
    hypothesis [H] in the context.  However, unlike ordinary
    [apply] (which rewrites a goal matching [L2] into a subgoal [L1]),
    [apply L in H] matches [H] against [L1] and, if successful,
    replaces it with [L2].
 
    In other words, [apply L in H] gives us a form of "forward
    reasoning" -- from [L1 -> L2] and a hypothesis matching [L1], it
    gives us a hypothesis matching [L2].  By contrast, [apply L] is
    "backward reasoning" -- it says that if we know [L1->L2] and we
    are trying to prove [L2], it suffices to prove [L1].  

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)
(** TERSE: The tactic [apply] is a form of "backward reasoning": it
    says "We're trying to prove [X] and we know [Y->X], so if we can
    prove [Y] we'll be done."  By contrast, the variant
    [apply... in...] is "forward reasoning": it says "We know [Y] and
    we know [Y->X], so we can deduce [X]." *)
(* HIDEFROMADVANCED *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. 
  apply H.  Qed.

(* /HIDEFROMADVANCED *)
(** FULL: Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_, and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.
    If you've seen informal proofs before (for example, in a math or
    computer science class), they probably used forward reasoning.  In
    general, Coq tends to favor backward reasoning, but in some
    situations the forward style can be easier to use or to think
    about.  *)

(* EX3! (plus_n_n_injective) *)
(** Practice using "in" variants in this exercise. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* Hint: use the plus_n_Sm lemma *)
    (* ADMITTED *)
    - (* n = 0 *) intros m. simpl. intros eq. destruct m as [| m'].
      + (* m = 0 *) reflexivity.
      + (* m = S m' *) inversion eq.
    - (* n = S n' *) intros m eq. destruct m as [| m'].
      + (* m = 0 *) inversion eq.
      + (* m = S m' *)
        apply f_equal. apply IHn'.
        (* just [simpl in eq] doesn't work here *)
        rewrite <- plus_n_Sm in eq. rewrite <- plus_n_Sm in eq.   
        inversion eq. reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: plus_n_n_injective *)
(** [] *)

(* ###################################################### *)
(** * Varying the Induction Hypothesis *)

(* TERSE *)
(** Here's a function for doubling a natural number (from the [Induction]
    chapter): *)
(* HIDE: Repeated because double only appears in the FULL version of 
   Induction.v *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
(* /TERSE *)

(** FULL: Sometimes it is important to control the exact form of the
    induction hypothesis when carrying out inductive proofs in Coq.
    In particular, we need to be careful about which of the
    assumptions we move (using [intros]) from the goal to the context
    before invoking the [induction] tactic.  For example, suppose 
    we want to show that the [double] function is injective -- i.e., 
    that it always maps different arguments to different results:  
[[
    Theorem double_injective: forall n m, double n = double m -> n = m. 
]]
    The way we _start_ this proof is a little bit delicate: if we 
    begin it with
[[
      intros n. induction n.
]] 
    all is well.  But if we begin it with
[[
      intros n m. induction n.
]]
    we get stuck in the middle of the inductive case... *)
(** TERSE: Suppose we want to show that [double] is injective -- i.e.,
    that it always maps different arguments to different results.  The
    way we _start_ this proof is a little bit delicate: *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) inversion eq. 
  - (* n = S n' *) intros eq. destruct m as [| m'].
    + (* m = O *) inversion eq.
    + (* m = S m' *)  apply f_equal. 
      (* Here we are stuck.  The induction hypothesis, [IHn'], does
         not give us [n' = m'] -- there is an extra [S] in the
         way -- so the goal is not provable. *)
      Abort.
(* HIDEFROMADVANCED *)

(** What went wrong? *)

(** FULL: The problem is that, at the point we invoke the induction
    hypothesis, we have already introduced [m] into the context -- 
    intuitively, we have told Coq, "Let's consider some particular
    [n] and [m]..." and we now have to prove that, if [double n =
    double m] for _these particular_ [n] and [m], then [n = m].

    The next tactic, [induction n] says to Coq: We are going to show
    the goal by induction on [n].  That is, we are going to prove that
    the proposition

      - [P n]  =  "if [double n = double m], then [n = m]"

    holds for all [n] by showing

      - [P O]              

         (i.e., "if [double O = double m] then [O = m]")

      - [P n -> P (S n)]  

        (i.e., "if [double n = double m] then [n = m]" implies "if
        [double (S n) = double m] then [S n = m]").

    If we look closely at the second statement, it is saying something
    rather strange: it says that, for a _particular_ [m], if we know

      - "if [double n = double m] then [n = m]"

    then we can prove

       - "if [double (S n) = double m] then [S n = m]".

    To see why this is strange, let's think of a particular [m] --
    say, [5].  The statement is then saying that, if we know

      - [Q] = "if [double n = 10] then [n = 5]"

    then we can prove

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    But knowing [Q] doesn't give us any help with proving [R]!  (If we
    tried to prove [R] from [Q], we would say something like "Suppose
    [double (S n) = 10]..." but then we'd be stuck: knowing that
    [double (S n)] is [10] tells us nothing about whether [double n]
    is [10], so [Q] is useless at this point.) *)

(** To summarize: Trying to carry out this proof by induction on [n]
    when [m] is already in the context doesn't work because we are
    trying to prove a relation involving _every_ [n] but just a
    _single_ [m]. *)
(* /HIDEFROMADVANCED *)

(** The good proof of [double_injective] leaves [m] in the goal
    statement at the point where the [induction] tactic is invoked on
    [n]: *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) inversion eq. 
  - (* n = S n' *) 
(* FULL *)
    (* Notice that both the goal and the induction
       hypothesis have changed: the goal asks us to prove
       something more general (i.e., to prove the
       statement for _every_ [m]), but the IH is
       correspondingly more flexible, allowing us to
       choose any [m] we like when we apply the IH.  *)
(* /FULL *)
    intros m eq.
(* FULL *)
    (* Now we choose a particular [m] and introduce the
       assumption that [double n = double m].  Since we
       are doing a case analysis on [n], we need a case
       analysis on [m] to keep the two "in sync." *)
(* /FULL *)
    destruct m as [| m'].
    + (* m = O *) 
(* FULL *)
      (* The 0 case is trivial *)
(* /FULL *)
      inversion eq.  
    + (* m = S m' *)  
      apply f_equal. 
(* FULL *)
      (* At this point, since we are in the second
         branch of the [destruct m], the [m'] mentioned
         in the context at this point is actually the
         predecessor of the one we started out talking
         about.  Since we are also in the [S] branch of
         the induction, this is perfect: if we
         instantiate the generic [m] in the IH with the
         [m'] that we are talking about right now (this
         instantiation is performed automatically by
         [apply]), then [IHn'] gives us exactly what we
         need to finish the proof. *)
(* /FULL *)
      apply IHn'. inversion eq. reflexivity. Qed.

(* HIDEFROMADVANCED *)
(** What this teaches us is that we need to be careful about using
    induction to try to prove something too specific: If we're proving
    a property of [n] and [m] by induction on [n], we may need to
    leave [m] generic. *)

(* /HIDEFROMADVANCED *)
(** The proof of this theorem (left as an exercise) has to be treated similarly: *)

(* FULL *)
(* EX2 (beq_nat_true) *)
(* /FULL *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  (* ADMITTED *)
  intros n. induction n as [| n'].
  - (* n = 0 *) 
    intros m. destruct m as [| m'].
    + (* m = 0 *) reflexivity.  
    + (* m = S m' *) simpl. intros contra. inversion contra. 
  - (* n = S n' *)
    intros m. destruct m as [| m'].
    + (* m = 0 *) simpl. intros contra. inversion contra.
    + (* m = S m' *) simpl. intros H.
      apply f_equal. apply IHn'. apply H. Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: beq_nat_true *)
(* FULL *)
(** [] *)

(* EX2A (beq_nat_true_informal) *)
(** Give a careful informal proof of [beq_nat_true], being as explicit
    as possible about quantifiers. *)
(* GRADE_MANUAL 2: informal proof *)

(* SOLUTION *)
(** _Theorem_: For all natural numbers n and m, if [beq_nat n m = true],
      then [n = m].

    _Proof_ (more pedantic, arguably less clear): We show, by
    induction on [n], that, for all [m], if [beq_nat n m = true], then
    [n = m].

      - Suppose [n = 0].  We must show, for all [m], that if 
        [beq_nat 0 m = true], then [0 = m].  We proceed by cases on [m].
        
          - If [m = 0], we must show [0 = 0], which holds by
            reflexivity.

          - If [m = S m'], our hypothesis states that [beq_nat 0
            (S m') = true].  But [beq_nat 0 (S m')] reduces to [false], so
            this is absurd.

      - Otherwise, [n = S n'], and the induction hypothesis states
        that for all natural numbers m', if [beq_nat n' m' = true],
        then [n' = m'].  We must show that if [beq_nat (S n') m = true], 
        then [S n' = m].  We again proceed by cases on m.

          - If [m = 0], the IH states that [beq_nat (S n') 0 = true],
            which is absurd.

          - Otherwise [m = S m'], and the IH states that 
            [beq_nat (S n') (S m') = true], which simplifies to 
            [beq_nat n' m' = true].  We may therefore apply the
            induction hypothesis (instantiated at [m']) to conclude 
            that [n' = m'], which immediately implies that 
            [S n' = S m']. []

    _Proof_ (more natural style): By induction on [n].

      - Suppose [n = 0].  We must show that if [beq_nat 0 m = true],
        then [0 = m].  Now, it must be that [m = 0] and must therefore
        show [0 = 0], which is true by reflexivity.  (Otherwise, we
        would have [m = S m'] and [beq_nat 0 (S m') = true].  But
        [beq_nat 0 (S m')] reduces to [false], so we would have 
        [true = false], a contradiction.)

      - Otherwise, [n = S n'], and the induction hypothesis states
        that for all natural numbers m', if [beq_nat n' m' = true],
        then [n' = m'].  We must show that if [beq_nat (S n') 
        m = true], then [S n' = m].  This time, it cannot be that [m = 0],
        since then the hypothesis would state that 
        [beq_nat (S n') 0 = true], which is absurd.  So suppose 
        [m = S m'] for some [m'].  The IH now states that 
        [beq_nat (S n') (S m') = true], which simplifies to 
        [beq_nat n' m' = true].  We may therefore
        apply the induction hypothesis (instantiated at [m']) to
        conclude that [n' = m'], which immediately implies that 
        [S n' = S m'].  [] *)
(* /SOLUTION *)
(** [] *)

(* /FULL *)

(** The strategy of doing fewer [intros] before an [induction] doesn't
    always work directly; sometimes a little _rearrangement_ of
    quantified variables is needed.  Suppose, for example, that we
    wanted to prove [double_injective] by induction on [m] instead of
    [n]. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq. 
  - (* m = S m' *) intros eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *)  apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

(** The problem is that, to do induction on [m], we must first
    introduce [n].  (If we simply say [induction m] without
    introducing anything first, Coq will automatically introduce
    [n] for us!)   *)

(* HIDEFROMADVANCED *)
(** What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that [m] is quantified before [n].  This
    will work, but it's not nice: We don't want to have to mangle the
    statements of lemmas to fit the needs of a particular strategy for
    proving them -- we want to state them in the most clear and
    natural way. *)

(* /HIDEFROMADVANCED *)
(**  What we can do instead is to first introduce all the
    quantified variables and then _re-generalize_ one or more of
    them, taking them out of the context and putting them back at
    the beginning of the goal.  The [generalize dependent] tactic
    does this. *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. 
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.

(* SOONER: Somewhere (in this file? in Poly?), we need to do a more
   careful discussion of the way generalized IHs are handled in
   informal proofs.  Basically, the practice seems to be to assume
   we're working with a "general enough" IH, but seldom to bother
   saying exactly what it is! *)

(** FULL: Let's look at an informal proof of this theorem.  Note that
    the proposition we prove by induction leaves [n] quantified,
    corresponding to the use of generalize dependent in our formal
    proof.

_Theorem_: For any nats [n] and [m], if [double n = double m], then
  [n = m].

_Proof_: Let [m] be a [nat]. We prove by induction on [m] that, for
  any [n], if [double n = double m] then [n = m].

  - First, suppose [m = 0], and suppose [n] is a number such
    that [double n = double m].  We must show that [n = 0].

    Since [m = 0], by the definition of [double] we have [double n =
    0].  There are two cases to consider for [n].  If [n = 0] we are
    done, since this is what we wanted to show.  Otherwise, if [n = S
    n'] for some [n'], we derive a contradiction: by the definition of
    [double] we would have [double n = S (S (double n'))], but this
    contradicts the assumption that [double n = 0].

  - Otherwise, suppose [m = S m'] and that [n] is again a number such
    that [double n = double m].  We must show that [n = S m'], with
    the induction hypothesis that for every number [s], if [double s =
    double m'] then [s = m'].
 
    By the fact that [m = S m'] and the definition of [double], we
    have [double n = S (S (double m'))].  There are two cases to
    consider for [n].

    If [n = 0], then by definition [double n = 0], a contradiction.
    Thus, we may assume that [n = S n'] for some [n'], and again by
    the definition of [double] we have [S (S (double n')) = S (S
    (double m'))], which implies by inversion that [double n' = double
    m'].

    Instantiating the induction hypothesis with [n'] thus allows us to
    conclude that [n' = m'], and it follows immediately that [S n' = S
    m'].  Since [S n' = n] and [S m' = m], this is just what we wanted
    to show. [] *)



(** Here's another illustration of [inversion] and using an
    appropriately general induction hypothesis.  This is a slightly
    roundabout way of stating a fact that we have already proved
    above.  The extra equalities force us to do a little more
    equational reasoning and exercise some of the tactics we've seen
    recently. *)

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l. induction l as [| v' l'].

  - (* l = [] *) 
    intros n eq. rewrite <- eq. reflexivity.

  - (* l = v' :: l' *) 
    intros n eq. simpl. destruct n as [| n'].
    + (* n = 0 *) inversion eq.
    + (* n = S n' *)
      apply f_equal. apply IHl'. inversion eq. reflexivity. Qed.

(** FULL: It might be tempting to start proving the above theorem
    by introducing [n] and [eq] at the outset.  However, this leads
    to an induction hypothesis that is not strong enough.  Compare
    the above to the following (aborted) attempt: *)
(** TERSE: Note that introducing [n] too early doesn't yield a 
    general enough induction hypothesis: *)

Theorem length_snoc_bad : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l n eq. induction l as [| v' l'].

  - (* l = [] *) 
    rewrite <- eq. reflexivity.

  - (* l = v' :: l' *) 
    simpl. destruct n as [| n'].
    + (* n = 0 *) inversion eq.
    + (* n = S n' *)
      apply f_equal. Abort. (* apply IHl'. *) (* The IH doesn't apply! *)


(** FULL: As in the double examples, the problem is that by
    introducing [n] before doing induction on [l], the induction
    hypothesis is specialized to one particular natural number, namely
    [n].  In the induction case, however, we need to be able to use
    the induction hypothesis on some other natural number [n'].
    Retaining the more general form of the induction hypothesis thus
    gives us more flexibility.

    In general, a good rule of thumb is to make the induction hypothesis
    as general as possible. *)

(* FULL *)
(* EX3! (gen_dep_practice) *)
(** Prove this by induction on [l]. *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  (* ADMITTED *)
  intros n X l. generalize dependent n. induction l as [| x l'].
  - (* l = nil *) reflexivity.
  - (* l = x :: l' *) intros n eq. simpl. simpl in eq.
    rewrite <- eq.  apply IHl'.  reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: index_after_last *)
(** [] *)

(* EX3?A (index_after_last_informal) *)
(** Write an informal proof corresponding to your Coq proof
    of [index_after_last]:
 
     _Theorem_: For all sets [X], lists [l : list X], and numbers
      [n], if [length l = n] then [index n l = None].
 
     _Proof_:
     (* SOLUTION *)
      By induction on [l].
 
      - Suppose [l = []].  We must show, for all numbers [n],
        that, if length [[] = n], then [index n [] =
        None].
 
        This follows immediately from the definition of index.
 
      - Suppose [l = x :: l'] for some [x] and [l'], where
        [length l' = n'] implies [index n' l' = None], for
        any number [n'].  We must show, for all [n], that, if
        [length (x::l') = n] then [index n (x::l') =
        None].
 
        Let [n] be a number with [length l = n].  Since
[[
          length l = length (x::l') = S (length l'),
]]
        it suffices to show that 
[[
          index (length l') l' = None.
]]  
        But this follows directly from the induction hypothesis,
        picking [n'] to be length [l'].  []
     (* /SOLUTION *)
[]
*)

(* EX3? (gen_dep_practice_more) *)
(** Prove this by induction on [l]. *)

Theorem length_snoc''' : forall (n : nat) (X : Type) 
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  (* ADMITTED *)
  intros n X v l. 
  generalize dependent n.
  induction l as [| x l'].
  - (* l = nil *) intros n eq. rewrite <- eq. reflexivity.
  - (* l = x :: l' *) simpl. intros n eq.
    assert (length (snoc l' v) = n).
    { rewrite <- eq. apply IHl'. reflexivity. }
    rewrite -> H. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX3? (app_length_cons) *)
(** Prove this by induction on [l1], without using [app_length]
    from [Lists]. *)

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) 
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  (* ADMITTED *)
  intros X l1 l2 x. induction l1 as [| y l1'].
  - (* l1 = nil *) 
    intros n eq. apply eq.
  - (* l1 = y :: l1' *) 
    simpl. intros n eq. rewrite <- eq.
      assert (S (length (l1' ++ l2)) = length (l1' ++ x :: l2)).
        apply IHl1'. reflexivity.
      rewrite -> H. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX4? (app_length_twice) *)
(** Prove this by induction on [l], without using [app_length] from [Lists]. *)
(* SOONER: This might be a little bit hard??  
   There are a couple of tricky little points!  
   APT: Yes: the nested induction is a first, I think. And it would
     be good to have seen rewrite with an applied term; otherwise
     a kludgy forward [assert] or [pose proof] seems needed. *)
(* SOONER: no need for a _nested_ induction per se -- side lemmas will
   do the trick, too, and students have been exposed to that
   already.  *)
(* SOONER: APT: Yes, but the lemma above is terribly ad-hoc, as well
   as ill-suited for its use here!
   I realize that the pedagogical point here has nothing to do with
   developing sensible lemmas for lists, but these seem pretty distorted. *)

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  (* ADMITTED *)
  intros X n l. 
  generalize dependent n.
  induction l as [| x l'].
  - (* l = nil *) 
    simpl. intros n eq. rewrite <- eq. reflexivity.
  - (* l = x :: l' *) 
    simpl. intros n eq. rewrite <- eq.
    rewrite <- plus_n_Sm. simpl. rewrite <- IHl' by reflexivity.
    assert (S (length (l' ++ l')) = length (l' ++ x :: l')).
    { apply app_length_cons with x. reflexivity. }
    rewrite <- H. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)


(* EX3? (double_induction) *)
(* SOONER: Comment from reader: I would call this "diagonal induction"
   rather than "double induction". The latter word, for me, means a
   nested pair of inductions. *)
(** Prove the following principle of induction over two naturals. *)

Theorem double_induction: forall (P : nat -> nat -> Prop), 
  P 0 0 ->
  (forall m, P m 0 -> P (S m) 0) ->
  (forall n, P 0 n -> P 0 (S n)) ->
  (forall m n, P m n -> P (S m) (S n)) ->
  forall m n, P m n.
Proof.
  (* ADMITTED *)
  intros P H00 HS0 H0S HSS.
  induction m.
  - (* m = 0 *)
    intro n. induction n.
    + (* n = 0 *)
      apply H00.
    + (* n = S n *)
      apply H0S. apply IHn.
  - (* m = S m *)
    intro n. destruct n.
    + (* n = 0 *)
      apply HS0. apply IHm.
    + (* n = S n *)
      apply HSS. apply IHm.
Qed.
(* /ADMITTED *)
(** [] *)

(* /FULL *)

(* ###################################################### *)
(** * Using [destruct] on Compound Expressions *)

(** FULL: We have seen many examples where the [destruct] tactic is
    used to perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)
(** TERSE: The [destruct] tactic can be used on expressions as well as
    variables: *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun. 
  destruct (beq_nat n 3).
    - (* beq_nat n 3 = true *) reflexivity.
    - (* beq_nat n 3 = false *) destruct (beq_nat n 5).
      + (* beq_nat n 5 = true *) reflexivity.
      + (* beq_nat n 5 = false *) reflexivity.  Qed.

(** FULL: After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (beq_nat n 3) then ... else ...].  Well,
    either [n] is equal to [3] or it isn't, so we use [destruct
    (beq_nat n 3)] to let us reason about the two cases. 

    In general, the [destruct] tactic can be used to perform case
    analysis of the results of arbitrary computations.  If [e] is an
    expression whose type is some inductively defined type [T], then,
    for each constructor [c] of [T], [destruct e] generates a subgoal
    in which all occurrences of [e] (in the goal and in the context)
    are replaced by [c].

*)

(* FULL *)
(* EX1 (override_shadow) *)
Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  (* ADMITTED *)
  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).
  - (* beq_nat k1 k2 = true *)
    reflexivity.
  - (* beq_nat k1 k2 = false *)
    reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 1: override_shadow *)
(** [] *)

(* EX3? (combine_split) *)
(** Complete the proof below *)

(* LATER: AAA: Should we rework this exercise so that it doesn't
   depend on their own definition of [split] given in Poly.v? *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  (* ADMITTED *)
  intros X Y l. induction l as [| [x y] l'].
  - (* l = [] *)
    intros l1 l2 H.
    inversion H.
    reflexivity.
  - (* l = (x, y) :: l' *)
    intros l1 l2 H.
    simpl in H.
    destruct (split l') as [lx ly].
    inversion H.
    simpl.
    rewrite -> IHl'.
      reflexivity.
      reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(** Sometimes, doing a [destruct] on a compound expression (a
    non-variable) will erase information we need to complete a proof. *)
(** FULL: For example, suppose
    we define a function [sillyfun1] like this: *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** FULL: And suppose that we want to convince Coq of the rather
    obvious observation that [sillyfun1 n] yields [true] only when [n]
    is odd.  By analogy with the proofs we did with [sillyfun] above,
    it is natural to start the proof like this: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Abort.

(** FULL: We get stuck at this point because the context does not
    contain enough information to prove the goal!  The problem is that
    the substitution peformed by [destruct] is too brutal -- it threw
    away every occurrence of [beq_nat n 3], but we need to keep some
    memory of this expression and how it was destructed, because we
    need to be able to reason that since, in this branch of the case
    analysis, [beq_nat n 3 = true], it must be that [n = 3], from
    which it follows that [n] is odd.

    What we would really like is to substitute away all existing
    occurences of [beq_nat n 3], but at the same time add an equation
    to the context that records which case we are in.  The [eqn:]
    qualifier allows us to introduce such an equation (with whatever
    name we choose). *)
(** TERSE: 
    We can use the [eqn:] qualifier to save that information. *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
(* FULL *)
  (* Now we have the same state as at the point where we got stuck
    above, except that the context contains an extra equality
    assumption, which is exactly what we need to make progress. *)
(* /FULL *)
    - (* e3 = true *) apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
(* FULL *)
     (* When we come to the second equality test in the body of the
       function we are reasoning about, we can use [eqn:] again in the
       same way, allow us to finish the proof. *)
(* /FULL *)
      destruct (beq_nat n 5) eqn:Heqe5. 
        + (* e5 = true *)
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) inversion eq.  Qed.


(* FULL *)
(* EX2 (destruct_eqn_practice) *)
Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  (* ADMITTED *)
  intros f b.
  destruct b.
  - (* b = true *)
    destruct (f true) eqn:Heqftrue. 
    + (* f true = true *)
      rewrite Heqftrue.
      apply Heqftrue.
    + (* f true = false *)
      destruct (f false) eqn:Heqffalse.
      * (* f false = true *)
        apply Heqftrue.
      * (* f false = false *)
        apply Heqffalse.
  - (* b = false *)
    destruct (f false) eqn:Heqffalse.
    + (* f false = true *)
      destruct (f true) eqn: Heqftrue.
      * (* f true = true *)
        apply Heqftrue.
      * (* f true = false *)
        apply Heqffalse.
    + (* f false = false *)
      rewrite Heqffalse.
      apply Heqffalse.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: bool_fn_applied_thrice *)
(** [] *)

(* EX2 (override_same) *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
  (* ADMITTED *)
  intros X x1 k1 k2 f. intros Hx1.
  unfold override.
  destruct (beq_nat k1 k2) eqn:Heq. 
  - (* beq_nat k1 k2 = true *)
    apply beq_nat_true in Heq.
    rewrite <- Heq.
    symmetry. apply Hx1.
  - (* beq_nat k1 k2 = false *)
    reflexivity.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 2: override_same *)
(** [] *)
(* /FULL *)

(* ################################################################## *)
(** * Review *)

(** We've now seen a bunch of Coq's fundamental tactics.  We'll
    introduce a few more as we go along through the coming lectures,
    and later in the course we'll introduce some more powerful
    _automation_ tactics that make Coq do more of the low-level work
    in many cases.  But basically we've got what we need to get work
    done.

    Here are the ones we've seen:

      - [intros]: 
        move hypotheses/variables from goal to context 

      - [reflexivity]:
        finish the proof (when the goal looks like [e = e])

      - [apply]:
        prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: 
        apply a hypothesis, lemma, or constructor to a hypothesis in
        the context (forward reasoning)

      - [apply... with...]:
        explicitly specify values for variables that cannot be
        determined by pattern matching

      - [simpl]:
        simplify computations in the goal 

      - [simpl in H]:
        ... or a hypothesis 

      - [rewrite]:
        use an equality hypothesis (or lemma) to rewrite the goal 

      - [rewrite ... in H]:
        ... or a hypothesis 

      - [symmetry]:
        changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]:
        changes a hypothesis of the form [t=u] into [u=t]

      - [unfold]:
        replace a defined constant by its right-hand side in the goal 

      - [unfold... in H]:
        ... or a hypothesis  

      - [destruct... as...]:
        case analysis on values of inductively defined types 

      - [destruct... eqn:...]:
        specify the name of an equation to be added to the context,
        recording the result of the case analysis

      - [induction... as...]:
        induction on values of inductively defined types 

      - [inversion]:
        reason by injectivity and distinctness of constructors

      - [assert (e) as H]:
        introduce a "local lemma" [e] and call it [H] 

      - [generalize dependent x]:
        move the variable [x] (and anything else that depends on it)
        from the context back to an explicit hypothesis in the goal
        formula 
*)

(* TERSE *)
(* ###################################################### *)
(** * Micro Sermon *)

(** Mindless proof-hacking is a terrible temptation... 

    Try to resist! *)

(* /TERSE *)
(* FULL *)
(* ###################################################### *)
(** * Additional Exercises *)

(* FULL *)
(* EX3 (beq_nat_sym) *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  (* ADMITTED *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    intros m. destruct m as [| m'].
    + (* m = 0 *) reflexivity. 
    + (* m = S m' *) reflexivity. 
  - (* n = S n' *)
    intros m. destruct m as [| m'].
    + (* m = 0 *) reflexivity.
    + (* m = S m' *) apply IHn'.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: beq_nat_sym *)
(** [] *)

(* EX3A? (beq_nat_sym_informal) *)
(** Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Proof:
   (* SOLUTION *)
   Let an arbitrary nat [n] be given.  We go by induction
   on [n].

   - For the base case, we have [n = 0].  Let [m] be given.
     We must show that
[[
       beq_nat 0 m = beq_nat m 0
]]
     Either [m = 0] or not.

     - If [m = 0], we must show [beq_nat 0 0 = beq_nat 0 0]
       which is true by reflexivity.

     - Otherwise, [m = S m'] for some [m'], and we must show
       [beq_nat 0 (S m') = beq_nat (S m') 0]. By the definition
       of [beq_nat], both sides are [false].

   - In the inductive case, we have [n = S n'] for some
     [n'] such that, for any [m],
[[
       beq_nat n' m = beq_nat m n'
]]
     Let [m] be given.  Again, [m] is either zero or nonzero.
  
     - Suppose first [m = 0].  It's
       enough to show [beq_nat (S n') 0 = beq_nat 0 (S n')].
       By the definition of [beq_nat], both sides are [false].
   
     - Otherwise, [m = S m'] for some [m'].  By the
       assumption, it's enough to show:
[[
         beq_nat (S n') (S m') = beq_nat (S m') (S n')
]]
       And, by the definition of [beq_nat], this reduces to
       showing:
[[
         beq_nat m' n' = beq_nat n' m'.
]]
       which is exactly the induction hypothesis.
   (* /SOLUTION *)
[]
 *)
(* /FULL *)

(* FULL *)
(* EX3? (beq_nat_trans) *)
Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  (* ADMITTED *)
  intros n m p. intros Hnm Hmp.
  apply beq_nat_true in Hnm.
  rewrite -> Hnm.
  rewrite -> Hmp.
  reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* FULL *)
(* EX3A (split_combine) *)
(** We have just proven that for all lists of pairs, [combine] is the
    inverse of [split].  How would you formalize the statement that
    [split] is the inverse of [combine]? When is this property true?

    Complete the definition of [split_combine_statement] below with a
    property that states that [split] is the inverse of
    [combine]. Then, prove that the property holds. (Be sure to leave
    your induction hypothesis general by not doing [intros] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split] [combine l1 l2 = (l1,l2)] to be true?)  *)

Definition split_combine_statement : Prop :=
(* ADMIT *)
  forall (X Y:Type) (l1 : list X) (l2 : list Y),
    length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
(* /ADMIT *)

Theorem split_combine : split_combine_statement.
Proof.
(* ADMITTED *)
  intros X Y. induction l1 as [| x l1'].
  - (* l1 = [] *)
    intros l2 Heq. destruct l2 as [|y l2'].
    + (* l2 = [] *) reflexivity.
    + (* l2 = y :: l2' *) inversion Heq.
  - (* l1 = x :: l1' *)
    intros l2 Heq. destruct l2 as [|y l2'].
    + (* l2 = [] *) inversion Heq.
    + (* l2 = y :: l2' *)
      simpl. rewrite IHl1'. reflexivity.
      inversion Heq. reflexivity.  Qed.
(* /ADMITTED *)

(* GRADE_THEOREM 3: split_combine *)

(* QUIETSOLUTION *)
(** Here is another approach *)

Theorem split_combine' : forall (X Y:Type) l (l1 : list X) (l2 : list Y),
  (l1, l2) = split l -> split (combine l1 l2) = (l1, l2).
Proof.
  induction l as [| [x y] l'].
  - (* l = [] *) intros l1 l2 Heq.
    simpl in Heq. inversion Heq. reflexivity.
  - (* l = (x,y) :: l' *) intros l1 l2 Heq.
    simpl in Heq. destruct (split l') as [l1' l2'].
    inversion Heq. simpl. rewrite IHl'.
    reflexivity. reflexivity.  Qed.
(* /QUIETSOLUTION *)
(** [] *)
(* /FULL *)

(* FULL *)
(* EX3! (override_permute) *)
Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  (* ADMITTED *)
  (* This simple proof is by Aaditya Shirodkar *)
  intros X x1 x2 k1 k2 k3 f H. unfold override.
  destruct (beq_nat k1 k3) eqn: Heq13.
  - (* beq_nat k1 k3 = true *)
    apply beq_nat_true in Heq13. 
    rewrite -> Heq13 in H.
    rewrite H. reflexivity.
  - (* beq_nat k1 k3 = false *) reflexivity.
Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: override_permute *)
(** [] *)

(* FULL *)
(* EX3A (filter_exercise) *)
(** This one is a bit challenging.  Pay attention to the form of your IH. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* ADMITTED *)
  intros X test x l. induction l as [| v' l'].
    - (* l = [] *) intros lf eq. inversion eq.
    - (* l = v' :: l' *) intros lf eq.
      simpl in eq.
      destruct (test v') eqn: Heq.
        + (* test v' = true *) 
          inversion eq. rewrite <- H0. 
          rewrite <- Heq. reflexivity.
        + (* test v' = false *) 
          apply IHl' with lf. apply eq.  Qed.
(* /ADMITTED *)
(* GRADE_THEOREM 3: filter_exercise *)
(** [] *)

(* EX4!A (forall_exists_challenge) *)
(* HIDE: Why not turn these tests in comments into real tests? *)
(** Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:
[[
      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true
  
      forallb evenb [0;2;4;5] = false
  
      forallb (beq_nat 5) [] = true
]]
    The second checks whether there exists an element in the list that
    satisfies a given predicate:
[[
      existsb (beq_nat 5) [0;2;3;6] = false
 
      existsb (andb true) [true;true;false] = true
 
      existsb oddb [1;0;0;0;0;3] = true
 
      existsb evenb [] = false
]]
    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].
 
    Prove theorem [existsb_existsb'] that [existsb'] and [existsb] have
    the same behavior.
*)

(* SOLUTION *)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity.  Qed.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity.  Qed.

Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. reflexivity.  Qed.

Example test_forallb_4 : forallb (beq_nat 5) [] = true.
Proof. reflexivity.  Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => false
    | x :: l' => orb (test x) (existsb test l')
  end.

Example test_existsb_1 : existsb (beq_nat 5) [0;2;3;6] = false.
Proof. reflexivity.  Qed.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity.  Qed.

Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity.  Qed.

Example test_existsb_4 : existsb evenb [] = false.
Proof. reflexivity.  Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros. induction l as [| x l'].
  - (* l = [] *)
    unfold existsb'. simpl. reflexivity.
  - (* l = x :: l' *)
    unfold existsb'. simpl.
    destruct (test x).
    + (* test x = true *)
      simpl. reflexivity.
    + (* test x = false *)
      simpl.
      rewrite -> IHl'.
      unfold existsb'. reflexivity.  Qed.

(* GRADE_MANUAL 3: need to rework to make autograding possible *)

(* /SOLUTION *)
(** [] *)

(* SOONER: Another nice exercise would be to show how to
   define forallb in terms of fold, as in...
      Complete the following definition of [every] as a recursive function:
         Definition forallb' (X:Type) (p:X->bool) (l:list X) : bool :=
           fold _ _
             (fun x acc => both_yes _________  __________) ________  _________.
*)

(* HIDE *)
(* SOONER: ... *)
(* APT: If and when override and its many close relatives are
   rationalized across chapters, it might be good to stress that all
   the necessary properties of finite maps can be recovered just from
   the override_eq and override_neq lemmas... Here's an example: *)

(* That last theorem is a bit more challenging if you do it without
   unfolding the definition of [override], and instead use
   previously-proved lemmas about it.  *)
Theorem override_permute' : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros X x1 x2 k1 k2 k3 f. intros Hneq.
  destruct (beq_nat k1 k3) eqn: Heq13. 
    - (* beq_nat k1 k3 = true *) 
      apply beq_nat_true in Heq13.  rewrite <- Heq13.
      rewrite override_eq.  
      symmetry. apply override_neq. apply override_eq.  
      rewrite <- Hneq. reflexivity.
    - (* beq_nat k1 k3 = false *) 
      destruct (beq_nat k2 k3) eqn: Heq23. 
      + (* beq_nat k2 k3 = true *)
           apply beq_nat_true in Heq23. rewrite <- Heq23.
           rewrite override_eq.  apply override_neq.  
           apply override_eq. rewrite -> beq_nat_sym.  
           rewrite <- Hneq. reflexivity.
      + (* beq_nat k2 k3 = false *)
           apply override_neq.  
              symmetry.  apply override_neq.  
                apply override_neq. 
                   symmetry. apply override_neq. 
                     reflexivity. 
                     rewrite Heq23. reflexivity. 
                   rewrite Heq13. reflexivity. 
                rewrite Heq23. reflexivity. 
              rewrite Heq13. reflexivity.  Qed. 
(* /HIDE *)

(** $Date$ *)

(* /FULL *)


