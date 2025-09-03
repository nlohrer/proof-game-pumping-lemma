import Game.Metadata

World "LeanBasics"
Level 14

Title "induction'"

Introduction "
# Induction
We utilize several inductive structures that we can handle with the `induction'` tactic."

Statement (n : ℕ) : n < 2 ^ n := by
  Hint "Use `induction' {n} with n ih` to start a proof by induction"
  induction' n with n ih
  · Hint "`simp` will close the goal."
    simp
  · Hint "We now have our induction hypothesis `ih` at our disposal.
    We can just rely on `omega` to close out our goal rather than going for any
    convoluted rewriting."
    omega

Conclusion "Both the type `Word` as well as our definitions for it will be
inductive, so we will make frequent use of `induction'`!"

-- copied from the induction docstring
/--
Assuming `x` is a variable in the local context with an inductive type, `induction' x` applies induction on `x` to the main goal, producing one goal for each constructor of the inductive type, in which the target is replaced by a general instance of that constructor and an inductive hypothesis is added for each recursive argument to the constructor. If the type of an element in the local context depends on `x`, that element is reverted and reintroduced afterward, so that the inductive hypothesis incorporates that hypothesis as well.
-/
TacticDoc induction'

NewTactic induction'
OnlyTactic
  induction'
  exact
  simp
  omega
