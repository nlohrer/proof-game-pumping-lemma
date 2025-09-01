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
inductive, so we will make frequent use of induction'!"

NewTactic induction'
OnlyTactic
  induction'
  exact
  simp
  omega
