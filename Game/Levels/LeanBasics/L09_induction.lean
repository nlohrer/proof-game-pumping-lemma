import Game.Metadata

World "LeanBasics"
Level 9

Title "induction'"

Introduction "
# Induction
We utilize several inductive structures that we can handle with the `induction'` tactic."

Statement (n : ℕ) : 2 * n = n + n := by
  Hint "Use `induction' {n} with n ih` to start a proof by induction"
  induction' n with n ih
  · omega
  · omega

Conclusion "Both the type `Word` as well as our definitions for it will be
inductive, so we will make frequent use of induction'!"

NewTactic induction'
OnlyTactic
  induction'
  exact
