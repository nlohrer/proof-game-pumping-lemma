import Game.Metadata

World "LeanBasics"
Level 9

Title "induction"

Introduction "
# Induction
We utilize several inductive structures that we can handle with the `induction'` tactic."

Statement (n : ℕ) : 0 ≤ n := by
  Hint "Use `induction' {n} with n ih` to start a proof by induction"
  induction' n with n ih
  · rfl
  ·
    sorry

Conclusion "Both the type `Word` as well as our definitions for it will be
inductive, so we will make frequent use of induction'!"

/- Use these commands to add items to the game's inventory. -/

NewTactic induction'
OnlyTactic
  induction'
  exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
