import Game.Metadata

World "LeanBasics"
Level 11

Title "exact"

Introduction "
# simp only
whenever a hypothesis matches the goal precisely, we can use `exact` to close out the goal."

Statement (h : x = 2) : x = 2 := by
  Hint "Use `exact {h}` to close the goal immediately"
  exact h

Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic
  simp only
OnlyTactic
  simp only
  exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
