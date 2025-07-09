import Game.Metadata

World "LeanBasics"
Level 10

Title "exact"

Introduction "
# match
For some structures, we might just need to match the forms that they can appear in."

Statement (h : x = 2) : x = 2 := by
  Hint "Use `exact {h}` to close the goal immediately"
  exact h

Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic «match»
OnlyTactic
  «match»
  exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
