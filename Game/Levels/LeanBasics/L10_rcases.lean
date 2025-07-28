import Game.Metadata

World "LeanBasics"
Level 10

Title "rcases"

Introduction "
# rcases
For some structures, we might just need to match the forms that they can appear in rather than going for a full blown induction."

Statement (h : x = 2) : x = 2 := by
  Hint "Use `exact {h}` to close the goal immediately"
  exact h

Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic rcases
OnlyTactic
  rcases
  exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
