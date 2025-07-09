import Game.Metadata

World "LeanBasics"
Level 8

Title "exact"

Introduction "
# Induction
To work through certain structures, the `constructor` can be useful.
"

Statement (hx : x = 2) (hy : y = 3) : x = 2 ∧ y = 3 := by
  Hint "Use `constructor` to split the conjunction we want to prove into two separate goals."
  constructor
  · exact hx
  · exact hy

Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic constructor
OnlyTactic
  constructor
  exact
