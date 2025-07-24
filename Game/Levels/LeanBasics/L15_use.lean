import Game.Metadata

World "LeanBasics"
Level 15

Title "use"

Introduction "
# use
We can resolve existential quantors with the help of the `use` keyword."

Statement : ∃ n : ℕ, n = 4 := by
  Hint "We want to set n := 4: `use 4`."
  use 4
Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic use
OnlyTactic
  use
