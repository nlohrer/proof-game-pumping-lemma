import Game.Metadata

World "LeanBasics"
Level 13

Title "omega"

Introduction "
# omega
The tactic `omega` can solve integer and natural linear arithmetic problems."

Statement (x y : ℕ) (hx : x ≠ 0) : (x + y) * 2 - 8 = 2 * x + y * 2 - 2 * 2 - 4 := by
  Hint "Use `omega` to close the goal immediately"
  omega

Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic omega
OnlyTactic
  omega
  exact
