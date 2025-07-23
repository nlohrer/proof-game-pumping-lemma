import Game.Metadata

World "LeanBasics"
Level 12

Title "exact"

Introduction "
# simp_all only
whenever a hypothesis matches the goal precisely, we can use `exact` to close out the goal."

Statement (h : x = 2) : x = 2 := by
  Hint "Use `exact {h}` to close the goal immediately"
  simp_all

Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic simp_all only
OnlyTactic
  simp_all only
