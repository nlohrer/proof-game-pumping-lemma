import Game.Metadata

World "LeanBasics"
Level 12

Title "simp_all"

Introduction "
# simp_all
whenever a hypothesis matches the goal precisely, we can use `exact` to close out the goal."

Statement (h : x = 2) : x = 2 := by
  Hint "Use `exact {h}` to close the goal immediately"
  simp_all

Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic simp_all
OnlyTactic
  simp_all
