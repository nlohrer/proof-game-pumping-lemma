import Game.Metadata

World "LeanBasics"
Level 2

Title "exact"

Introduction "
# exact
Whenever a hypothesis matches the goal precisely, we can use `exact` to close out the goal."

Statement (h : x = 2) : x = 2 := by
  Hint "Use `exact {h}` to close the goal immediately."
  exact h

Conclusion "`exact` will often be useful to close out a (sub-)goal."

NewTactic exact
OnlyTactic exact
