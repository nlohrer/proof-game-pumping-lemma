import Game.Metadata

World "LeanBasics"
Level 6

Title "have"

Introduction "
# have
Sometimes, we want to construct sub-hypotheses of our own. We can do this with the
`have` tactic."

Statement (h : x = 2) : x = 2 := by
  Hint "Use `exact {h}` to close the goal immediately"
  exact h

Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

-- we need to use the same trick as in the natural number game
NewTactic
  «have»

OnlyTactic
  exact
  «have»
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
