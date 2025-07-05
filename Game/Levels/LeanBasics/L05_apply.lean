import Game.Metadata

World "LeanBasics"
Level 5

Title "apply"

Introduction "
# apply
whenever a hypothesis matches the goal precisely, we can use `exact` to close out the goal."

Statement (A B : Prop) (hA : A) (hAB : A → B) : B := by
  Hint "Use `apply {hAB} at {hA}`."
  apply hAB at hA
  Hint "`exact {hA}` will close the goal now."
  exact hA

Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic apply
OnlyTactic
  apply
  exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
