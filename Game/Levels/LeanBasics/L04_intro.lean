import Game.Metadata

World "LeanBasics"
Level 4

Title "exact"

Introduction "
# intro
We use the `intro` tactic to handle both `∀`-statements, and to introduce the antecedent
of an implication.
"

Statement : ∀ (A : Prop), A → A := by
  Hint "start with `intro A`"
  intro A
  Hint "Now, `intro ha` will introduce the antecedent into our given hypotheses."
  intro ha
  exact ha

Conclusion "Good!"

NewTactic intro
OnlyTactic
  intro
  exact
