import Game.Metadata

World "LeanBasics"
Level 4

Title "intro"

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
  Hint (hidden := true) "`exact {ha}` closes the goal."
  exact ha

Conclusion "Using `intro x y...` will be equivalent to steps such as \"
Let x be arbitrary...\", or \"Assume y...\" in a paper proof."

NewTactic intro
OnlyTactic
  intro
  exact
