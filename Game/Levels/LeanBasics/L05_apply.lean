import Game.Metadata

World "LeanBasics"
Level 5

Title "apply"

Introduction "
# apply
whenever a hypothesis matches the goal precisely, we can use `exact` to close out the goal."

Statement (A B : Prop) (hA : A) (hAB : A → B) : B := by
  Hint "Use `apply {hAB} at {hA}`. Alternatively, use `apply {hAB}`
  so that the antecedent of the implication `{hAB}` becomes our new goal."
  Branch
    apply hAB at hA
    Hint "`exact {hA}` will close the goal now."
    exact hA
  apply hAB
  Hint "`exact {hA}` will close the goal now."
  exact hA

Conclusion "While we mostly use `rw` to make use of our available theorems and
hypotheses, `apply` will sometimes be useful in cases where a simple `rw` does
not fit what we want to achieve."

NewTactic apply
OnlyTactic
  apply
  exact
