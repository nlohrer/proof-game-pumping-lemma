import Game.Metadata

World "LeanBasics"
Level 8

Title "exact"

Introduction "
# Induction
To work through certain inductive structures, the `constructor` can be useful.
We will exclusively use it as a way to handle conjunctions appearing in the goal.
"

Statement (hx : x = 2) (hy : y = 3) : x = 2 ∧ y = 3 := by
  Hint "Use `constructor` to split the conjunction we want to prove into two separate goals."
  constructor
  · Hint (hidden := true) "`exact hx`"
    exact hx
  · Hint (hidden := true) "`exact hy`"
    exact hy

Conclusion "We will generally use `constructor` for conjunctions, but it works
for any inductive type."

NewTactic constructor
OnlyTactic
  constructor
  exact
