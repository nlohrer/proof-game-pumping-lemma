import Game.Metadata

World "LeanBasics"
Level 10

Title "rcases"

Introduction "
# rcases
For some structures, we might just need to match the forms that they can appear in rather than going for a full blown induction.

In this level, we will be using the tactics `left` and `right` to deal
with the disjunction in our goal. Since further disjunction will not
appear hereafter, we will tell you when to use these tactics here directly
without fully introducing them."

Statement (n : ℕ) : n = 0 ∨ ∃ m, n = m + 1 := by
  Hint "Start with `rcases {n} with _ | n`."
  rcases n with _ | n
  · Hint "This is the left case, so use `left`."
    left
    Hint "`rfl` closes the goal."
    rfl
  · Hint "Now we are in the right case, so use `right`."
    right
    Hint "obviously {n} is the number we are looking for, so `use {n}`."
    use n

Conclusion "Good!"

NewTactic rcases
HiddenNewTactic
  left
  right
  use
OnlyTactic
  rfl
  rcases
  exact
  left
  right
