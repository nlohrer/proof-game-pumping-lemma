import Game.Metadata

World "LeanBasics"
Level 15

Title "use"

Introduction "
# use
We can resolve existential quantifiers with the help of the `use` keyword."

Statement (m : ℕ) (hm : m = 4) : ∃ n : ℕ, n = m := by
  Hint "We want to set n := 4: `use 4`."
  use 4
  Hint (hidden := true) "`rw [{hm}]` or `omega` will solve this goal."
  rw [hm]
Conclusion "Good!"

NewTactic use
OnlyTactic
  use
