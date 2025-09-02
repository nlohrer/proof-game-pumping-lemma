import Game.Metadata

World "LeanBasics"
Level 12

Title "split_ifs"

Introduction "
# split_ifs
The tactic `split_ifs` allows us to handle `if` statements in our goal."

Statement (n : ℕ) : if n < 4 then n + 1 < 5 else n + 2 ≤ 2 * n := by
  Hint "Use `split_ifs with h`."
  split_ifs with h
  · Hint "The goal follows from `{h}` via simple arithmetic, so `omega` closes the goal."
    omega
  · Hint "Once again the goal follows from `{h}`, so use `omega` again."
    omega
Conclusion "Good!"

NewTactic split_ifs
OnlyTactic
  split_ifs
  omega
