import Game.Metadata

World "LeanBasics"
Level 15

Title "rcases"

Introduction "
# rcases
For some structures, we might just need to match the forms that they can appear in rather than going for a full blown induction.
"

TheoremDoc False.elim as "False.elim" in "Minor Lemmas"
NewTheorem False.elim

Statement (n : ℕ) (hpos : n ≠ 0) : ∃ k, n = k + 1 := by
  Hint "`n` is a natural number, meaning that it is either 0, or the successor
  of some other natural number `m`. To match on those cases, start with
  `rcases {n} with _ | m`."
  rcases n with _ | m
  · Hint "We are in the case `n = 0`.
    `{hpos}` is an obvious contradiction.
    To utilize that fact, we can `apply False.elim` to change our goal to `False`."
    apply False.elim
    Hint "Since a negation of the form `¬A` is treated like an implication
    `A → False` in Lean, we can `apply {hpos}`."
    apply hpos
    Hint (hidden := true) "`rfl` closes the goal"
    rfl
  · Hint "We are in the case `n = succ {m}` for some natural number {m}.
    Obviously {m} is the number we are looking for, so `use {m}`."
    use m

Conclusion "Good!"

NewTactic rcases
OnlyTactic
  rfl
  apply
  use
  rcases
  exact
