import Game.Metadata

World "LeanBasics"
Level 3

Title "rw"

Introduction "
# rw
The `rw` tactic allows for rewriting using certain theorems or hypotheses,
both at the goal as well as at specific hypotheses.
"

Statement (a b c : ℕ) (h : b = a + 1 - 1) (k : b = c + 1 - 1)
    (g: ∀ (n : ℕ), n + 1 - 1 = n) : a = c := by
  Hint "As we can see, both `{h}` and `{k}` are currently stated a bit awkwardly. Start with `rw [{g}] at {h} {k}`."
  rw [g] at h k
  Hint "The goal now follows from `{h}` and `{k}` quite directly.
  You can't use `exact` or `rfl` in this level, but `rw` will try to close out
  the goal anyway using reflexivity.
  `rw [← {h}, {k}]` closes the goal immediately. Mind that we write
  `← {h}` since `rw` usually substitutes a term matching the left side of the equation with the one on the right side. The equality `{h}` is in the opposite direction of the rewrite we wish to apply, so we use `←` (which can
  be typed with `\\l`) to reverse it."
  Branch
    rw [← h]
    Hint "From here `rw [{k}]` closes the goal."
    rw [k]
  rw [← h, k]

Conclusion "There are some more syntactic specifics when it comes to using `rw`,
but we will not need them in the future."

NewTactic rw
OnlyTactic
  rw
