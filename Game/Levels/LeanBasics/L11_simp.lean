import Game.Metadata

World "LeanBasics"
Level 11

Title "simp"

Introduction "
# simp
Using the more elementary tactics `rw`, `apply`, and `exact` to work through proofs
will quickly become tedious for more involved proofs.
Lean offers a number of automation tactics that will take care of different steps
on their own.

In this level, we introduce the `simp` tactic, which simplifies the goal
or a hypothesis, and can take on a number of lemmas as arguments that
it will then try to employ.
"

Statement (h : x = 2) : x = 2 := by
  Hint "Use `simp [{h}]` to close the goal immediately"
  simp [h]

Conclusion "The exact behavior of `simp` can be a little unpredictable if you're
not used to working with it, but it is very useful to skip over a great number of
simple, but manual steps."

NewTactic
  simp
OnlyTactic
  simp
