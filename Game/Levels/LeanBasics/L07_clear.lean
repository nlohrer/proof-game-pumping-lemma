import Game.Metadata

World "LeanBasics"
Level 7

Title "exact"

Introduction "
# clear
Sometimes, especially when proving a lemma via `have`, the proof state might include a
lot of hypotheses that are not necessary to achieve the current goal. To keep them from
distracting us, we can use the `clear` tactic to remove them."

Statement (a b c d e f : ℕ) (h : x = 2) (hy : y = 3) (hz : z = 0)  : x = 2 := by
  Hint "Use `clear {a} {b} {c} {d} {e} {f} {hy} {hz} {y} {z}` to remove the unneeded hypotheses"
  clear a b c d e f hy hz y z
  exact h

Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic
  clear
OnlyTactic
  clear
  exact
