import Game.Levels.Lemmas.L04_cat_chars
import Game.Metadata

World "Lemmas"
Level 5

Title "cons_cat_cancel"

Introduction "Let's prove a simple lemma: concatenating any word with the empty word should yield the word itself."

namespace Regular

/-- Canceling -/
TheoremDoc Regular.cons_cat_cancel as "cons_cat_cancel" in "cat"

Statement cons_cat_cancel (c d : Char) (x y : Word) :
    Word.cons c x = .cons d y → c = d ∧ x = y := by
  Hint "Lean has automatically generated a lemma called `Word.cons.injEq`
  that contains the necessary information for this level, so `simp` will
  close the goal."
  simp

Conclusion "Good!"
