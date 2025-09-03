import Game.Levels.Lemmas.L04_cat_chars
import Game.Metadata

World "Lemmas"
Level 5

Title "cons_cat_cancel"

Introduction "For characters `c, d` and words `x, y`, the equality `cx = dy` should result
in the equalities `c = d` and `x = y`.
Arriving at either equality is essentially equivalent to canceling the other side of the
original equation.
"

namespace Regular

/-- Canceling from either the right or left side when two words are equal. -/
TheoremDoc Regular.cons_cat_cancel as "cons_cat_cancel" in "cat"

Statement cons_cat_cancel (c d : Char) (x y : Word) :
    Word.cons c x = .cons d y → c = d ∧ x = y := by
  Hint "Lean has automatically generated a lemma called `Word.cons.injEq`
  that contains the necessary information for this level, so `simp` will
  close the goal."
  simp

Conclusion "Good! We do not strictly need this lemma, but it is good to be aware
of that property."
