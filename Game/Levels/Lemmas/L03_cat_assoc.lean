import Game.Levels.Lemmas.L02_cat_eps
import Game.Metadata

World "Lemmas"
Level 3

Title "cat_assoc"

Introduction "Let's prove another basic lemma: concatenation is associative."

namespace Regular

/-- Concatenation of words is associative, e.g. (x ∘ y) ∘ z = x ∘ (y ∘ z). -/
TheoremDoc Regular.cat_assoc as "cat_assoc" in "cat"


Statement cat_assoc (x y z : Word) : (x ∘ y) ∘ z = x ∘ y ∘ z := by
  induction' x with s w ih <;> simp_all only [Word.cat]

Conclusion "Good! Incidentally, we've just shown that strings together with concatenation form a monoid."
