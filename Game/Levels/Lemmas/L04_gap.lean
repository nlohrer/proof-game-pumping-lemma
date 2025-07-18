import Game.Levels.Lemmas.L03_cat_assoc
import Game.Metadata

World "Lemmas"
Level 4

Title "cat_assoc"

Introduction "Let's prove a simple lemma: concatenating any word with the empty word should yield the word itself."

namespace Regular

Statement (x y z : Word) : (x ∘ y) ∘ z = x ∘ y ∘ z := by
  induction' x with s w ih <;> simp_all only [Word.cat]

Conclusion "Good!"
