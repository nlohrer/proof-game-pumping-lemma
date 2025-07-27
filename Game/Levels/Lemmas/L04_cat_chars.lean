import Game.Levels.Lemmas.L03_cat_assoc
import Game.Metadata

World "Lemmas"
Level 4

Title "cat_assoc"

Introduction "Let's prove a simple lemma: concatenating any word with the empty word should yield the word itself."

namespace Regular

Statement cat_chars (x y : Word) : (x ∘ y).chars = x.chars ∪ y.chars := by
  induction' x with s w ih
  · simp only [Word.cat, Word.chars, Set.empty_union]
  · rw [Word.chars, Word.cat, Word.chars, ih]
    rw [Set.union_assoc]

Statement (x y z : Word) : (x ∘ y) ∘ z = x ∘ y ∘ z := by
  induction' x with s w ih <;> simp_all only [Word.cat]

Conclusion "Good!"
