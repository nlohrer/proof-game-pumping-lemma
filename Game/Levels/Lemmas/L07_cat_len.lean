import Game.Levels.Lemmas.L06_cat_count_zero
import Game.Metadata

World "Lemmas"
Level 7

Title "cat_len"

Introduction "Our new definition `length` defines the length of a word. Let's show that the length of a word is equal to the sum of its subwords."

namespace Regular
/-- To determine the length of the concatenation of two words, you can add the length of both words. -/
TheoremDoc Regular.cat_len as "cat_len" in "cat"

/-- The amount of symbols in a word. -/
DefinitionDoc Regular.Word.length as "length"
NewDefinition Regular.Word.length

lemma cat_len (x y : Word) :
    |(x ∘ y)| = |x| + |y| := by
  induction' x with s x ih
  · simp only [Word.cat, Word.length, Nat.zero_add]
  · rw [Word.length, Nat.add_assoc, ← ih]
    simp_all only [Word.length]

Conclusion "Good!"
