import Game.Levels.Lemmas.L03_cat_assoc
import Game.Metadata

World "Lemmas"
Level 4

Title "cat_chars"

Introduction "The newly introduced definition `Word.chars w` produces a set
containing all of the characters occuring in the word `w`.
Let's show that for a concatenated word `xy`, its character set is equal
to the union of the character sets of each subword.
"

namespace Regular

/-- The set of characters in a word is the union of all sets of characters
in its subwords. -/
TheoremDoc Regular.cat_chars as "cat_chars" in "cat"

Statement cat_chars (x y : Word) : (x ∘ y).chars = x.chars ∪ y.chars := by
  Hint "Start with induction' x with s w ih"
  induction' x with s w ih
  · Hint "You can either rewrite with fitting definitions and then `simp`,
    or directly give those definitions as arguments to `simp`."
    Hint (hidden := true) "`simp [Word.cat, Word.chars]` closes the goal."
    simp [Word.cat, Word.chars]
  · Hint "You can go for similar rewrites here, though you will need the
    induction hypothesis {ih} as well. You might eventually find the theorem
    `Set.union_assoc` useful."
    Hint (hidden := true) "Start with `rw [Word.chars, Word.cat, Word.chars, ih]`."
    rw [Word.chars, Word.cat, Word.chars, ih]
    Hint (hidden := true) "`rw [Set.union_assoc]` closes the goal now."
    rw [Set.union_assoc]

Conclusion "Good!"
