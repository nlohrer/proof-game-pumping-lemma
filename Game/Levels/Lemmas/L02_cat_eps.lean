import Game.Metadata

World "Lemmas"
Level 2

Title "cat_eps"

Introduction "Let's prove a simple lemma: concatenating any word with the empty word should yield the word itself."

namespace Regular
TheoremTab "cat"

/-- Concatenating a word with ε yields the original word. -/
TheoremDoc Regular.cat_eps as "cat_eps" in "cat"

/-- Concatenation of words: for two words w₁ and w₂, the concatenation w₁ and w₂ yields w₁w₂. -/
DefinitionDoc Regular.Word.cat as "Word.cat"

/-- A word over an alphabet, i.e. a string of symbols from that alphabet. -/
DefinitionDoc Word as "Word"

NewDefinition Word Regular.Word.cat

Statement cat_eps (w : Word) : w.cat .ε = w := by
  Hint "This proof calls for an induction! Try starting with `induction' w with s w ih`."
  induction' w with s w ih
  · Hint "This is essentially true by definition of `Word.cat`."
    Hint (hidden := true) "`rw [Word.cat]`."
    rw [Word.cat]
  · Hint (hidden := true) "`rw [Word.cat, ih]`."
    rw [Word.cat, ih]

Conclusion "Good!"
