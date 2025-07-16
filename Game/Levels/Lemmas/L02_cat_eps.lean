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
DefinitionDoc Regular.Word.cat as "cat"

/-- A word over an alphabet, i.e. a string of symbols from that alphabet. -/
DefinitionDoc Word as "Word"

NewDefinition Word Regular.Word.cat

--TheoremDoc Regular.Word.cat as "Word.cat" in "Word"

--NewTheorem Regular.Word.cat

Statement cat_eps (w : Word) : w.cat .ε = w := by
  induction' w with s w ih
  · rw [Word.cat]
  · rw [Word.cat, ih]

Conclusion "Good!"
