import Game.Levels.Lemmas.L01_Introduction
import Game.Metadata

World "Lemmas"
Level 2

Title "cat_eps"

Introduction "Let's prove a simple lemma: concatenating any word with the empty word should yield the word itself."

namespace Regular

Statement cat_eps (w : Word) : w.cat .ε = w := by
  Hint "This proof calls for an induction! Try starting with `induction' w with s w ih`."
  induction' w with s w ih
  · Hint "This is essentially true by definition of `Word.cat`."
    Hint (hidden := true) "`rw [Word.cat]`."
    rw [Word.cat]
  · Hint (hidden := true) "`rw [Word.cat, ih]`."
    rw [Word.cat, ih]

Conclusion "Good!"
