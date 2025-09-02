import Game.Levels.Lemmas.L01_Introduction
import Game.Metadata

World "Lemmas"
Level 2

Title "cat_eps"

Introduction "Let's prove a simple lemma: concatenating any word with the empty word should yield the word itself.

Like for most proofs in this world, we will need to utilize `induction'`.
Recalling our definition of a `Word`, a word `v` will either be the empty
word `Word.ε`, or have the `Word.cons s w` for some symbol `s`, and some word `w`.
To match on these possible forms with those exact variable names, we need to use
`induction' v with s w ih`,
with `ih` being the name of the induction hypothesis that we'll be able to access
in the induction step.
"

namespace Regular

Statement cat_eps (w : Word) : w.cat .ε = w := by
  Hint "This proof calls for an induction! Try starting with `induction' w with s w ih`."
  induction' w with s w ih
  · Hint "This is essentially true by definition of `Word.cat`."
    Hint (hidden := true) "`rw [Word.cat]`"
    rw [Word.cat]
  · Hint "We are in the induction step, so our original word now has the form
    `Word.cons {s} {w}`, which corresponds with the variable names we specified
    when we used the `induction'` tactic."
    Hint (hidden := true) "`rw [Word.cat, ih]`"
    rw [Word.cat, ih]

Conclusion "Good!"
