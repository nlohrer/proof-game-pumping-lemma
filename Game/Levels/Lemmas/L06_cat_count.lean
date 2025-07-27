import Game.Levels.Lemmas.L05_cons_cat_cancel
import Game.Metadata

World "Lemmas"
Level 6

Title "assoc_count"

Introduction "We've just introduced the `count` definition, which counts how many times a certain character occurs in a word. Let's show that we can get the count for a character in a word by summing up the counts in its subwords."

namespace Regular
/-- for the concatenation of two words, counting the occurrences of a certain character in the entire word
is the same as counting the occurrences in both subwords and adding them up.
 -/
TheoremDoc Regular.cat_count as "cat_count" in "cat"

/-- Counts how often a character occurs in a word. -/
DefinitionDoc Regular.Word.count as "Word.count"

NewDefinition Regular.Word.count

Statement cat_count {s : Char} (x y : Word) :
    (x ∘ y).count s = x.count s + y.count s := by
  Hint (hidden := true) "Start with `induction' x with s' w ih`."
  induction' x with s' w ih
  · Hint (hidden := true) "Utilize `Word.cat` and `Word.count`."
    Hint (hidden := true) "`simp [Word.cat, Word.count]`"
    simp [Word.cat, Word.count]
  · Hint "Remember you can use the tactic `split_ifs` to handle if statements."
    Hint (hidden := true) "`simp [Word.cat, Word.count]`"
    simp [Word.cat, Word.count]
    Hint (hidden := true) "`split_ifs with h`"
    split_ifs with h
    · Hint (hidden := true) "`omega` will solve this goal directly!"
      omega
    · Hint (hidden := true) "`exact {ih}` closes the goal immediately."
      exact ih

Conclusion "Good!"
