import Game.Levels.Lemmas.L04_gap
import Game.Metadata

World "Lemmas"
Level 5

Title "assoc_count"

Introduction "We've just introduced the `count` definition, which counts how many times a certain character occurs in a word. Let's show that we can get the count for a character in a word by summing up the counts in its subwords."

namespace Regular
/-- for the concatenation of two words, counting the occurrences of a certain character in the entire word
is the same as counting the occurrences in both subwords and adding them up.
 -/
TheoremDoc Regular.cat_count as "cat_count" in "cat"

/-- Counts how often a character occurs in a word. -/
DefinitionDoc Regular.Word.count as "count"

NewDefinition Regular.Word.count

Statement cat_count {s : Char} (x y : Word) :
    (x ∘ y).count s = x.count s + y.count s := by
  induction' x with s' w ih
  · simp_all only [Word.cat, Word.count, Nat.zero_add]
  · rw [Word.count]
    simp_all only [Word.cat, Word.count]
    split_ifs with h
    · omega
    · simp_all only

Conclusion "Good!"
