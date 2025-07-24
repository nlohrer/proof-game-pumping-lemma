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

Statement cat_len (x y : Word) :
    |(x ∘ y)| = |x| + |y| := by
  Hint (hidden := true) "This calls for yet another induction: `induction' x with _ x ih`"
  induction' x with _ x ih
  · Hint "`Nat.zero_add` should be useful at some point."
    Hint (hidden := true) "`simp only [Word.cat, Word.length, Nat.zero_add]`"
    simp only [Word.cat, Word.length, Nat.zero_add]
  · Hint "Use `Nat.add_assoc`."
    Hint (hidden := true) "`simp_all [Word.length, Word.cat, {ih}, Nat.add_assoc]`"
    simp_all [Word.length, Word.cat, ih, Nat.add_assoc]

Conclusion "Good!"
