import Game.Levels.Lemmas.L07_cat_count_zero
import Game.Metadata

World "Lemmas"
Level 8

Title "cat_len"

Introduction "Our new definition `length` defines the length of a word:

```
def Word.length : (w : Word) → ℕ
 | .ε => 0
 | .cons _ w => 1 + w.length
```

The empty word `ε` has a length of 0, while for the inductive case `Word.cons s w`
we do not care about the symbol `s`, always incrementing the length of `w` by 1.
We also introduce the notation `|w|` for `Word.length w`.

Let's show that the length of a word is equal to the sum of its subwords."

namespace Regular
/--
To determine the length of the concatenation of two words, you can add the length of both words. -/
TheoremDoc Regular.cat_len as "cat_len" in "cat"

/--
```
def Word.length : (w : Word) → ℕ
 | .ε => 0
 | .cons _ w => 1 + w.length
```

The length of a word, i.e. the amount of symbols in it.
-/
DefinitionDoc Regular.Word.length as "Word.length"
NewDefinition Regular.Word.length

/--
Adding zero to a natural number results in the original number.
-/
TheoremDoc Nat.zero_add as "Nat.zero_add" in "Minor Lemmas"

/--
Addition of natural numbers is associative.
-/
TheoremDoc Nat.add_assoc as "Nat.add_assoc" in "Minor Lemmas"
NewTheorem Nat.zero_add Nat.add_assoc

Statement cat_len (x y : Word) :
    |(x ∘ y)| = |x| + |y| := by
  Hint (hidden := true) "This calls for yet another induction: `induction' x with _ x ih`"
  induction' x with _ x ih
  · Hint "`Nat.zero_add`, which has been added to your inventory, should be useful
    at some point."
    Hint (hidden := true) "`simp only [Word.cat, Word.length, Nat.zero_add]`"
    simp only [Word.cat, Word.length, Nat.zero_add]
  · Hint "Use `Nat.add_assoc`."
    Hint (hidden := true) "`simp_all [Word.length, Word.cat, {ih}, Nat.add_assoc]`"
    simp_all [Word.length, Word.cat, ih, Nat.add_assoc]

Conclusion "Good!"
