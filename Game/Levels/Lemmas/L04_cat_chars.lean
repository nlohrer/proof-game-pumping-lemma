import Game.Levels.Lemmas.L03_cat_assoc
import Game.Metadata

World "Lemmas"
Level 4

Title "cat_chars"

Introduction "The newly introduced definition `Word.chars w` produces a set
containing all of the characters occuring in the word `w`:

```
def Word.chars : (w : Word) → Set Char
  | ε => ∅
  | cons s w => {s} ∪ w.chars
```

As we can see from the definition, the empty word `ε` contains no symbols at all.
Meanwhile, for a word of the form `Word.cons s w`, we determine the characters contained in `w`,
and add `s` that set.


Let's show that for a concatenated word `xy`, its character set is equal
to the union of the character sets of each subword.
"

namespace Regular
/--
```
def Word.chars : (w : Word) → Set Char
  | ε => ∅
  | cons s w => {s} ∪ w.chars
```

The set of all characters occuring in a particular word.
-/
DefinitionDoc Regular.Word.chars as "Word.chars"

TheoremTab "Minor Lemmas"
/--
Forming the union over three sets is associative.
-/
TheoremDoc Set.union_assoc as "Set.union_assoc" in "Minor Lemmas"
NewTheorem Set.union_assoc

NewDefinition Regular.Word.chars

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
    induction hypothesis {ih} as well. You might find the theorem
    `Set.union_assoc` useful at some point, which has been added to the `Minor Lemmas`
    tab in your inventory on the right."
    Hint (hidden := true) "Start with `rw [Word.chars, Word.cat, Word.chars, ih]`."
    rw [Word.chars, Word.cat, Word.chars, ih]
    Hint (hidden := true) "`rw [Set.union_assoc]` closes the goal now."
    rw [Set.union_assoc]

Conclusion "Good!"
