import Game.Levels.Lemmas.L05_cons_cat_cancel
import Game.Metadata

World "Lemmas"
Level 6

Title "cat_count"

Introduction "We've just introduced the `count` definition, which counts how many times a certain character occurs in a word.
`Word.count w s` is equivalent to the notation `#s(w)` that we will later see in
the non-regularity proof on paper.

```
def Word.count (w : Word) (s' : Char) : ℕ := match w with
  | .ε => 0
  | .cons s w => if (s = s') then 1 + w.count s' else w.count s'
```

As we can see, the empty word `ε` always contains zero instances of `s'`.
For a word of the form `Word.cons s w`, we count how many times `s'` occurs in `w`,
and then further increment that count by 1 if `s` also matches with `s'`.

Let's show that we can get the count for a character in a word by summing up the counts in its subwords."

namespace Regular
/-- for the concatenation of two words, counting the occurrences of a certain character in the entire word
is the same as counting the occurrences in both subwords and adding them up.
 -/
TheoremDoc Regular.cat_count as "cat_count" in "cat"

/--
```
def Word.count (w : Word) (s' : Char) : ℕ := match w with
  | .ε => 0
  | .cons s w => if (s = s') then 1 + w.count s' else w.count s'
```

`w.count s` shows `#s(w)`, i.e. the amount of times that the character
`s` occurs in the word `w`.
-/
DefinitionDoc Regular.Word.count as "Word.count"

NewDefinition Regular.Word.count

Statement cat_count {s : Char} (x y : Word) :
    (x ∘ y).count s = x.count s + y.count s := by
  Hint (strict := true) (hidden := true) "Start with `induction' x with s' w ih`."
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

Conclusion "Good! We will rely on this lemma quite frequently in the non-regularity proof."
