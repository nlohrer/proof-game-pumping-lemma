import Game.Levels.Lemmas.L08_cat_len
import Game.Metadata

World "Lemmas"
Level 9

Title "pow_len"

Introduction "The `pow` definition allows us to create strings of the form aⁿ, such as a⁴ = aaaa:

```
def Symbol.pow (a : Char) (n : ℕ) : Word :=
  match n with
  | 0 => .ε
  | .succ n => .cons a (Symbol.pow a n)
```

We want to show that aⁿ is n characters long."

namespace Regular
TheoremTab "pow"
/-- The length of cⁿ is n for any character c. -/
TheoremDoc Regular.pow_len as "pow_len" in "pow"

TheoremDoc Nat.one_add as "Nat.one_add" in "Minor Lemmas"
NewTheorem Nat.one_add

/--
```
def Symbol.pow (a : Char) (n : ℕ) : Word :=
  match n with
  | 0 => .ε
  | .succ n => .cons a (Symbol.pow a n)
```

The power of a symbol: aⁿ = a...a repeated n times. -/
DefinitionDoc Regular.Symbol.pow as "Symbol.Pow"
DefinitionDoc Regular.Word.pow as "Word.pow"
NewDefinition Regular.Symbol.pow Regular.Word.pow

Statement pow_len {s : Char} (n : ℕ) : |s ^ n| = n := by
  Hint "This is yet another induction, this time over `{n}`:
  `induction' {n} with n ih`."
  induction' n with n ih
  · Hint (hidden := true) "`rfl` closes the goal immediately."
    rfl
  · Hint "The lemma `Nat.one_add` will be useful here."
    Hint (hidden := true) "`simp only [Word.length, {ih}, Nat.one_add]`"
    simp [Word.length, ih, Nat.one_add]

Conclusion "Good!"
