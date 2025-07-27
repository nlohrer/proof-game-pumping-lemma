import Game.Levels.Lemmas.L08_cat_len
import Game.Metadata

World "Lemmas"
Level 9

Title "pow_len"

Introduction "The `pow` definition allows us to create strings of the form aⁿ, such as a⁴ = aaaa. We want to show that aⁿ is n characters long."

namespace Regular
TheoremTab "pow"
/-- The length of cⁿ is n for any character c. -/
TheoremDoc Regular.pow_len as "pow_len" in "pow"

/-- The power of a symbol: aⁿ = a...a repeated n times. -/
DefinitionDoc Symbol.Pow as "Pow"
NewDefinition Symbol.Pow

Statement pow_len {s : Char} (n : ℕ) : |s ^ n| = n := by
  Hint "This is yet another induction, this time over `{n}`:
  `induction' {n} with n ih`."
  induction' n with n ih
  · Hint (hidden := true) "`rfl` closes the goal immediately."
    rfl
  · Hint "The lemma `Nat.one_add` will be useful here."
    Hint (hidden := true) "`simp only [Word.length, {ih}, Nat.one_add]`"
    simp only [Word.length, ih, Nat.one_add]

Conclusion "Good!"
