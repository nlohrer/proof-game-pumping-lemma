import Game.Levels.Lemmas.L07_cat_len
import Game.Metadata

World "Lemmas"
Level 8

Title "pow_len"

Introduction "The `pow` definition allows us to create strings of the form aⁿ, such as a⁴ = aaaa. We want to show that aⁿ is n characters long."

namespace Regular
TheoremTab "pow"
/-- The length of cⁿ is n for any character c. -/
TheoremDoc Regular.pow_len as "pow_len" in "pow"

/-- The power of a symbol: aⁿ = a...a repeated n times. -/
DefinitionDoc Symbol.Pow as "Pow"
NewDefinition Symbol.Pow

Statement pow_len {s : Char} (n : ℕ) : |s ^+^ n| = n := by
  induction' n with n ih
  · rfl
  · simp only [Word.length]
    rw [ih]
    exact Nat.one_add _

Conclusion "Good!"
