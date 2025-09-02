import Game.Levels.Lemmas.L09_pow_len
import Game.Metadata

World "Lemmas"
Level 10

Title "pow_count"

Introduction "We will now show that for a word of the form cⁿ, it will contain n instances of c, and none of any other character."

namespace Regular
/-- A word of the form cⁿ will contain n instances of the character c, and none of any other character. -/
TheoremDoc Regular.pow_count as "pow_count" in "pow"

Statement pow_count {s₁ s₂ : Char} (n : ℕ) :
    (s₁ ^ n).count s₂ = if s₁ = s₂ then n else 0 := by
  Hint (hidden := true) "This is another induction: `induction' {n} with n ih`."
  induction' n with n ih
  · Hint (hidden := true) "`simp [Word.count]`"
    simp [Word.count]
  · Hint (hidden := true) "`simp [Word.count]` to introduce the `if` statement in the goal."
    simp [Word.count]
    Hint (hidden := true) "`split_ifs with h`"
    split_ifs with h
    · Hint (hidden := true) "`simp_all` followed by `omega` will close the goal."
      simp_all
      omega
    · Hint (hidden := true) "`simp_all` closes the goal."
      simp_all
Conclusion "Good!"
