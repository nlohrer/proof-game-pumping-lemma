import Game.Levels.Lemmas.L08_pow_len
import Game.Metadata

World "Lemmas"
Level 9

Title "pow_count"

Introduction "Let's prove a simple lemma: concatenating any word with the empty word should yield the word itself."

namespace Regular
/-- A word of the form cⁿ will contain n instances of the character c, and none of any other character. -/
TheoremDoc Regular.pow_count as "pow_count" in "pow"

Statement pow_count {s₁ s₂ : Char} (n : ℕ) :
    (s₁ ^+^ n).count s₂ = if s₁ = s₂ then n else 0 := by
  induction' n with n ih
  · simp_all only [Word.count, ite_self]
  · simp_all only [Word.count, ↓reduceIte]
    split_ifs with h
    · subst h
      simp_all only [↓reduceIte]
      omega
    · simp_all only [↓reduceIte]

Conclusion "Good!"
