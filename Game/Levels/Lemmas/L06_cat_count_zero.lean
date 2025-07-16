import Game.Metadata
import Game.Levels.Lemmas.L05_cat_count

World "Lemmas"
Level 6

Title "cat_count_zero"

Introduction "Let's prove a simple lemma: concatenating any word with the empty word should yield the word itself."

namespace Regular
/-- If a symbol doesn't occur in the concatenation of two words, then it won't occur in any of the two words either. -/
TheoremDoc Regular.cat_count_zero as "cat_count_zero" in "cat"

Statement cat_count_zero {s : Char} (x y : Word) :
    (x ∘ y).count s = 0 → x.count s = 0 ∧ y.count s = 0 := by
  intro hcatcount
  apply And.intro <;> simp_all only [cat_count, Nat.add_eq_zero_iff]

Conclusion "Good!"
