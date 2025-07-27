import Game.Levels.Lemmas.L06_cat_count
import Game.Metadata

World "Lemmas"
Level 7

Title "cat_count_zero"

Introduction "We'll need a special case of the lemma we just showed later on: when a certain character does not occur in a word, it won't appear in any of its subwords either."

namespace Regular
/-- If a symbol doesn't occur in the concatenation of two words, then it won't occur in any of the two words either. -/
TheoremDoc Regular.cat_count_zero as "cat_count_zero" in "cat"

Statement cat_count_zero {s : Char} (x y : Word) :
    (x ∘ y).count s = 0 → x.count s = 0 ∧ y.count s = 0 := by
  Hint "Let's start out by introducing the antecedent: `intro hcatcount`"
  intro hcatcount
  Hint "To split the conjunction, let's use the `constructor` tactic."
  constructor
  · Hint "Use the theorem `Nat.add_eq_zero`"
    Hint (hidden := true) "simp_all [cat_count, Nat.add_eq_zero]"
    simp_all [cat_count, Nat.add_eq_zero]
  · Hint "Use the theorem `Nat.add_eq_zero_iff`"
    Hint (hidden := true) "simp_all [cat_count, Nat.add_eq_zero_iff]"
    simp_all [cat_count, Nat.add_eq_zero_iff]

Conclusion "Good!"
