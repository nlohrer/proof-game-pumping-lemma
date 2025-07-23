import Game.Levels.Lemmas.L09_pow_count
import Game.Metadata

open Nat

World "Lemmas"
Level 10

Title "cons_a"

Introduction "For the last level of this game, let's prove a much more complex statement!
While it will be much more involved to prove than the other statements in this world,
it will also be very useful in our non-regularity proof."

namespace Regular
/-- A word of the form cⁿ will contain n instances of the character c, and none of any other character. -/
TheoremDoc Regular.cons_a as "cons_a" in "cat"

lemma cons_a (n : ℕ) (x y z : Word) (hz : x ∘ y = ('a' ^ n) ∘ z) (hx : |x| ≤ n) :
    x.count 'b' = 0 := by
  induction' x with s w ih generalizing n
  · simp_all only [Word.length, Nat.zero_le, Word.count]
  · specialize ih (n - 1)
    simp_all [Word.cat, Word.length, Word.count, Char.isValue]
    have ha : s = 'a' := by
      clear ih
      match n with
      | 0 => simp_all only [Word.cat, le_zero_eq, Nat.add_eq_zero, succ_ne_self, false_and]
      | n + 1 =>
        simp_all only [Word.cat, add_eq, Nat.add_zero, Word.cons.injEq]
    simp_all only [↓Char.isValue, Char.reduceEq, ↓reduceIte]
    subst ha
    match n with
    | 0 =>
      subst hz
      simp_all only [le_zero_eq, Nat.add_eq_zero, succ_ne_self, false_and]
    | n + 1 =>
      simp only [Nat.add_one_sub_one, Char.isValue] at ih
      rw [Symbol.pow] at hz
      simp_all only [not_false_eq_true, Word.cat, Word.cons.injEq, true_and, forall_true_left, Char.isValue]
      exact ih (by omega)

lemma cat_char_subset_left (x y : Word) :
    x.chars ⊆ (x ∘ y).chars := by
  simp only [Word.cat_chars, Set.subset_union_left]

lemma cat_char_subset_right (x y : Word) :
    y.chars ⊆ (x ∘ y).chars := by
  simp only [Word.cat_chars, Set.subset_union_right]
Conclusion "Good!"
