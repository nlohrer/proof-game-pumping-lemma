import Game.Levels.Lemmas.L10_pow_count
import Game.Metadata

open Nat

World "Lemmas"
Level 11

Title "pow_cons_count_eq"

Introduction "Let's prove a statement for a slightly more complex situation that
may show up in a nonregularity proof:
For `n > 0`, characters `c, d`, and words `x, y`, if
`cx = dⁿy`, then `c` must be `d`!."

namespace Regular
/-- A word of the form cⁿ will contain n instances of the character c, and none of any other character. -/
TheoremDoc Regular.pow_cons_count_eq as "pow_cons_count_eq" in "pow"

Statement pow_cons_count_eq (c d : Char) (n : ℕ) (x y : Word) (hcons : .cons c x = (d ^ n) ∘ y)
    (hn : 0 < n) :
    c = d := by
  Hint "We need to match on `{n}` here, so use `rcases {n} with _ | n`.
  Since we're just matching, we do not need to name the induction hypothesis."
  rcases n with _ | n
  · Hint "`{hn}` is obviously a contradiction, so `simp at {hn}` will close
    the goal immediately."
    simp at hn
  · Hint "This goal follows directly from `{hcons}`. Let's first
    `rw [Symbol.pow] at {hcons}` to unfold the definition."
    rw [Symbol.pow] at hcons
    Hint "Our previous lemma `cons_cat_cancel` will help here:
    `apply cons_cat_cancel at {hcons}`"
    apply cons_cat_cancel at hcons
    Hint (hidden := true) "We can now close the goal with `exact {hcons}.left`."
    exact hcons.left
Conclusion "Good!"
