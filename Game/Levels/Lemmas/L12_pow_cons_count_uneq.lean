import Game.Levels.Lemmas.L11_pow_cons_count_eq
import Game.Metadata

open Nat

World "Lemmas"
Level 12

Title "pow_cons_count_uneq"

Introduction "For the last level of this game, let's prove a much more complex statement!
While it will be much more involved to prove than the other statements in this world,
it will also be very useful in our non-regularity proof."

namespace Regular
/-- A word of the form cⁿ will contain n instances of the character c, and none of any other character. -/
TheoremDoc Regular.pow_cons_count_uneq as "pow_cons_count_uneq" in "pow"

Statement pow_cons_count_uneq (c d : Char) (huneq : c ≠ d) (n : ℕ) (x y z : Word) (hz : x ∘ y = (c ^ n) ∘ z)
    (hx : |x| ≤ n) :
    x.count d = 0 := by
  Hint "This is yet another proof by induction, so start with
  `induction' {x} with s x ih generalizing {n}`"
  induction' x with s x ih generalizing n
  · Hint (hidden := true) "`rw [Word.count]` will solve this goal immediately."
    rw [Word.count]
  · Hint "Since we are in the `.cons` case, we can do a bunch of rewrites
    now. Start out with `rw [Word.length] at {hx}`, as that will be useful
    later on."
    rw [Word.length] at hx
    Hint "We can now look at our goal: `rw [Word.count]`."
    rw [Word.count]
    Hint (hidden := true) "We now have an if-statement in our goal, with the guard `{s} = {d}`.
    From our previous lemma `pow_cons_count_eq`, and by looking at `{hz}` directly,
    it is already obvious that `{s} = {c}` has to hold, and since `{c} ≠ {d}`
    according to `{huneq}`, we must have `{s} ≠ {d}`, meaning that we should
    always land in the `else` case.

    We can now employ our previously proved lemma by pattern matching with its
    arguments:
    `have heq := pow_cons_count_eq {s} {c} {n} ({x} ∘ {y}) {z} {hz} (by omega)`."
    have heq := pow_cons_count_eq s c n (x ∘ y) z hz (by omega)
    Hint "To make use of `{heq}` and `{huneq}` to land in the `else` case,
    let's use `simp [{heq}, {huneq}]`."
    simp [heq, huneq]
    Hint "As we can see, we need to show that `{x}` does not contain any instances
    of the character `{d}`, which matches with our goal before the starting the induction.
    However, we now have the induction hypothesis at our disposal!

    From here on out, the easiest way forward is to match on `{n}`.
    Proceed with `rcases {n} with _ | n`."
    rcases n with _ | n
    · Hint "`simp at {hx}` closes the goal here, since it produces a contradiction."
      simp at hx
    · Hint "if we use `{n}` for our induction hypothesis `{ih}`, we will need to show
      `{x} ∘ {y} = {c} ^ {n} ∘ {z}`. This follows directly from `{hz}`; to show this,
      we first need some rewrites: `rw [Symbol.pow, {heq}] at {hz}`"
      rw [Symbol.pow, heq] at hz
      Hint "We can see that `{hz}` precisely matches a previous lemma
      that we can `apply` to it."
      Hint (hidden := true) "`apply cons_cat_cancel at {hz}`"
      apply cons_cat_cancel at hz
      Hint (strict := true) "To use our induction hypothesis `{ih}`, we also need to show
      `Word.length {x} ≤ {n}`; This follows quite obviously from `{hx}`, so
      we can just show this with

      `have hlen : Word.length {x} ≤ {n} := by omega`"
      have hlen : Word.length x ≤ n := by omega
      Hint (hidden := true) "Close the goal with `exact {ih} {n} {hz}.right {hlen}`."
      exact ih n hz.right hlen

lemma cat_char_subset_left (x y : Word) :
    x.chars ⊆ (x ∘ y).chars := by
  simp only [Word.cat_chars, Set.subset_union_left]

lemma cat_char_subset_right (x y : Word) :
    y.chars ⊆ (x ∘ y).chars := by
  simp only [Word.cat_chars, Set.subset_union_right]
Conclusion "Good!"
