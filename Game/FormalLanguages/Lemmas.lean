import Game.FormalLanguages.BasicDefinitions

open Nat
namespace Regular
@[simp]
lemma Word.cat_eps (w : Word) : w ∘ .ε = w := by
  induction' w with s w ih
  · rw [cat]
  · rw [cat, ih]

@[simp]
lemma Word.cat_assoc (x y z : Word) : (x ∘ y) ∘ z = x ∘ y ∘ z := by
  induction' x with s w ih <;> simp_all only [cat]

@[simp]
lemma Word.cat_count {s : Char} (x y : Word) :
    (x ∘ y).count s = x.count s + y.count s := by
  induction' x with s' w ih
  · simp_all only [cat, count, Nat.zero_add]
  · rw [count]
    simp_all only [cat, count]
    split
    next h =>
      omega
    next h => simp_all only

@[simp]
lemma Word.cat_count_zero {s : Char} (x y : Word) :
    (x ∘ y).count s = 0 → x.count s = 0 ∧ y.count s = 0 := by
  intro hcatcount
  apply And.intro <;> simp_all only [cat_count, Nat.add_eq_zero_iff]

lemma Word.cat_char_subset_left (x y : Word) :
    x.chars ⊆ (x ∘ y).chars := by
  simp only [cat_chars, Set.subset_union_left]

lemma Word.cat_char_subset_right (x y : Word) :
    y.chars ⊆ (x ∘ y).chars := by
  simp only [cat_chars, Set.subset_union_right]

lemma Word.cat_len (x y : Word) :
    |(x ∘ y)| = |x| + |y| := by
  induction' x with s x ih
  · simp only [cat, length, Nat.zero_add]
  · rw [Word.length, Nat.add_assoc, ← ih]
    simp_all only [length]


@[simp]
lemma Symbol.pow_len {s : Char} (n : ℕ) : |s ^ n| = n := by
  induction' n with n ih
  · rfl
  · simp only [pow, Word.length]
    rw [ih]
    exact Nat.one_add _

@[simp]
lemma Symbol.pow_count {s₁ s₂ : Char} (n : ℕ) :
    (s₁ ^ n).count s₂ = if s₁ = s₂ then n else 0 := by
  induction' n with n ih
  · simp_all only [pow, Word.count, ite_self]
  · simp_all only [pow, Word.count, ↓reduceIte]
    split
    next h =>
      subst h
      simp_all only [↓reduceIte]
      omega
    next h => simp_all only [↓reduceIte]


--set_option tactic.simp.trace true
lemma Word.cons_a (n : ℕ) (x y z : Word) (hz : x ∘ y = ('a' ^ n) ∘ z) (hx : |x| ≤ n) :
    x.count 'b' = 0 := by
  induction' x with s w ih generalizing n
  · simp_all only [Word.length, Nat.zero_le, Word.count]
  · specialize ih (n - 1)
    simp_all [Word.cat, Word.length, Word.count, Char.isValue]
    have ha : s = 'a' := by
      clear ih
      match n with
      | 0 => simp_all only [cat, le_zero_eq, Nat.add_eq_zero, succ_ne_self, false_and]
      | n + 1 =>
        simp_all only [cat, add_eq, Nat.add_zero, cons.injEq]
    simp_all only [↓Char.isValue, Char.reduceEq, ↓reduceIte]
    subst ha
    match n with
    | 0 =>
      subst hz
      simp_all only [le_zero_eq, Nat.add_eq_zero, succ_ne_self, false_and]
    | n + 1 =>
      simp only [Nat.add_one_sub_one, Char.isValue] at ih
      rw [Symbol.pow] at hz
      simp_all only [not_false_eq_true, cat, cons.injEq, true_and, forall_true_left, Char.isValue]
      exact ih (by omega)

lemma not_pump : ¬pumping_property anbn_lang := by
  rw [pumping_property]
  push_neg  -- push_neg first
  intro n hpos -- introduce n, and the hypothesis that n > 0

  let z : Word := ('a' ^ n) ∘ ('b' ^ n) -- we need to use a fitting word
  -- we'll need to show that the word is actually an element of anbn
  have hzinanbn : z ∈ anbn := by
    rw [anbn, Set.mem_setOf_eq]
    use n
  use z
  -- simp only [gt_iff_lt, ge_iff_le]
  -- we now need to show every conjunct
  constructor
  · exact hzinanbn
  · -- we only need this 'have' because we don't have access to 'set' rather than let
    have heq : z = ('a' ^ n) ∘ 'b' ^ n := rfl
    -- now we need to handle this inner conjunction
    constructor
    · -- showing that the length of z is actually greater than n - fairly trivial step
      rw [heq, Word.cat_len, Symbol.pow_len, Symbol.pow_len]
      omega
    · -- main part of the proof!
      intro u v w hcons hlenlower hv
      use 2
      -- it's obvious that v doesn't contain any b's, but we have to show it!
      have honlyas : v.count 'b' = 0 := by
        clear hv
        -- this simp_all simplifies the proof state for us
        simp_all only [gt_iff_lt, z, ↓Char.isValue]
        have huv : (u ∘ v).count 'b' = 0 := by
          symm at hcons
          rw [← Word.cat_assoc] at hcons
          -- might need to proof the cons_a lemma in the lemma section!
          apply Word.cons_a n (u ∘ v) w ('b' ^ n) hcons hlenlower
        exact (@Word.cat_count_zero 'b' u v huv).right
      -- this is almost as obvious, but much more involved to show!
      have hatleastonea : v.count 'a' > 0 := by
        have hzcharsinab := anbn_lang.word_constraint z hzinanbn
        -- simp to remove the .Alphabet thing
        simp only [anbn_lang, ↓Char.isValue] at hzcharsinab
        -- since v is a subword of z, its characters will be a subset of z's
        have hsub : v.chars ⊆ z.chars := by
          have hleft := Word.cat_char_subset_left v w
          have hright := Word.cat_char_subset_right u (v ∘ w)
          rw [hcons]
          intro c hc
          exact hright (hleft hc)
        -- since z's characters are 'a' and 'b'
        have hvchars : v.chars ⊆ {'a', 'b'} := subset_trans hsub hzcharsinab
        -- clearing a bunch of hypotheses that will only be a distraction otherwise
        clear hzinanbn hlenlower hcons heq u w z hpos n hzcharsinab hsub
        -- from here on out we need a fairly lengthy induction
        induction' v with s w ih
        · simp_all only [Word.length, Nat.le_zero_eq, Nat.succ_ne_self]
        · simp_all only [gt_iff_lt, Word.length, Nat.le_add_right, Word.count, ↓Char.isValue]
          generalize w.count 'a' = n at *
          split_ifs with hs
          · exact Nat.le_add_right 1 n
          · have hsb : s = 'b' := by
              -- once again clearing unnecessary hypotheses
              clear ih honlyas n
              rw [Word.chars] at hvchars
              have hsab := (Set.union_subset_iff.mp hvchars).left
              -- with the preparatory work done, simp_all can take care of the rest
              simp_all only [Set.singleton_union, Set.singleton_subset_iff, Set.mem_insert_iff,
                Set.mem_singleton_iff, false_or]
            split_ifs at honlyas with h
            · simp_all only [Nat.add_eq_zero_iff, Nat.succ_ne_self, false_and]
            · simp_all only
      -- now we can proceed with the rest of the proof
      -- mind that our main hypotheses right now are honlyas and hatleastonea,
      -- and those reflect the steps in the proof that we worked through first
      intro hin
      -- we can do the next rewrite with a separate lemma!
      simp only [Word.pow, Word.cat_eps, Set.mem_setOf_eq, anbn_lang] at hin
      -- another big rewrite
      simp_all only [gt_iff_lt, Word.cat_assoc, z, ↓Char.isValue]
      -- clearing a few unneeded hypotheses
      clear hlenlower hzinanbn hv hpos z
      rcases hin with ⟨m, hm⟩
      have heven : (u ∘ v ∘ v ∘ w).count 'a' = (u ∘ v ∘ v ∘ w).count 'b' := by
        clear hatleastonea honlyas hcons
        simp_all only [Word.cat_count, Symbol.pow_count, ite_true, ite_false, Nat.add_zero, Nat.zero_add, Char.reduceEq]
      have huneven : (u ∘ v ∘ v ∘ w).count 'a' ≠ (u ∘ v ∘ v ∘ w).count 'b' := by
        simp only [Word.cat_count, ne_eq, ↓Char.isValue]
        intro heq
        have hcount : (u ∘ v ∘ w).count 'a' = (u ∘ v ∘ w).count 'b' := by
          rw [← hcons]
          clear hcons
          simp_all only [Nat.zero_add, Word.cat_count, Symbol.pow_count, ite_true, ite_false,
            Nat.add_zero, Nat.add_zero, Nat.zero_add, Char.reduceEq]
        simp only [Word.cat_count, ↓Char.isValue] at hcount
        have hgoal : v.count 'a' = v.count 'b' := by
          omega
        simp_all only [lt_self_iff_false]
      exact huneven heven
