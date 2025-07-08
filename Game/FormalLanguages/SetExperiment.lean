import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs

open Nat

namespace Regular

def ex_alphabet : Set Char := {'a', 'b', 'c'}

inductive Word where
  | ε
  | cons (s : Char) (w : Word)

def w₁ := Word.cons 'a' (Word.cons 'b' .ε)
def w₂ := Word.cons 'b' (Word.cons 'b' (Word.cons 'a' .ε))

@[simp]
def Word.chars : (w : Word) → Set Char
  | ε => ∅
  | cons s w => {s} ∪ w.chars

structure Language where
  Alphabet : Set Char
  Words : Set Word
  word_constraint : ∀ word ∈ Words, word.chars ⊆ Alphabet

@[simp]
def Word.count (w : Word) (s' : Char) : ℕ := match w with
  | .ε => 0
  | .cons s w => if (s = s') then 1 + w.count s' else w.count s'
#reduce w₂.count 'b'

theorem count_uneq (w u : Word) : (∃ (s : Char), w.count s ≠ u.count s) → w ≠ u := by
  aesop

@[simp]
def Word.length : (w : Word) → ℕ
 | .ε => 0
 | .cons _ w => 1 + w.length

macro:max (priority := 1001) atomic("|" noWs) a:term noWs "|" : term => `(Word.length $a)

@[simp]
def Word.cat (x y : Word) : Word :=
  match x with
 | .ε => y
 | .cons s x => .cons s (x.cat y)

infixr:90 " ∘ " => Word.cat
--#reduce w₁ ∘ w₂

@[simp]
lemma Word.cat_eps (w : Word) : w ∘ .ε = w := by
  induction' w with s w ih
  · rw [cat]
  · rw [cat, ih]

@[simp]
lemma Word.cat_assoc (x y z : Word) : (x ∘ y) ∘ z = x ∘ y ∘ z := by
  induction' x with s w ih <;> simp_all only [cat]

@[simp]
lemma Word.assoc_count {s : Char} (x y : Word) :
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
lemma Word.assoc_count_zero {s : Char} (x y : Word) :
    (x ∘ y).count s = 0 → x.count s = 0 ∧ y.count s = 0 := by
  intro hcatcount
  apply And.intro <;> simp_all only [assoc_count, Nat.add_eq_zero_iff]

@[simp]
lemma Word.cat_chars (x y : Word) : (x ∘ y).chars = x.chars ∪ y.chars := by
  induction' x with s w ih
  · simp only [cat, chars, Set.empty_union]
  · aesop

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
def Word.pow (w : Word) (n : ℕ) : Word :=
  match n with
  | 0 => .ε
  | .succ n => w ∘ (w.pow n)

infix:92 " ^ " => Word.pow

--#reduce w₁ ^ 3

@[simp]
def Symbol.pow (a : Char) (n : ℕ) : Word :=
  match n with
  | 0 => .ε
  | .succ n => .cons a (Symbol.pow a n)

infix:91 " ^+^ " => Symbol.pow

@[simp]
lemma Symbol.pow_len {s : Char} (n : ℕ) : |s ^+^ n| = n := by
  induction' n with n ih
  · rfl
  · simp only [pow, Word.length]
    rw [ih]
    exact Nat.one_add _

@[simp]
lemma Symbol.pow_chars {s : Char} {n : ℕ} (hn : n > 0) : (s ^+^ n).chars = {s} := by
  induction' n, hn using Nat.le_induction with n
  · simp_all only [Word.chars, Set.union_empty]
  · simp_all only [Word.chars, add_eq, Nat.add_zero, Set.union_self]

@[simp]
lemma Symbol.pow_count {s₁ s₂ : Char} (n : ℕ) :
    (s₁ ^+^ n).count s₂ = if s₁ = s₂ then n else 0 := by
  induction' n with n ih
  · simp_all only [pow, Word.count, ite_self]
  · simp_all only [pow, Word.count, ↓reduceIte]
    split
    next h =>
      subst h
      simp_all only [↓reduceIte]
      omega
    next h => simp_all only [↓reduceIte]

def anbn : Set Word := {w | ∃ n, w = 'a' ^+^ n ∘ 'b' ^+^ n}
def anbn_lang : Language := ⟨{'a', 'b'}, anbn,
  by
    intro w hw c hc
    rw [anbn] at hw
    simp_all only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, ↓Char.isValue]
    rcases hw with ⟨n, hw⟩
    have hchars : w.chars = ('a' ^+^ n ∘ 'b' ^+^ n).chars := by rw [hw]
    simp only [↓Char.isValue, Word.cat_chars] at hchars
    rw [hchars] at hc
    simp at hc
    match n with
    | 0 =>
      simp_all only [Word.cat, Symbol.pow, Word.chars, Set.union_self, Set.mem_empty_iff_false, or_self]
    | n + 1 =>
      have hpowa := @Symbol.pow_chars 'a' (n + 1) (by omega)
      have hpowb := @Symbol.pow_chars 'b' (n + 1) (by omega)
      rw [hpowa, hpowb] at hc
      simp only [↓Char.isValue, Set.mem_singleton_iff] at hc
      exact hc
  ⟩

set_option linter.unusedVariables false

@[simp]
def pumping_property (L : Language) :=
  ∃ (n : ℕ) (hpos : n > 0),
  ∀ z ∈ L.Words,
  (hlen : z.length > n) →
    ∃ (u v w : Word),
      z = u ∘ v ∘ w ∧
      |u ∘ v| ≤ n ∧
      |v| ≥ 1 ∧
      ∀ (i : ℕ), u ∘ v ^ i ∘ w ∈ L.Words

--set_option tactic.simp.trace true
lemma Word.cons_a (n : ℕ) (x y z : Word) (hz : x ∘ y = 'a' ^+^ n ∘ z) (hx : |x| ≤ n) :
    x.count 'b' = 0 := by
  induction' x with s w ih generalizing n
  · simp_all only [Word.length, Nat.zero_le, Word.count]
  · specialize ih (n - 1)
    simp_all only [Word.cat, Word.length, Word.count, ↓Char.isValue]
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
      simp only [Nat.add_one_sub_one, ↓Char.isValue] at ih
      rw [Symbol.pow] at hz
      simp_all only [not_false_eq_true, cat, cons.injEq, true_and, forall_true_left, ↓Char.isValue]
      exact ih (by omega)

lemma not_pump : ¬pumping_property anbn_lang := by
  rw [pumping_property]
  push_neg
  intro n hpos
  let z : Word := ('a' ^+^ n) ∘ ('b' ^+^ n)
  have hzinnonreg : z ∈ anbn := by
    simp_all only [gt_iff_lt]
    rw [anbn]
    simp only [Set.mem_setOf_eq]
    use n
  use z
  simp only [gt_iff_lt, ge_iff_le]
  constructor
  · exact hzinnonreg
  · have heq : z = 'a' ^+^ n ∘ 'b' ^+^ n := rfl
    constructor
    · rw [anbn] at hzinnonreg
      rw [heq, Word.cat_len]
      clear hzinnonreg
      repeat rw [Symbol.pow_len]
      exact Nat.lt_add_of_pos_right hpos
    · intro u v w hcons hlenlower hv
      use 2
      have honlyas : v.count 'b' = 0 := by
        clear hv
        have hz : |z| = 2*n := by
          rw [heq, Word.cat_len, Symbol.pow_len, Symbol.pow_len]
          omega
        simp_all only [gt_iff_lt, z, ↓Char.isValue]
        have huv : (u ∘ v).count 'b' = 0 := by
          symm at hcons
          rw [← Word.cat_assoc] at hcons
          apply Word.cons_a n (u ∘ v) w ('b' ^+^ n) hcons hlenlower
        exact (@Word.assoc_count_zero 'b' u v huv).right
      have hatleastonea : v.count 'a' > 0 := by
        have hthing := anbn_lang.word_constraint z hzinnonreg
        have hsub : v.chars ⊆ z.chars := by
          have hleft := Word.cat_char_subset_left v w
          have hright := Word.cat_char_subset_right u (v ∘ w)
          rw [hcons]
          exact fun _ hin ↦ hright (hleft hin)
        have hvchars : v.chars ⊆ {'a', 'b'} := fun _ a_1 ↦ hthing (hsub a_1)
        clear hzinnonreg hlenlower hcons heq u w z hpos n hthing hsub
        induction' v with s w ih
        · simp_all only [Word.length, Nat.le_zero_eq, Nat.succ_ne_self]
        · simp_all only [gt_iff_lt, Word.length, Nat.le_add_right, Word.count, ↓Char.isValue]
          generalize w.count 'a' = n at *
          split_ifs with hs
          · subst hs
            have hsim : 1 ≤ 1 + n := by exact Nat.le_add_right 1 n
            exact hsim
          · have hsb : s = 'b' := by
              clear ih honlyas n
              rw [Word.chars] at hvchars
              have hsab := (Set.union_subset_iff.mp hvchars).left
              simp_all only [Set.singleton_union, Set.singleton_subset_iff, Set.mem_insert_iff,
                Set.mem_singleton_iff, false_or]
            split at honlyas
            next h =>
              subst h
              simp_all only [Nat.add_eq_zero_iff, Nat.succ_ne_self, false_and]
            next h =>
              simp_all only
      intro hin
      rw [anbn_lang] at hin
      simp only [Word.pow, Word.cat_eps, Set.mem_setOf_eq] at hin
      simp_all only [gt_iff_lt, Word.cat_assoc, z]
      have huneven : (u ∘ v ∘ v ∘ w).count 'a' ≠ (u ∘ v ∘ v ∘ w).count 'b' := by
        simp only [Word.assoc_count, ne_eq, z]
        apply Aesop.BuiltinRules.not_intro
        intro heq
        have hcount : (u ∘ v ∘ w).count 'a' = (u ∘ v ∘ w).count 'b' := by
          rw [← hcons]
          clear hcons
          simp_all only [Nat.zero_add, Word.assoc_count, Symbol.pow_count, ite_true, ite_false,
            Nat.add_zero]
          simp_all only [↓Char.isValue,
            Char.reduceEq,
            ↓reduceIte,
            Nat.add_zero,
            Nat.zero_add]
        simp only [Word.assoc_count] at hcount
        have hgoal : v.count 'a' = v.count 'b' := by
          omega
        simp_all only [lt_self_iff_false, z]
      rcases hin with ⟨m, hm⟩
      have heven : (u ∘ v ∘ v ∘ w).count 'a' = (u ∘ v ∘ v ∘ w).count 'b' := by
        clear huneven
        simp_all only [Word.assoc_count, Symbol.pow_count, ite_true, ite_false, Nat.add_zero,
          Nat.zero_add]
        simp_all only [↓Char.isValue,
          Char.reduceEq,
          ↓reduceIte,
          Nat.add_zero,
          Nat.zero_add]
      simp_all only [Word.assoc_count, ne_eq, z]
