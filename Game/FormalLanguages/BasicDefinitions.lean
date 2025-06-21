import Mathlib.Data.Set.Basic

namespace Regular

inductive Symbol where
  | a
  | b

instance : DecidableEq Symbol :=
  λ
  | .a, .a
  | .b, .b => isTrue rfl
  | .a, .b
  | .b, .a => isFalse (by intro h; contradiction)

inductive Word where
  | ε
  | cons (s : Symbol) (w : Word)

def w₁ := Word.cons .a (Word.cons .b .ε)
def w₂ := Word.cons .b (Word.cons .b (Word.cons .a .ε))

@[simp]
def Word.count (w : Word) (s' : Symbol) : ℕ := match w with
  | .ε => 0
  | .cons s w => if (s = s') then 1 + w.count s' else w.count s'
#reduce w₂.count .b

theorem count_uneq (w u : Word) : (∃ (s : Symbol), w.count s ≠ u.count s) → w ≠ u := by
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

@[simp]
lemma Word.cat_eps (w : Word) : w ∘ .ε = w := by
  induction' w with s w ih
  · rw [cat]
  · rw [cat, ih]

@[simp]
lemma Word.cat_assoc (x y z : Word) : (x ∘ y) ∘ z = x ∘ y ∘ z := by
  induction' x with s w ih <;> simp_all only [cat]

@[simp]
lemma Word.assoc_count {s : Symbol} (x y : Word) :
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
lemma Word.assoc_count_zero {s : Symbol} (x y : Word) :
    (x ∘ y).count s = 0 → x.count s = 0 ∧ y.count s = 0 := by
  intro hcatcount
  apply And.intro <;> simp_all only [assoc_count, Nat.add_eq_zero_iff]

lemma Word.cat_len (x y : Word) :
    |(x ∘ y)| = |x| + |y| := by
  induction' x with s x ih
  · simp only [cat, length, Nat.zero_add]
  · rw [Word.length, Nat.add_assoc, ← ih]
    simp_all only [length]

#reduce w₂ ∘ w₁ ∘ w₁
@[simp]
def Word.pow (w : Word) (n : ℕ) : Word :=
  match n with
  | 0 => .ε
  | .succ n => w ∘ (w.pow n)

infix:92 " ^ " => Word.pow

--#reduce w₁ ^ 3

@[simp]
def Symbol.pow (a : Symbol) (n : ℕ) : Word :=
  match n with
  | 0 => .ε
  | .succ n => .cons a (Symbol.pow a n)

infix:91 " ^+^ " => Symbol.pow
#reduce .a ^+^ 5 ∘ .b ^+^ 3

lemma Symbol.pow_len {s : Symbol} (n : ℕ) : |s ^+^ n| = n := by
  induction' n with n ih
  · rfl
  · simp only [pow, Word.length]
    rw [ih]
    exact Nat.one_add _

@[simp]
lemma Symbol.pow_count {s₁ s₂ : Symbol} (n : ℕ) :
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

def anbn : Set Word := {w | ∃ n, w = .a ^+^ n ∘ .b ^+^ n}
set_option linter.unusedVariables false

@[simp]
def pumping_property (L : Set Word) :=
  ∃ (n : ℕ) (hpos : n > 0),
  ∀ z ∈ L,
  (hlen : z.length > n) →
    ∃ (u v w : Word) (heq : z = u ∘ v ∘ w),
      |u ∘ v| ≤ n ∧
      |v| ≥ 1 ∧
      ∀ (i : ℕ), u ∘ v ^ i ∘ w ∈ L

-- TODO: REFACTOR
lemma Word.cons_a (n : ℕ) (x y z : Word) (hz : x ∘ y = .a ^+^ n ∘ z) (hx : |x| ≤ n) :
    x.count .b = 0 := by
  induction' x with s w ih generalizing n
  · simp_all only [Word.length, Nat.zero_le, Word.count]
  · specialize ih (n - 1)
    simp_all only [Word.cat, Word.length, Word.count]
    split
    next h =>
      subst h
      simp_all only [Nat.add_eq_zero_iff, Nat.succ_ne_self, false_and]
      match n with
      | 0 =>
        subst hz
        simp_all only [Nat.le_zero_eq, Nat.add_eq_zero_iff, Nat.succ_ne_self, false_and]
      | n + 1 =>
        simp_all only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, cat, Nat.add_eq, Nat.add_zero,
          cons.injEq, false_and]
    next h =>
      have ha : s = Symbol.a := by
        match s with
        | .a => rfl
        | .b => exact False.elim (h rfl)
      subst ha
      match n with
      | 0 =>
        subst hz
        simp_all only [not_false_eq_true, Nat.le_zero_eq, cat, Nat.zero_sub]
        generalize length w = n at *
        omega
      | n + 1 =>
        simp only [Nat.add_one_sub_one] at ih
        rw [Symbol.pow] at hz
        simp_all only [not_false_eq_true, cat, cons.injEq, true_and, forall_true_left]
        exact ih (by omega)

lemma not_pump : ¬pumping_property anbn := by
  rw [pumping_property]
  push_neg
  intro n hpos
  let z : Word := (.a ^+^ n) ∘ (.b ^+^ n)
  have hzinnonreg : z ∈ anbn := by
    simp_all only [gt_iff_lt]
    rw [anbn]
    simp only [Set.mem_setOf_eq]
    use n
  use z
  simp only [gt_iff_lt, ge_iff_le]
  constructor
  · exact hzinnonreg
  · have heq : z = Symbol.a ^+^ n ∘ Symbol.b ^+^ n := rfl
    constructor
    · rw [anbn] at hzinnonreg
      rw [heq]
      rw [Word.cat_len]
      clear hzinnonreg
      repeat rw [Symbol.pow_len]
      exact Nat.lt_add_of_pos_right hpos
    · intro u v w hcons hlenlower hv
      use 2
      have honlyas : v.count .b = 0 := by
        clear hv
        have hz : |z| = 2*n := by
          rw [heq, Word.cat_len, Symbol.pow_len, Symbol.pow_len]
          omega
        simp_all only [gt_iff_lt, z]
        have huv : (u ∘ v).count .b = 0 := by
          symm at hcons
          rw [← Word.cat_assoc] at hcons
          apply Word.cons_a n (u ∘ v) w (.b ^+^ n) hcons hlenlower
        exact (@Word.assoc_count_zero Symbol.b u v huv).right
      have hatleastonea : v.count .a > 0 := by
        clear hzinnonreg hlenlower hcons heq u w z hpos n
        induction' v with s w ih
        · simp_all only [Word.length, Nat.le_zero_eq, Nat.succ_ne_self]
        · simp_all only [gt_iff_lt, Word.length, Nat.le_add_right, Word.count]
          generalize w.count Symbol.a = n at *
          split_ifs with hs
          · subst hs
            simp_all only [ite_false, forall_true_left]
            have hsim : 1 ≤ 1 + n := by exact Nat.le_add_right 1 n
            exact hsim
          · split at honlyas
            next h =>
              subst h
              simp_all only [Nat.add_eq_zero_iff, Nat.succ_ne_self, false_and]
            next h =>
              simp_all only [forall_const]
              match s with
              | .a => exact False.elim (hs rfl)
              | .b => exact False.elim (h rfl)
      intro hin
      rw [anbn] at hin
      simp only [Word.pow, Word.cat_eps, Set.mem_setOf_eq] at hin
      --have h (w : Word) : w ∈ nonreg → w.count .a = w.count .b := sorry
      simp_all only [gt_iff_lt, Word.cat_assoc, z]
      have huneven : (u ∘ v ∘ v ∘ w).count .a ≠ (u ∘ v ∘ v ∘ w).count .b := by
        simp only [Word.assoc_count, ne_eq, z]
        apply Aesop.BuiltinRules.not_intro
        intro heq
        have hcount : (u ∘ v ∘ w).count .a = (u ∘ v ∘ w).count .b := by
          rw [← hcons]
          clear hcons
          simp_all only [Nat.zero_add, Word.assoc_count, Symbol.pow_count, ite_true, ite_false,
            Nat.add_zero]
        simp only [Word.assoc_count] at hcount
        have hgoal : v.count .a = v.count .b := by
          omega
        simp_all only [lt_self_iff_false, z]
      rcases hin with ⟨m, hm⟩
      have heven : (u ∘ v ∘ v ∘ w).count .a = (u ∘ v ∘ v ∘ w).count .b := by
        clear huneven
        simp_all only [Word.assoc_count, Symbol.pow_count, ite_true, ite_false, Nat.add_zero,
          Nat.zero_add]
      simp_all only [Word.assoc_count, ne_eq, z]
