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
  | cons (a : Symbol) (w : Word)

def w₁ := Word.cons .a (Word.cons .b .ε)
def w₂ := Word.cons .b (Word.cons .b (Word.cons .a .ε))

@[simp]
def Word.count (w : Word) (a : Symbol) : ℕ := match w with
  | .ε => 0
  | .cons s w => if (s = a) then 1 + w.count a else w.count a
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
 | .cons a x => .cons a (x.cat y)

infixr:90 " ∘ " => Word.cat

@[simp]
lemma Word.cat_eps (w : Word) : w ∘ .ε = w := by
  induction' w with s w ih
  · rw [cat]
  · rw [cat, ih]

lemma Word.cat_len (x y : Word) :
    |(x ∘ y)| = |x| + |y| := by
  induction' x with a x ih
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
  · simp only [Word.length]
    rw [ih]
    exact Nat.one_add _

def anbn : Set Word := {w | ∃ n, w = .a ^+^ n ∘ .b ^+^ n}

@[simp]
def pumping_property (L : Set Word) :=
  ∃ (n : ℕ) (hpos : n > 0),
  ∀ z ∈ L,
  (hlen : z.length > n) →
    ∃ (u v w : Word) (heq : z = u ∘ v ∘ w),
      |u ∘ v| ≤ n ∧
      |v| ≥ 1 ∧
      ∀ (i : ℕ), u ∘ (v ^ i) ∘ w ∈ L

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
        sorry
      have hatleastonea : v.count .a > 0 := by
        clear hzinnonreg hlenlower hcons heq u w z hpos n
        sorry
      intro hin
      rw [anbn] at hin
      simp only [Word.pow, Word.cat_eps, Set.mem_setOf_eq] at hin
      rcases hin with ⟨m, hm⟩
      --have h (w : Word) : w ∈ nonreg → w.count .a = w.count .b := sorry
      sorry
