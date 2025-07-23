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

def Word.chars : (w : Word) → Set Char
  | ε => ∅
  | cons s w => {s} ∪ w.chars

structure Language where
  Alphabet : Set Char
  Words : Set Word
  word_constraint : ∀ word ∈ Words, word.chars ⊆ Alphabet

def Word.count (w : Word) (s' : Char) : ℕ := match w with
  | .ε => 0
  | .cons s w => if (s = s') then 1 + w.count s' else w.count s'
#reduce w₂.count 'b'

theorem count_uneq (w u : Word) : (∃ (s : Char), w.count s ≠ u.count s) → w ≠ u := by
  aesop

def Word.length : (w : Word) → ℕ
 | .ε => 0
 | .cons _ w => 1 + w.length

macro:max (priority := 1001) atomic("|" noWs) a:term noWs "|" : term => `(Word.length $a)

def Word.cat (x y : Word) : Word :=
  match x with
 | .ε => y
 | .cons s x => .cons s (x.cat y)

infixr:90 " ∘ " => Word.cat
def Word.pow (w : Word) (n : ℕ) : Word :=
  match n with
  | 0 => .ε
  | .succ n => w ∘ (w.pow n)

infix:92 " ^ " => Word.pow

def Symbol.pow (a : Char) (n : ℕ) : Word :=
  match n with
  | 0 => .ε
  | .succ n => .cons a (Symbol.pow a n)

infix:93 " ^ " => Symbol.pow
lemma Word.cat_chars (x y : Word) : (x ∘ y).chars = x.chars ∪ y.chars := by
  induction' x with s w ih
  · simp only [cat, chars, Set.empty_union]
  · rw [chars, cat, chars, ih]
    rw [Set.union_assoc]

lemma Symbol.pow_chars {s : Char} {n : ℕ} (hn : n > 0) : (s ^ n).chars = {s} := by
  induction' n, hn using Nat.le_induction with n
  · simp_all only [Word.chars, Set.union_empty]
  · simp_all only [Word.chars, add_eq, Nat.add_zero, Set.union_self]

def anbn : Set Word := {w | ∃ n : ℕ, w = ('a' ^ n) ∘ ('b' ^ n)}
def anbn_lang : Language := ⟨{'a', 'b'}, anbn,
  by
    intro w hw c hc
    rw [anbn] at hw
    simp_all only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, ↓Char.isValue]
    rcases hw with ⟨n, hw⟩
    have hchars : w.chars = (('a' ^ n) ∘ 'b' ^ n).chars := by rw [hw]
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

def pumping_property (L : Language) :=
  ∃ (n : ℕ),
  n > 0 ∧
  ∀ z ∈ L.Words,
  (hlen : z.length > n) →
    ∃ (u v w : Word),
      z = u ∘ v ∘ w ∧
      |u ∘ v| ≤ n ∧
      |v| ≥ 1 ∧
      ∀ (i : ℕ), u ∘ v ^ i ∘ w ∈ L.Words
