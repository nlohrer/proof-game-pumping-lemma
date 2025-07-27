import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Defs
import Game.FormalLanguages.BasicDefinitions
import Mathlib.Computability.DFA

namespace Regular

#check DFA

#check "hello"

@[simp]
def charListToWord : List Char → Word
  | [] => .ε
  | c :: s => .cons c (charListToWord s)

@[simp]
def stringToWord : String → Word
  | ⟨s⟩ => charListToWord s

structure DFA where
  Z : Finset ℕ
  Sigma : Set Char
  z0 : ℕ
  hzinZ : z0 ∈ Z
  E : Set ℕ
  hE : E ⊆ Z
  delta : ℕ → Char → ℕ
  hdelta : ∀ z ∈ Z, ∀ s ∈ Sigma, delta z s ∈ Z

def example_dfa : DFA :=
  ⟨{0, 1, 2},
  {'a', 'b'},
  0,
  by exact Finset.mem_insert_self 0 {1, 2},
  {2},
  by simp,
  λ n c ↦ match n, c with
    | 0, 'a' => 1
    | 1, 'a' => 2
    | 2, 'a' => 2
    | 0, 'b' => 0
    | 1, 'b' => 0
    | 2, 'b' => 2
    | _, _ => 100
  ,
  by intro z hz s hs; aesop⟩

@[simp]
def processFrom (dfa : DFA) (currentState : ℕ) (w : Word) : ℕ :=
  match w with
  | .ε => currentState
  | .cons c w => processFrom dfa (dfa.delta currentState c) w

@[simp]
def process (dfa : DFA) (w : Word) : ℕ :=
  processFrom dfa dfa.z0 w

@[simp]
def stateSequenceFrom (dfa : DFA) (w : Word) (currentState : ℕ) : List ℕ :=
  match w with
  | .ε => [currentState]
  | .cons c w => currentState :: stateSequenceFrom dfa w (dfa.delta currentState c)

@[simp]
def stateSequence (dfa : DFA) (w : Word) : List ℕ :=
  stateSequenceFrom dfa w dfa.z0

@[simp]
lemma state_len_from (dfa : DFA) (w : Word) (currentState : ℕ) :
    (stateSequenceFrom dfa w currentState).length = |w| + 1 := by
  induction' w with c w ih generalizing currentState
  · simp_all only [stateSequenceFrom, List.length_singleton, Word.length, zero_add]
  · specialize ih (dfa.delta currentState c)
    rw [stateSequenceFrom, List.length, ih, Word.length]
    omega

@[simp]
lemma state_len (dfa : DFA) (w : Word) : (stateSequence dfa w).length = |w| + 1 := by
  simp_all only [stateSequence, state_len_from]

@[simp]
lemma state_sub (dfa : DFA) (w : Word) : (stateSequence dfa w).toFinset ⊆ dfa.Z := by
  sorry

#check List.Mem

#check List.nodup_iff_forall_not_duplicate
#check List.nodup_iff_get?_ne_get?
#check Fintype.card_le_of_surjective
#check Fintype.card_le_of_injective
#check Fintype.card_of_bijective
#check Finset.card_eq_of_bijective
#check List.removeNth

lemma nodup_subset_sub (A B : List U) (hsub : A ⊆ B) (hlen : A.length = B.length)
    (huniq : A.Nodup) : B ⊆ A := by
  generalize hn : List.length A = n at *
  induction' n with n ih generalizing A B
  · simp only [Nat.zero_eq] at hlen
    symm at hlen
    apply List.length_eq_zero.mp at hlen
    intro ab hb
    rw [hlen] at hb
    by_contra _
    exact List.not_mem_nil ab hb
  · match A, B with
    | a :: A, b :: B =>
      intro ab hab
      rw [List.mem_cons]
      by_cases hbinA : b ∈ A
      · rw [List.mem_cons] at hab
        rcases hab with hb | hB
        · subst hb
          right
          exact hbinA
        · simp only [List.cons_subset, List.mem_cons] at hsub
          obtain ⟨ha, hsub⟩ := hsub
          -- could probably rewrite many of these proofs by casting Lists to Finsets
          rcases ha with ha | ha
          · subst ha
            simp_all only [List.nodup_cons, not_true_eq_false, false_and]
          · rw [List.nodup_cons] at huniq
            obtain ⟨hanotinA, huniq⟩ := huniq
            by_cases hab : ab ∈ A
            · right
              exact hab
            · left
              rw [List.mem_iff_get] at ha
              rcases ha with ⟨i, ha⟩
              specialize ih A (b :: B.removeNth i) _ huniq (by simp_all) (_)
              · rw [← ha] at hanotinA
                clear hab hB hbinA huniq hn hlen ab ih ha a
                intro a ha
                specialize hsub ha
                rw [List.mem_cons] at *
                rcases hsub with hab | haB
                · left
                  exact hab
                · right
                  by_contra h
                  have hai : a = List.get B i := by
                    clear ha hanotinA A
                    induction' B with b B ih
                    · simp_all only [List.not_mem_nil]
                    · induction' i using Fin.induction with i _
                      · simp_all only [List.mem_cons, List.removeNth, List.get_cons_zero, or_false]
                      · rw [Fin.succ] at h
                        simp only at h
                        rw [List.removeNth, List.mem_cons] at h
                        simp_all only [List.mem_cons, List.length_cons, Fin.coe_castSucc,
                        List.removeNth, Nat.add_eq, add_zero, List.get_cons_succ']
                        push_neg at h
                        obtain ⟨haneqb, hanelemBi⟩ := h
                        rcases haB with hab | haB
                        · exact (haneqb hab).elim
                        · exact ih i haB hanelemBi
                  rw [hai] at ha
                  exact hanotinA ha
              · clear hn huniq hanotinA hsub hab hbinA A ha a ih
                rw [List.length]
                simp at hlen
                match B with
                | [] => simp_all only [List.not_mem_nil]
                | b' :: B =>
                  induction' i using Fin.induction
                  · simp_all only [List.mem_cons, List.length_cons, List.removeNth]
                  · rw [List.length_removeNth]
                    · omega
                    · exact (Fin.succ i_1).isLt
              by_contra h
              have hab' : ab ∈ b :: List.removeNth B ↑i := by
                rw [← ha] at h
                clear hn hlen ha huniq hanotinA hsub hab hbinA ih a A
                rw [List.mem_cons]
                right
                induction' B with b B ih
                · exact hB
                · rw [List.mem_cons] at hB
                  induction' i using Fin.induction with i _
                  · simp_all only [List.get_cons_zero, List.removeNth, false_or]
                  · rcases hB with hb | hB
                    · simp_all
                    · right
                      exact ih hB i h
              exact hab (ih hab')
      · rw [List.mem_cons] at hab
        have hAsubB : A ⊆ B := by
          have hAsub : A ⊆ b :: B := by
            simp_all only [List.cons_subset, List.mem_cons, List.nodup_cons, List.length_cons,
              Nat.succ.injEq]
          clear ih hsub huniq hn hab ab hlen
          intro a ha
          specialize hAsub ha
          rw [List.mem_cons] at hAsub
          rcases hAsub with hb | hB
          · rw [hb] at ha
            exact (hbinA ha).elim
          · exact hB
        specialize ih A B hAsubB (List.Nodup.of_cons huniq)
          (Nat.succ.inj hn) ((Nat.succ.inj (id hlen.symm)).symm)
        rcases hab with hb | hB
        · subst hb
          left
          simp_all only [List.nodup_cons, List.length_cons, Nat.succ.injEq, List.cons_subset,
            List.mem_cons]
          apply And.left at hsub
          rcases hsub with hab | haB
          · exact hab.symm
          · specialize ih haB
            exact (huniq.left ih).elim
        · right
          exact ih hB
    | [], [] => exact hsub

@[simp]
lemma nodup_subset_nodup [DecidableEq U] (A B : List U) (hsub : A ⊆ B) (hsize : A.length = B.length)
    (huniq : A.Nodup) : B.Nodup := by
  generalize hn : List.length A = n
  have hsubB := nodup_subset_sub A B hsub hsize huniq
  rw [@List.nodup_iff_get?_ne_get?] at *
  intro i j hih hhlen heq
  have hiB := lt_trans hih hhlen
  rw [List.get?_eq_get hiB, List.get?_eq_get hhlen, Option.some.injEq] at heq
  have hiA := hsubB (List.get_mem B i hiB)
  have hjA := hsubB (List.get_mem B j hhlen)
  rw [@List.mem_iff_get] at hiA hjA
  rcases hiA with ⟨i', hi'⟩
  rcases hjA with ⟨j', hj'⟩
  specialize huniq i' j'
  sorry

/-   specialize hsubB b
  induction' n with n ih generalizing A B
  · sorry
  · match A, B with
    | a :: A, b :: B =>
      sorry
    | [], [] => simp_all -/
/-   by_contra h
  rw [List.nodup_iff_count_le_one] at h -/

@[simp]
lemma pigeon_prep (A B : List U) (hsub : A ⊆ B) (hsize : B.length = A.length)
    (huniq : ∀ (i j : Fin A.length), A[i] ≠ A[j]) :
    ∀ (i : Fin A.length),
    ∃! (j : Fin B.length), A[i] = B[j] := by
  intro i
  have hin : A[i] ∈ A := by
    clear hsize hsub huniq
    rw [@List.mem_iff_get]
    use i
    rfl
  specialize hsub hin
  have hind := List.mem_iff_get.mp hsub
  rcases hind with ⟨j, hj⟩
  use j
  constructor
  · exact id hj.symm
  · intro k heq
    sorry

@[simp]
lemma general_pigeon (A B : List U) (hsub : A ⊆ B) (hsize : B.length + 1 = A.length)
    (n : ℕ) (hlen : n = A.length) :
    ∃ (i j : Fin A.length), i ≠ j ∧ A[i] = A[j] := by
  by_contra h
  push_neg at h
  match A with
  | [] => simp_all
  | a :: A =>
/-     have huniq : ∀ (i j : Fin A.length), i ≠ j → A[i] ≠ A[j] := by
      intro i j huneq heq
      have i' := Fin.succ i
      have j' := Fin.succ j
      specialize h ⟨i, Fin.find.proof_6 (List.length A) i⟩
        ⟨j, Fin.find.proof_6 (List.length A) j⟩
        (by intro heq'; simp at heq'; exact huneq (Fin.eq_of_val_eq heq'))
      apply h
      simp_all
      sorry -/

    have hprep := pigeon_prep A B (by sorry) (by exact Nat.succ.inj hsize) sorry
    sorry

/-   induction' n with n ih generalizing A B
  · simp_all
    symm at hlen
    have h : A = [] := by
      exact List.length_eq_zero.mp hlen
    simp_all only [List.nil_subset, List.length_nil, add_eq_zero, one_ne_zero, and_false]
  · have hmin : List.length A > 0 := by omega
    use 0
    use 0
    use (by exact hmin)
    use (by exact hmin)
    sorry -/

lemma pigeon (dfa : DFA) (w : Word) (hlen : dfa.Z.card = |w|) :
    ∃ (i j : Fin (|w| + 1)),
    (stateSequence dfa w)[i] = (stateSequence dfa w)[j] := by
  have h := state_len dfa w
  by_contra hneg
  push_neg at hneg
  have hstate := state_sub dfa w

  sorry
/-   by_contra hneg
  push_neg at hneg
  have hcon : |w| < dfa.Z.card := by
    sorry
  clear hneg
  omega -/
/-   generalize hn : dfa.Z.card = n at *
  induction' w with c w ih
  · aesop
  · rw [stateSequenceFrom]
    simp only [List.length_cons]
    sorry -/

def ex_word : Word := .cons 'b' (.cons 'a' (.cons 'a' .ε))
def ex_word2 : Word := stringToWord "bbbab"

def accepted_lang (dfa : DFA) : Set Word :=
  {word | (process dfa word) ∈ dfa.E}

#reduce ex_word ∈ (accepted_lang example_dfa)

#reduce processFrom example_dfa 1 ex_word
#reduce stateSequence example_dfa ex_word
#reduce stateSequence example_dfa (stringToWord "babaaba")
#reduce stateSequence example_dfa (stringToWord "a")


def dfa_pumping (dfa : DFA) (L : Language) (hmodel : L.Words = accepted_lang dfa) :
    pumping_property L := by
  simp_all only [pumping_property, gt_iff_lt, ge_iff_le, exists_prop]
  --let n := dfa.Z.card
  use dfa.Z.card
  constructor
  · sorry
  · intro z hz hlen
    rw [accepted_lang] at hz
    simp only [process, Set.mem_setOf_eq] at hz
    set states := stateSequence dfa z with hstates
    have hstatelen := state_len dfa z
    rw [← hstates] at hstatelen
    have hdup : ∃ (j k : ℕ) (hj : j < states.length) (hk : k < states.length),
        states[j] = states[k] := by
      sorry
    have hwlog : ∃ (states : List ℕ), states.toFinset ⊆ dfa.Z := sorry
    rcases hwlog with ⟨qs, hqs⟩
    sorry
