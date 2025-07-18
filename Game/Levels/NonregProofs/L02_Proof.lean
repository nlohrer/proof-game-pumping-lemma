import Game.Levels.Lemmas.L09_pow_count
import Game.Metadata

World "NonregProofs"
Level 2

Title "Proving the nonregularity of aⁿbⁿ"

Introduction "We are finally ready to work through a proof that utilizes the pumping lemma!
The proof on paper is as follows:
-
...
-

We will want to replicate the structure of the proof in Lean, but it will turn out
that some of the steps are far more difficult to realize than on paper. Therefore,
we will mostly guide you through each of the individual steps; you should therefore
try to follow the instructions closely, as later steps might be contingent on earlier
ones so that the proof state is in a fitting form.
"

namespace Regular

Statement not_pump : ¬pumping_property anbn_lang := by
  rw [pumping_property]
  push_neg
  intro n hpos
  let z : Word := ('a' ^+^ n) ∘ ('b' ^+^ n)
  have hzinanbn : z ∈ anbn := by
    simp_all only [gt_iff_lt]
    rw [anbn]
    simp only [Set.mem_setOf_eq]
    use n
  use z
  simp only [gt_iff_lt, ge_iff_le]
  constructor
  · exact hzinanbn
  · have heq : z = 'a' ^+^ n ∘ 'b' ^+^ n := rfl
    constructor
    · rw [anbn] at hzinanbn
      rw [heq, Word.cat_len]
      clear hzinanbn
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
        exact (@Word.cat_count_zero 'b' u v huv).right
      have hatleastonea : v.count 'a' > 0 := by
        have hthing := anbn_lang.word_constraint z hzinanbn
        have hsub : v.chars ⊆ z.chars := by
          have hleft := Word.cat_char_subset_left v w
          have hright := Word.cat_char_subset_right u (v ∘ w)
          rw [hcons]
          exact fun _ hin ↦ hright (hleft hin)
        have hvchars : v.chars ⊆ {'a', 'b'} := fun _ a_1 ↦ hthing (hsub a_1)
        clear hzinanbn hlenlower hcons heq u w z hpos n hthing hsub
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
        simp only [Word.cat_count, ne_eq, z]
        apply Aesop.BuiltinRules.not_intro
        intro heq
        have hcount : (u ∘ v ∘ w).count 'a' = (u ∘ v ∘ w).count 'b' := by
          rw [← hcons]
          clear hcons
          simp_all only [Nat.zero_add, Word.cat_count, Symbol.pow_count, ite_true, ite_false,
            Nat.add_zero]
          simp_all only [↓Char.isValue,
            Char.reduceEq,
            ↓reduceIte,
            Nat.add_zero,
            Nat.zero_add]
        simp only [Word.cat_count] at hcount
        have hgoal : v.count 'a' = v.count 'b' := by
          omega
        simp_all only [lt_self_iff_false, z]
      rcases hin with ⟨m, hm⟩
      have heven : (u ∘ v ∘ v ∘ w).count 'a' = (u ∘ v ∘ v ∘ w).count 'b' := by
        clear huneven
        simp_all only [Word.cat_count, Symbol.pow_count, ite_true, ite_false, Nat.add_zero,
          Nat.zero_add]
        simp_all only [↓Char.isValue,
          Char.reduceEq,
          ↓reduceIte,
          Nat.add_zero,
          Nat.zero_add]
      simp_all only [Word.cat_count, ne_eq, z]

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
