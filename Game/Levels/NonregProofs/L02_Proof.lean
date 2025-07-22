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

Statement : ¬pumping_property anbn_lang := by
  Hint "Let's first `rw [pumping_property]` to recall the definition of the pumping
  property, then `push_neg` to push the negation all the way in."
  rw [pumping_property]
  push_neg
  Hint "We can now replicate the initial 'let n > 0' part of the proof with `intro n hpos`."
  intro n hpos
  Hint "The word we want to use is z = aⁿbⁿ.
  Let's introduce it with `let z : Word := 'a' ^+^ {n} ∘ 'b' ^+^ {n}`"
  let z : Word := 'a' ^+^ n ∘ 'b' ^+^ n
  Hint "We will need to show that z is actually an element of the language anbn in
  a second, so let's introduce that as a new hypothesis: `have hzinanbn : z ∈ anbn`."
  have hzinanbn : z ∈ anbn
  · Hint "After rewriting with `anbn` and `Set.mem_setOf_eq`, we can just `use n`."
    rw [anbn, Set.mem_setOf_eq]
    use n
  Hint "`use z`"
  use z
  Hint "`constructor` will split the conjunction into separate proofs."
  constructor
  · Hint "`exact {hzinanbn}` closes the goal directly."
    exact hzinanbn
  · -- we only need this 'have' because we don't have access to 'set' rather than let
    Hint "Since we're using an earlier Lean version for several reasons, we don't
    have access to the `set` tactic, which would have given us a hypothesis that
    `{z}` is indeed equal to aⁿbⁿ. However, we introduced `{z}` with the `let` tactic,
    so we will need to prove that hypothesis separately:

    `have heq : {z} = 'a' ^+^ n ∘ 'b' ^+^ n := rfl`"
    have heq : z = 'a' ^+^ n ∘ 'b' ^+^ n := rfl
    Hint "We once again use `constructor` to handle the conjunction."
    constructor
    · -- showing that the length of z is actually greater than n - fairly trivial step
      Hint "We need to show that the length of z is indeed greater than n. You can
      `rw` step by step with some of the lemmas that we showed in the previous world,
      and then use the `omega` tactic once you arrive at a proof state of the form
      `n + n > n`."
      Hint (hidden := true) "The exact hypotheses for rewriting that you should use
      are `{heq}`, `Word.cat_len`, `Symbol.pow_len`, and `Symbol.pow_len` again."
      rw [heq, Word.cat_len, Symbol.pow_len, Symbol.pow_len]
      omega
    ·
      Hint "We can finally get to the main part of the proof! First of all, we need
      to introduce all the conditions that we also introduce in the paper proof:

      `intro u v w hcons hlenlower hv`"
      intro u v w hcons hlenlower hv
      Hint "Let's look at our hypotheses: ...

      We now need to provide a suitable `i`; in the paper proof we set `i := 2`,
      so let's `use 2`."
      use 2
      -- it's obvious that v doesn't contain any b's, but we have to show it!
      Hint "In our paper proof, we made an argument for why there are no b's in `{v}`. For our formalization, let's have this as a separate hypothesis:

      `have honlyas: {v}.count 'b' = 0`"
      have honlyas : v.count 'b' = 0
      ·
        -- this simp_all simplifies the proof state for us
        Hint "Let's simplify the entire proof state with
        `simp_all only [gt_iff_lt, {z}, ↓Char.isValue]`"
        simp_all only [gt_iff_lt, z, ↓Char.isValue]
        Hint "The argument in our proof works to show that there are no b's in
        `uv`. Let's show that first: `have huv : (u ∘ v).count 'b' = 0`."
        have huv : (u ∘ v).count 'b' = 0
        ·
          Hint "We need to utilize the associativity that we proved earlier:

          `rw [← Word.cat_assoc]`

          Following that, use the tactic `symm at {hcons}`"
          rw [← Word.cat_assoc] at hcons
          symm at hcons
          -- might need to proof the cons_a lemma in the lemma section!
          Hint "For this specific situation, the lemma `Word.cons_a` is already provided to us, so you can finish the subproof with

          `apply Word.cons_a {n} ({u} ∘ {v}) {w} ('b' ^+^ {n}) {hcons} {hlenlower}`"
          apply Word.cons_a n (u ∘ v) w ('b' ^+^ n) hcons hlenlower
        Hint "We can now use the fresh hypothesis `{huv}`:

        `exact (@Word.cat_count_zero 'b' {u} {v} {huv}).right`"
        exact (@Word.cat_count_zero 'b' u v huv).right
      -- this is almost as obvious, but much more involved to show!
      Hint "For the next step of our proof, we showed that `{v}` contained at least
      one 'a'. This will unfortunately be much more involved to show!"
      have hatleastonea : v.count 'a' > 0
      ·
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

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
