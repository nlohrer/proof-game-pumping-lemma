import Game.Levels.Lemmas.L10_cons_a
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
  Let's introduce it with `set z : Word := ('a' ^ n) ∘ 'b' ^ n with hz`"
  set z : Word := ('a' ^ n) ∘ 'b' ^ n with hz
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
    Hint "We once again use `constructor` to handle the conjunction."
    constructor
    · -- showing that the length of z is actually greater than n - fairly trivial step
      Hint "We need to show that the length of z is indeed greater than n. You can
      `rw` step by step with some of the lemmas that we showed in the previous world,
      and then use the `omega` tactic once you arrive at a proof state of the form
      `n + n > n`."
      Hint (hidden := true) "The exact hypotheses for rewriting that you should use
      are `{hz}`, `cat_len`, `pow_len`, and `pow_len` again."
      rw [hz, cat_len, pow_len, pow_len]
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

      `have honlyas : {v}.count 'b' = 0`"
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

          `rw [← Word.cat_assoc] at hcons`

          Following that, use the tactic `symm at {hcons}`"
          rw [← cat_assoc] at hcons
          symm at hcons
          -- might need to proof the cons_a lemma in the lemma section!
          Hint "For this specific situation, the lemma `Word.cons_a` is already provided to us, so you can finish the subproof with

          `apply Word.cons_a {n} ({u} ∘ {v}) {w} ('b' ^ {n}) {hcons} {hlenlower}`"
          apply cons_a n (u ∘ v) w ('b' ^ n) hcons hlenlower
        Hint "We can now use the fresh hypothesis `{huv}`:

        `exact (@Word.cat_count_zero 'b' {u} {v} {huv}).right`"
        exact (@cat_count_zero 'b' u v huv).right
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
          have hleft := cat_char_subset_left v w
          have hright := cat_char_subset_right u (v ∘ w)
          rw [hcons]
          intro c hc
          exact hright (hleft hc)
        -- since z's characters are 'a' and 'b'
        have hvchars : v.chars ⊆ {'a', 'b'} := subset_trans hsub hzcharsinab
        -- clearing a bunch of hypotheses that will only be a distraction otherwise
        Hint "We have a lot of unnecessary hypotheses, so let's remove them:

        `clear {hzinanbn} {hlenlower} {hcons} {hz} {u} {w} {z} {hpos} {n} {hzcharsinab} {hsub}`"
        clear hzinanbn hlenlower hcons hz u w z hpos n hzcharsinab hsub
        Hint "The fact that v contains no a's should follow quite obviously from
        {honlyas} and {hvchars}.

        We still need to do the rest of the work to show our statement. Let's pattern match
        on `{v}` with `rcases v with _ | ⟨s, w⟩`."
        -- from here on out we need a fairly lengthy induction
        rcases v with _ | ⟨s, w⟩
        · Hint "{hv} states that our word should have a length of at least 1, but
          the empty word `ε` has a length of 0, meaning that we get a contradiction
          in our hypotheses. As we can achieve any goal from a false hypothesis,
          this is exactly what we want!

          To reduce {hv} to false, just use `simp [Word.length] at {hv}`, which
          will also do some additional steps that end up closing the goal directly."
          simp [Word.length] at hv
        · Hint "Let's use `simp_all [Word.length, Word.count]` to simplify our proof state."
          simp_all [Word.length, Word.count]
          Hint "At this point, we don't specifically care about the fact that `{w}.count 'a'`
          specifically describes how many a's there are in {w} - we just care about the fact that
          it is some arbitrary natural number. We can therefore make the proof state a bit more
          readible by generalizing it into some number `n`:

          `generalize {w}.count 'a' = n at *`"
          generalize w.count 'a' = n at *
          Hint "We an now look at at the if statement in our goal: `split_ifs with hs`."
          split_ifs with hs
          · Hint "This inequality is obviously true for any {n}, so let's solve it directly
            with `omega`."
            omega
          ·
            Hint "According to `{hvchars}`, `{s}` is either 'a' or 'b', and `{hs}` states that
            `{s}` is not 'a' - therefore, `{s}` must be 'b'! Let's show this as a new hypothesis:

            `have hsb : {s} = 'b'`"
            have hsb : s = 'b'
            · Hint "Let's remove the unrequired elements: `clear {honlyas} {n}`."
              clear honlyas n
              Hint "We want to mutate `{hvchars}` into a form where it essentially directly states
              that `{s}` is either 'a' or 'b', so that `simp_all` can take care of the rest.

              Start with `rw [Word.chars] at {hvchars}`."
              rw [Word.chars] at hvchars
              Hint "We can apply a preexisting theorem that shows how unions interact with subsets:

              `apply Set.union_subset_iff.mp at {hvchars}`"
              apply Set.union_subset_iff.mp at hvchars
              Hint "From here on out, the proof state contains enough information that `simp_all`
              will close the goal."
              simp_all
            Hint "The new hypothesis `{hsb}` has added sufficient information to our proof state
            that another `simp_all` will close the goal now."
            simp_all
      -- now we can proceed with the rest of the proof
      -- mind that our main hypotheses right now are honlyas and hatleastonea,
      -- and those reflect the steps in the proof that we worked through first
      Hint "We can now work through the main step of the proof. We want to show a negated
      statement. For a statement `φ`, its negation `¬φ` will actually be equivalent to
      `φ → False` in Lean, so our goal is actually an implication right now. We therefore want to
      proceed by introducing the antecedent: `intro hin`."
      intro hin
      Hint "Let's simplify the newly introduced hypothesis so it's in a form that's more useful to
      us: `simp [Word.pow, cat_eps] at {hin}`."
      simp [Word.pow, cat_eps] at hin
      -- another big rewrite
      Hint "To make several of our hypotheses easier to read, let's proceed with another
      simplification: `simp_all [cat_assoc, {z}]`."
      simp_all [cat_assoc, z]
      Hint "After this last `simp_all`, our proof state contains some hypotheses that our no longer
      necessary. Let's remove them with `clear {hlenlower} {hzinanbn} {hv} {hpos} {z}`."
      clear hlenlower hzinanbn hv hpos z
      Hint "Our hypothesis `{hin}` states that `uvvw` is a word in the language `aⁿbⁿ`. Let's
      understand what this means exactly with `simp [anbn_lang, anbn] at {hin}`."
      simp [anbn_lang, anbn] at hin
      Hint "Since `uvvw` is in `aⁿbⁿ`, there must be some `n` such that `uvvw = aⁿbⁿ`. Let's access
      this `n` with `rcases {hin} with ⟨m, hm⟩`."
      rcases hin with ⟨m, hm⟩
      Hint "Our goal is to show some sort of contradiction now. The idea is that due to `{hm}`, the
      number of a's and b's in `uvvw` has to be equal. But according to `{hcons}`, `{honlyas}`,
      and `{hatleastonea}`, those counts have to be different!

      Let's show the first statement now:
      `have heven : ({u} ∘ {v} ∘ {v} ∘ {w}).count 'a' = ({u} ∘ {v} ∘ {v} ∘ {w}).count 'b'`"
      have heven : (u ∘ v ∘ v ∘ w).count 'a' = (u ∘ v ∘ v ∘ w).count 'b'
      · Hint "This statement should follow quite directly from `{hm}`, but is a little convoluted
        to prove manually, so we want to employ `simp` once again.
        Let's open by rewriting with `{hm}`: `rw [{hm}]`."
        rw [hm]
        Hint "Remember that we stated the lemma `cat_count` to handle counts of concatenations,
        and further `pow_count` to state that #ₐ(aⁿ) = n. These two facts are obviously enough to
        show the goal right now, so let's just close it directly with
        `simp [cat_count, pow_count]`."
        simp [cat_count, pow_count]
      Hint "The more involved proof will be to use the previously proven hypotheses to show
      that the number of a's in `{u}{v}{v}{w}` differs from the number of b's.
      We first want to show that `{u}{v}{w}` indeed has the same amount of a's and b's.

      `have hcount : ({u} ∘ {v} ∘ {w}).count 'a' = ({u} ∘ {v} ∘ {w}).count 'b'`"
      have hcount : (u ∘ v ∘ w).count 'a' = (u ∘ v ∘ w).count 'b'
      · Hint "This is based on the fact that `{u}{v}{w} = aⁿbⁿ`, so let's substitute it back with
        `rw [← {hcons}]`."
        rw [← hcons]
        Hint "Our proof state is almost exactly the same as at the end of our previous hypothesis
        `heven`, so the lemmas `cat_count` and `pow_count` are essentially enough to solve the
        goal:"
        simp [cat_count, pow_count]
      Hint "Since both `{u}{v}{w}` and `{u}{v}{v}{w}` have the same count of a's and b's, {v} must
      have the same count as well:

      `have hveqcount : {v}.count 'a' = {v}.count 'b'`"
      have hveqcount : v.count 'a' = v.count 'b'
      · Hint "The two hypotheses that the goal should intuitively follow from are `{hcount}` and
        `{heven}`, so let's transform them into sums with `simp [cat_count] at hcount heven`."
        simp [cat_count] at hcount heven
        Hint "This is now essentially just a simple arithmetic problem, so let's close the goal
        with `omega`."
        omega
      Hint "The previous hypotheses we showed were only steps to get to {hveqcount}; to have a
      clearer view of what we actually need, let's remove them again:
      `clear {heven} {hcount} {hm} {m} {hcons}`."
      clear heven hcount hm m hcons
      Hint "The contradiction we now receive boils down to the fact that according to `{hveqcount}`,
      `{v}` contains as many a's as b's, but according to `{honlyas}` and `{hatleastonea}`, that
      number should be different.

      At this point our hypotheses contain enough information that `simp_all` or `omega` will
      close the goal, but if you want you can try to go for a more manual approach."
      simp_all

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
