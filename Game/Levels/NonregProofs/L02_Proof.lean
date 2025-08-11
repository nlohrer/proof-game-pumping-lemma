import Game.Levels.Lemmas.L12_pow_cons_count_uneq
import Game.Metadata

World "NonregProofs"
Level 2

Title "Proving the nonregularity of aⁿbⁿ"

Introduction "We are finally ready to work through a proof that utilizes the pumping lemma!
The proof on paper is as follows:

Let n > 0; we choose z = aⁿbⁿ ∈ anbn, clearly |z| = 2n > n.
Let u, v, w be words over the alphabet \\{a, b} with z = uvw with |uv| ≤ n
and |v| ≥ 1.
We have to show that there is i ∈ ℕ such that uvⁱw ∉ aⁿbⁿ.
Since |uv| ≤ n and the first n symbols of z are a's, we know that there are no b's
in v.
Since |v| ≥ 1, there must be at least one a in v.
So `#a(v) ≠ #b(v)`.
We show that uvvw ∉ aⁿbⁿ by contradiction, so let us assume uvvw ∈ aⁿbⁿ.
This directly means #a(uvvw) = #b(uvvw); since the count of a symbol in a word
is just the sum of its counts in all its subwords, we directly get the equality
`#a(u) + #a(v) + #a(v) + #a(w) = #b(u) + #b(v) + #b(v) + #b(w)`.
Since uvw = z ∈ aⁿbⁿ, we also have #a(uvw) = #b(uvw), leading to the equality
`#a(u) + #a(v) + #a(w) = #b(u) + #b(v) + #b(w)`.
Subtracting the latter equality from the former yields `#a(v) = #b(v)`.
But that is a contradiction to `#a(v) ≠ #b(v)`.
Therefore, aⁿbⁿ is not regular.

We will want to replicate the structure of the proof in Lean, but it will turn out
that some of the steps are far more difficult to realize than on paper. Therefore,
we will mostly guide you through each of the individual steps; you should therefore
try to follow the instructions closely, as later steps might be contingent on earlier
ones so that the proof state is in a fitting form.
"

namespace Regular

/-- Within the context of our proof, this lemma shows that the characters contained in v
are either 'a' or 'b'. -/
lemma v_subset_ab {z u v w : Word} {n : ℕ} (hz : z = ('a' ^ n) ∘ 'b' ^ n) (hcons : z = u ∘ v ∘ w) :
    v.chars ⊆ {'a', 'b'} := by
  have hzinanbn : z ∈ anbn := by use n
  have hzcharsinab := anbn_lang.word_constraint z hzinanbn
  have hsub : v.chars ⊆ z.chars := by
    have hleft := cat_char_subset_left v w
    have hright := cat_char_subset_right u (v ∘ w)
    rw [hcons]
    intro c hc
    exact hright (hleft hc)
  exact subset_trans hsub hzcharsinab

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
  Hint "`use z`"
  use z
  Hint "`constructor` will split the conjunction into separate proofs."
  constructor
  · Hint "We need to show that the word we have chosen is actually contained
    in the language aⁿbⁿ. We can first unfold the definition with `simp [anbn_lang, anbn]`."
    simp [anbn_lang, anbn]
    Hint (hidden := true) "`use {n}` closes the goal immediately."
    use n
  · Hint "We once again use `constructor` to handle the conjunction."
    constructor
    · Hint "We need to show that the length of z is indeed greater than n. You can
      `rw` or simp step by step with some of the lemmas that we showed in the previous world,
      and then use the `omega` tactic once you arrive at a proof state of the form
      `n + n > n`."
      Hint (hidden := true) "The exact hypotheses for rewriting that you should use
      are `{hz}`, `cat_len`, `pow_len`, and `pow_len` again."
      rw [hz, cat_len, pow_len, pow_len]
      Hint (hidden := true) "`omega` closes the subgoal."
      omega
    · Hint "We can finally get to the main part of the proof! First of all, we need
      to introduce all the conditions that we also introduce in the paper proof:

      `intro u v w hcons hlenlower hv`"
      intro u v w hcons hlenlower hv
      Hint "Let's look at our hypotheses:
       - `{u}`, `{v}`, and `{w}` are the newly introduced words
       - `hcons` states that `{z} = {u}{v}{w}`, so we have indeed split `{z}`
       into three subwords
       - `{hlenlower}` represents the assumption `|{u}{v}| ≤ n`
       - `{hv}` represents the other assumption `|{v}| ≥ 1`

      These are all exactly the syme assumptions that we introduced at this point
      in our proof!

      We now need to provide a suitable `i`; in the paper proof we chose `i = 2`,
      so let's `use 2`."
      use 2
      Hint "In our paper proof, we made an argument for why there are no b's in `{v}`. For our formalization, let's have this as a separate hypothesis:

      `have hnobs : {v}.count 'b' = 0`"
      have hnobs : v.count 'b' = 0
      · Hint "Let's simplify the entire proof state with
        `simp_all only [gt_iff_lt, {z}, ↓Char.isValue]`"
        simp_all only [gt_iff_lt, z, ↓Char.isValue]
        Hint "The argument in our proof works to show that there are no b's in
        `uv`. Let's show that first: `have huv : (u ∘ v).count 'b' = 0`."
        have huv : (u ∘ v).count 'b' = 0
        · Hint "We need to utilize the associativity that we proved earlier:

          `rw [← Word.cat_assoc] at hcons`

          Following that, use the tactic `symm at {hcons}`"
          rw [← cat_assoc] at hcons
          symm at hcons
          Hint "For this specific situation, we have already proved the lemma `pow_cons_count_uneq`,
          so you can finish the subproof with

          `apply pow_cons_count_uneq 'a' 'b'
          (ne_of_beq_false rfl) {n} ({u} ∘ {v}) {w} ('b' ^ {n}) {hcons} {hlenlower}`"
          apply pow_cons_count_uneq 'a' 'b' (ne_of_beq_false rfl) n (u ∘ v) w ('b' ^ n) hcons hlenlower
        Hint "We can now use the fresh hypothesis `{huv}`:

        `exact (@Word.cat_count_zero 'b' {u} {v} {huv}).right`"
        exact (@cat_count_zero 'b' u v huv).right
      Hint "For the next step of our proof, we showed that `{v}` contained at least
      one `'a'`. This will unfortunately be much more involved to show!"
      have hatleastonea : v.count 'a' > 0
      · Hint "Since `{v}` is a subword of `{z}`, and `{z} ∈ aⁿbⁿ`, it is obvious that the
        characters contained in `{v}` have to either be `'a'` or `'b'`. Showing this is a slightly
        involved proof since it involves some manual handling of sets - therefore, we have
        already provided this hypothesis in the form of the lemma `v_subset_ab`:

        `have hvchars := v_subset_ab {hz} {hcons}`"
        have hvchars := v_subset_ab hz hcons
        Hint "We have a lot of unnecessary hypotheses, so let's remove them:

        `clear {hlenlower} {hcons} {hz} {u} {w} {z} {hpos} {n}`"
        clear hlenlower hcons hz u w z hpos n
        Hint "The fact that v contains no a's should follow quite obviously from
        {hnobs} and {hvchars}.

        We still need to do the rest of the work to show our statement. Let's pattern match
        on `{v}` with `rcases v with _ | ⟨s, w⟩`."
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

          `generalize {w}.count 'a' = m at *`"
          generalize w.count 'a' = n at *
          Hint "We an now look at at the if statement in our goal: `split_ifs with hs`."
          split_ifs with hs
          · Hint "This inequality is obviously true for any {n}, so let's solve it directly
            with `omega`."
            omega
          ·
            Hint "According to `{hvchars}`, `{s}` is either `'a'` or `'b'`, and `{hs}` states that
            `{s}` is not `'a'` - therefore, `{s}` must be `'b'`! Let's show this as a new hypothesis:

            `have hsb : {s} = 'b'`"
            have hsb : s = 'b'
            · Hint "Let's remove the unrequired elements: `clear {hnobs} {n}`."
              clear hnobs n
              Hint "We want to mutate `{hvchars}` into a form where it essentially directly states
              that `{s}` is either `'a'` or `'b'`, so that `simp_all` can take care of the rest.

              Start with `rw [Word.chars] at {hvchars}`."
              rw [Word.chars] at hvchars
              Hint "We can apply a preexisting theorem that shows how unions interact with subsets:

              `apply Set.union_subset_iff.mp at {hvchars}`"
              apply Set.union_subset_iff.mp at hvchars
              Hint "From here on out, the proof state contains enough information that `simp_all`
              will close the goal."
              simp_all
            Hint "With the new hypothesis `{hsb}` we land in the `if` case in `hnobs`, which
            will be the statement `1 + Word.count {w} 'b' = 0`.

            This statement is a contradiction, so `simp [{hsb}] at {hnobs}` will
            close the goal."
            simp [hsb] at hnobs
      -- mind that our main hypotheses right now are hnobs and hatleastonea,
      -- and those reflect the steps in the proof that we worked through first
      Hint "We can now work through the main step of the proof. We want to show a negated
      statement. For a statement `φ`, its negation `¬φ` will actually be equivalent to
      `φ → False` in Lean, so our goal is actually an implication right now. We therefore want to
      proceed by introducing the antecedent: `intro hin`."
      intro hin
      Hint "Let's simplify the newly introduced hypothesis so it's in a form that's more useful to
      us: `simp [Word.pow, cat_eps] at {hin}`."
      simp [Word.pow, cat_eps] at hin
      Hint "To make several of our hypotheses easier to read, let's proceed with another
      simplification: `simp_all [cat_assoc, {z}]`."
      simp_all [cat_assoc, z]
      Hint "After this last `simp_all`, our proof state contains some hypotheses that our no longer
      necessary. Let's remove them with `clear {hlenlower} {hv} {hpos} {z}`."
      clear hlenlower hv hpos z
      Hint "Our hypothesis `{hin}` states that `uvvw` is a word in the language `aⁿbⁿ`. Let's
      understand what this means exactly with `simp [anbn_lang, anbn] at {hin}`."
      simp [anbn_lang, anbn] at hin
      Hint "Since `uvvw` is in `aⁿbⁿ`, there must be some `n` such that `uvvw = aⁿbⁿ`. Let's access
      this `n` with `rcases {hin} with ⟨m, hm⟩`."
      rcases hin with ⟨m, hm⟩
      Hint "Our goal is to show some sort of contradiction now. The idea is that due to `{hm}`, the
      number of a's and b's in `uvvw` has to be equal. But according to `{hcons}`, `{hnobs}`,
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
      `{v}` contains as many a's as b's, but according to `{hnobs}` and `{hatleastonea}`, that
      number should be different.

      At this point our hypotheses contain enough information that `simp_all` or `omega` will
      close the goal, but if you want you can try to go for a more manual approach."
      simp_all

Conclusion "This last message appears if the level is solved."
