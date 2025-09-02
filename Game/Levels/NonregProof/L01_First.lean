import Game.Levels.Lemmas.L12_pow_cons_count_uneq
import Game.Metadata

World "NonregProof"
Level 1

Title "Languages and the Pumping Lemma"

Introduction "
# Introduction
In this level, we introduce a number of definitions.

## Languages
So far, we have been working with individual words made up of arbitrary characters.
We now look at sets of words over a restricted set of characters, which we call *languages*.
The new `Language` definition in your inventory shows how we defined languages for our purposes:
```
structure Language where
  Alphabet : Set Char
  Words : Set Word
  word_constraint : ∀ word ∈ Words, word.chars ⊆ Alphabet
```
One example for a language would be `aⁿbⁿ`, which is the following set over the alphabet `\\{a,b}`:
`{w | ∃ n : ℕ, w = ('a' ^ n) ∘ ('b' ^ n)}`

## Regular languages and the pumping lemma
Our goal in the next level will be to show that `aⁿbⁿ` is not regular.
Regular languages encompass those that can be expressed as DFAs.
Every regular language satisfies the pumping pumping property, which informally states that each word `z` in that language can be
split into subwords `u`, `v`, `w`, with `z = uvw`, such that `uvⁱw` will still be contained in the language
for any `i ∈ ℕ`.
There are some additional aspects to the pumping property, which are all captured in our definition:
```
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
```
"

namespace Regular

/--
```
structure Language where
  Alphabet : Set Char
  Words : Set Word
  word_constraint : ∀ word ∈ Words, word.chars ⊆ Alphabet
```

A language is a set of words over an alphabet.
-/
DefinitionDoc Regular.Language as "Language"

/--
```
def anbn : Set Word := {w | ∃ n : ℕ, w = ('a' ^ n) ∘ ('b' ^ n)}
```

The set aⁿbⁿ, which is differentiated from the corresponding language by the fact
that it is not explicitly defined over a restricted alphabet.
-/
DefinitionDoc Regular.anbn as "aⁿbⁿ (Set)"

/--
```
def anbn : Set Word := {w | ∃ n : ℕ, w = ('a' ^ n) ∘ ('b' ^ n)}
```

The language over the alphabet \{'a', 'b'} consisting of the set of words of the form aⁿbⁿ.
-/
DefinitionDoc Regular.anbn_lang as "aⁿbⁿ"

/--
```
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
```

The pumping property for regular languages states that each sufficiently long
word `z` in a regular language may be split as `z = uvw` with certain restrictions
such that `uvⁱw` will still be in the language for any `i ∈ ℕ`.
-/
DefinitionDoc Regular.pumping_property as "Pumping Property"

NewDefinition Regular.Language Regular.anbn_lang Regular.pumping_property Regular.anbn

#check anbn

Statement :
    (Symbol.pow 'a' 2) ∘ (Symbol.pow 'b' 2) ∈ anbn := by
  Hint "Start with `simp [anbn]`.
  You could also try `rw [anbn]` to replace the definition, but `simp` is nice
  to take care of the `∈` relation in any case."
  simp [anbn]
  Hint (hidden := true) "`use 2` closes the goal."
  use 2

Conclusion "With these new definitions, we can finally try our hand at a non-regularity proof!"
