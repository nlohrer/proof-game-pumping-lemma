import Game.Metadata

World "Lemmas"
Level 1

Title "Introduction: Words"

Introduction "
# Words
Formal languages consist of words over some alphabet Σ.
They are essentially strings consisting of symbols (or characters) in the alphabet.
For instance, for an alphabet `Σ = {a, b, c}`, `abc`, `aabba`, and `c`
will be words over that alphabet.
The empty word `ε` is also considered a word.

From this, our definition of a word in Lean arises:
```
inductive Word where
  | ε
  | cons (s : Char) (w : Word)
```

This is an inductive definition: a word is either the empty word `ε`, or
some symbol together with the rest of the word.
For example, the word `c` would look like
`Word.cons 'c' Word.ε`
and the word `abc` would look like
`Word.cons 'a' (Word.cons 'b' (Word.cons ('c' Word.ε)))`

# Concatenation
We can directly introduce the definition for concatenation of words:
For words `x` and `y`, the concatenation `xy` just consists of the symbols
of both words directly pasted in succession.
For example, if `x = ab` and `y = cbc`, then `xy = abcbc`.

In Lean, our definition looks like this:
```
def Word.cat (x y : Word) : Word :=
  match x with
 | .ε => y
 | .cons s x => .cons s (x.cat y)
```
We also introduce the notation `x ∘ y` in Lean to signify the concatenation `xy`.

To show how the definition for `Word.cat` is reasonable, let's show that
the concatenation `ab ∘ c` indeed yields the word `abc`.
"
namespace Regular
TheoremTab "cat"

/-- Concatenating a word with ε yields the original word. -/
TheoremDoc Regular.cat_eps as "cat_eps" in "cat"

/--
```
inductive Word where
  | ε
  | cons (s : Char) (w : Word)
```

A word over an alphabet, i.e. a string of symbols from that alphabet.
-/
DefinitionDoc Regular.Word as "Word"

/-- Concatenation of words: for two words w₁ and w₂, the concatenation w₁ and w₂ yields w₁w₂.

```
def Word.cat (x y : Word) : Word :=
  match x with
 | .ε => y
 | .cons s x => .cons s (x.cat y)
```
-/
DefinitionDoc Regular.Word.cat as "Word.cat"

NewDefinition Regular.Word Regular.Word.cat

Statement : (Word.cons 'a' (Word.cons 'b' .ε)) ∘ (Word.cons 'c' .ε) = Word.cons 'a' (Word.cons 'b' (Word.cons 'c' .ε)) := by
  Hint "Solving this goal is merely a matter of rewriting with `Word.cat`
  several times, so `rw [Word.cat, Word.cat, Word.cat]` or `simp [Word.cat]`
   will solve the goal.

  If you want, you can also just apply the rewrites separately and observe
  how each rewrite step adheres to the inductive definition of `Word.cat`."
  simp [Word.cat]

Conclusion "Since it is an integral part of the pumping lemma, concatenation
will feature heavily in the upcoming levels."
