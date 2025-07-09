import Game.Metadata
import Game.FormalLanguages.BasicDefinitions

World "Lemmas"
Level 1

Title "cat_eps"

Introduction "Let's prove a simple lemma: concatenating any word with the empty word should yield the word itself."

Statement cat_eps (w : Regular.Word) : w.cat .ε = w := by
  induction' w with s w ih
  · rw [Regular.Word.cat]
  · rw [Regular.Word.cat, ih]

Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
