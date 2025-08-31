import Game.Metadata

World "LeanBasics"
Level 1

Title "rfl"

Introduction "
# Introduction
Let's look at some of the very basics of Lean.

## Proof state
In the middle bottom of the screen, you'll find the proof state, which includes
both the goal of the proof, as well as all objects and assumptions that you may
use to arrive at the proof.

## rfl
The `rfl` tactic closes the goal using reflexivity.
"

Statement : 2 = 2 := by
  Hint "Use `rfl` to close the goal immediately."
  rfl

Conclusion "
Good! `rfl` isn't required very often, but we do need it sometimes."

NewTactic rfl
NewHiddenTactic «sorry»
