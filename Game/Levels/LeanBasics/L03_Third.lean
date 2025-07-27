import Game.Metadata

World "LeanBasics"
Level 3

Title "rw"

Introduction "
# rw
In this level, we'll be looking at...
"

Statement (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can either abc start using"
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw
OnlyTactic
  rw
