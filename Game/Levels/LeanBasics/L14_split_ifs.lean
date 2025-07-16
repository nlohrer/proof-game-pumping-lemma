import Game.Metadata

World "LeanBasics"
Level 14

Title "split_ifs"

Introduction "
# omega
The tactic `omega` can solve integer and natural linear arithmetic problems."

Statement : if true then true else false := by
  split_ifs with h
  · rfl
  · exact h rfl
Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic split_ifs
OnlyTactic
  split_ifs
  rfl
  exact
