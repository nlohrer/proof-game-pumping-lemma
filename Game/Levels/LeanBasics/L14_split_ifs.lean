import Game.Metadata

World "LeanBasics"
Level 14

Title "split_ifs"

Introduction "
# split_ifs
The tactic `split_ifs` allows us to handle `if` statements in our goal."

Statement : if true then true else false := by
  Hint "Use `split_ifs with h`."
  split_ifs with h
  · Hint "`rfl` closes the goal."
    rfl
  · Hint "Use `exact h rfl`."
    exact h rfl
Conclusion "Good!"

/- Use these commands to add items to the game's inventory. -/

NewTactic split_ifs
OnlyTactic
  split_ifs
  rfl
  exact
