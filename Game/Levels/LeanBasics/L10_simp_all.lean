import Game.Metadata

World "LeanBasics"
Level 10

Title "simp_all"

Introduction "
# simp_all
`simp_all` is similar to `simp`, but applies simplification to the goal
and all hypotheses several times until they can not get simplified further."

Statement (h : x = 2) : x = 2 := by
  Hint "`simp_all` closes the goal immediately."
  simp_all

Conclusion "As the name implies, `simp_all` can be useful not just to try
and solve the goal directly, but also to simplify the proof state overall,
which can make it easier to understand how one should proceed with the proof."

NewTactic simp_all
OnlyTactic
  simp_all
