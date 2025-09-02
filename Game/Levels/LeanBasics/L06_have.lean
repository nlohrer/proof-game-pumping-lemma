import Game.Metadata

World "LeanBasics"
Level 6

Title "have"

Introduction "
# have
Sometimes, we want to construct sub-hypotheses of our own. We can do this with the
`have` tactic."

Statement (A B C : Prop) (hA : A) (hAB : A → B) (hBC : B → C) : C := by
  Hint (strict := true) "We could solve this directly with `apply`, but let's see what it looks
  like when we construct a new hypothesis.

  Looking at `{hAB}` and `{hA}`, it is obvious that `{B}` should follow.
  Introduce the new hypothesis with the following:

  `have hB : {B}`"
  have hB : B
  · Hint "As we can see in the proof state window, we have introduced a new
    goal that we are working towards. Once we have solved our currently
    active goal, we will return back to our main goal, with the freshly
    proved hypothesis at our disposal."
    Hint (hidden := true) "There are several ways of solving this,
    but `exact {hAB} {hA}` will solve the goal directly."
    exact hAB hA
  Hint "As we can see in our proof state, the new hypothesis `hB` is now
  available to us. Let's use it to close out the goal!"
  Hint (hidden := true) "Among other possibilities, `exact {hBC} {hB}` will
  close the goal."
  exact hBC hB

Conclusion "Good!"

NewTactic
  «have»

OnlyTactic
  exact
  apply
  rfl
  «have»
