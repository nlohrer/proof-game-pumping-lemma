import Game.Levels.LeanBasics
import Game.Levels.Lemmas
import Game.Levels.NonregProof

Dependency LeanBasics → Lemmas
Dependency Lemmas → NonregProof

-- Here's what we'll put on the title screen
Title "Proof Game for the Pumping Lemma"
Introduction
"
# A Proof Game for the Pumping Lemma

Welcome to the proof game for the pumping lemma!
This game aims to teach you the basics of working through
non-regularity proofs for regular languages using the pumping lemma.

Due to the somewhat complex nature of such proofs we assume some base familiarity with Lean.
Nonetheless, since we give optional hints for every single step required to go
through all the levels, this game might still be of some use to you even if you
have not worked with Lean before.

The first world offers a refresher on the tactics we are going to need for this game.
"

Info "
This game is part of my Bachelor's thesis at LMU Munich.

The [original code can be found on github](https://github.com/nlohrer/proof-game-pumping-lemma)
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "A proof game for the pumping lemma."
CaptionLong "In this game you learn how to work through non-regularity proofs for regular languages
in Lean by applying the pumping lemma."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Shows warnings if it found a problem with your game. -/
MakeGame
