/- This file was copied from the natural number game on github:
https://github.com/leanprover-community/NNG4/blob/main/Game/Tactic/Have.lean
 -/

/- copied from mathlib. -/
import Lean
-- import Mathlib.Data.Array.Defs

/--
Uses `checkColGt` to prevent

```lean
have h
exact Nat
```

From being interpreted as
```lean
have h
  exact Nat
```
-/
def Lean.Parser.Term.haveIdLhs' : Parser :=
  optional (ppSpace >> ident >> many (ppSpace >>
    checkColGt "expected to be indented" >>
    letIdBinder)) >> optType

namespace Game.Tactic

open Lean Elab.Tactic Meta

syntax "have" Parser.Term.haveIdLhs' : tactic
syntax "let " Parser.Term.haveIdLhs' : tactic
syntax "suffices" Parser.Term.haveIdLhs' : tactic

open Elab Term in
def haveLetCore (goal : MVarId) (name : Option Syntax) (bis : Array Syntax)
  (t : Option Syntax) (keepTerm : Bool) : TermElabM (MVarId × MVarId) :=
  let declFn := if keepTerm then MVarId.define else MVarId.assert
  goal.withContext do
    let n := if let some n := name then n.getId else `this
    let elabBinders k := if bis.isEmpty then k #[] else elabBinders bis k
    let (goal1, t, p) ← elabBinders fun es ↦ do
      let t ← match t with
      | none => mkFreshTypeMVar
      | some stx => withRef stx do
          let e ← Term.elabTerm stx none
          Term.synthesizeSyntheticMVars false
          instantiateMVars e
      let p ← mkFreshExprMVar t MetavarKind.syntheticOpaque n
      pure (p.mvarId!, ← mkForallFVars es t, ← mkLambdaFVars es p)
    let (fvar, goal2) ← (← declFn goal n t p).intro1P
    if let some stx := name then
      goal2.withContext do
        Term.addTermInfo' (isBinder := true) stx (mkFVar fvar)
    pure (goal1, goal2)

elab_rules : tactic
| `(tactic| have $[$n:ident $bs*]? $[: $t:term]?) => do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n (bs.getD #[]) t false
  replaceMainGoal [goal1, goal2]

elab_rules : tactic
| `(tactic| suffices $[$n:ident $bs*]? $[: $t:term]?) => do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n (bs.getD #[]) t false
  replaceMainGoal [goal2, goal1]

elab_rules : tactic
| `(tactic| let $[$n:ident $bs*]? $[: $t:term]?) => withMainContext do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n (bs.getD #[]) t true
  replaceMainGoal [goal1, goal2]
