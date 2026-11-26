import Screening
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Build-time audit of the transitive dependencies of every project theorem.
The names are read from the environment rather than a hand-maintained sample. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  let mut checked := 0
  let mut used : List Name := []
  for (name, decl) in env.constants.toList do
    if (`Screening).isPrefixOf (privateToUserName name) then
      match decl with
      | .axiomInfo _ => throwError "Project axiom: {name}"
      | .thmInfo _ =>
        checked := checked + 1
        for dep in ← collectAxioms name do
          unless allowed.contains dep do
            throwError "Unexpected axiom in {name}: {dep}"
          unless used.contains dep do used := dep :: used
      | _ => pure ()
  unless checked > 0 do throwError "No project theorems found"
  logInfo m!"Audited {checked} theorem declarations (including auxiliary declarations). Axioms used: {used}"
