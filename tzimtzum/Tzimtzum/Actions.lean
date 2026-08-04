import Tzimtzum.Actions.Structural
import Tzimtzum.Actions.Ingest
import Tzimtzum.Actions.Settle
import Tzimtzum.Actions.Invoke
import Tzimtzum.Actions.Cross
import Kav.Transition

/-!
# TzimtzumV4 — the complete 12-action transition system

The registered surface of [[2026-07-24-tzimtzum-v4/architecture|architecture]] §6–§7:
seven structural actions, `ingest`, `begin_invocation`, `authorize_inspected`,
`settle_invocation`, `cross_output`. No V3 action is reachable — the archive is not a build
target, and this list is the *only* place actions become transitions.

Parameters are existentially closed by the `Kav.closeN` helpers, exactly as V3 did; the
per-action check modules (Tasks 7–10) operate on the *unclosed* families, where the
parameters stay universally quantified.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

def system : Kav.TransitionSystem
    (St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash) :=
  { init := initial
    actions :=
      [ ("register_tool",       Kav.close1 register_tool)
      , ("unregister_tool",     Kav.close1 unregister_tool)
      , ("delegate",            Kav.close2 delegate)
      , ("grant_capability",    Kav.close3 grant_capability)
      , ("grant_crossing",      Kav.close4 grant_crossing)
      , ("revoke",              Kav.close2 revoke)
      , ("cascade_revoke",      Kav.close2 cascade_revoke)
      , ("ingest",              Kav.close5 ingest)
      , ("begin_invocation",    Kav.close8 begin_invocation)
      , ("authorize_inspected", Kav.close4 authorize_inspected)
      , ("settle_invocation",   Kav.close7 settle_invocation)
      , ("cross_output",        Kav.close3 cross_output) ] }

end Tzimtzum
