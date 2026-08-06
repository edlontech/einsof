import Tzimtzum.State

/-!
# Opaque sort aliases for verification modules

The `K*` types instantiate the polymorphic state with opaque identifiers for closed-system
verification. `KSt`, `KSnapshot`, `KPending`, and `KChallengeScope` are abbreviations at that
instantiation; the generic soundness theorems apply to any choice of sort parameters.
-/

namespace Tzimtzum

opaque KAgent      : Type
opaque KTool       : Type
opaque KInv        : Type
opaque KCap        : Type
opaque KEgress     : Type
opaque KChallenge   : Type
opaque KAttest      : Type
opaque KCrossing    : Type
opaque KAssignment  : Type
opaque KPolicy      : Type
opaque KContentHash : Type

abbrev KSt :=
  St KAgent KTool KInv KCap KEgress KChallenge KAttest KCrossing KAssignment KPolicy
    KContentHash

/-- The snapshot type at the audit sorts. -/
abbrev KSnapshot := ActionPolicySnapshot KTool KCap KEgress KPolicy

/-- The pending-record type at the audit sorts. -/
abbrev KPending := PendingInvocation KAgent KTool KCap KEgress KAttest KPolicy

/-- The challenge-scope type at the audit sorts. -/
abbrev KChallengeScope := ChallengeScope KAgent KTool KCap KEgress KChallenge KPolicy KContentHash

end Tzimtzum
