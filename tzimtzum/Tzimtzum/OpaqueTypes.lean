import Tzimtzum.State

/-!
# Shared opaque sort aliases for the TzimtzumV4 check modules

Every `Check*.lean` monomorphises the parametric state at the same opaque sorts and the
corresponding `KSt` abbreviation. Defined once here so each check module can import it
rather than re-declaring them (which conflicts when several check modules are co-imported
in the aggregator or in `Audit.lean`).

The sorts stay **type parameters** on `St` rather than being declared opaque globally: the
Aeneas/Charon-extracted refinement (`argus/formal-lean/`) lives over concrete
`String`-backed id types and instantiates the sort-polymorphic soundness bundle at *its*
sorts. Monomorphising at `KSt` is just one instantiation, the one the `#kav_check` audit
prints axioms for.

Two V3 sorts are gone — `KIssuer` with the retired issuer relations (architecture §9) and
`KInstr` with `load_instruction` — and six are new: challenges, attestations, crossings,
assignment digests, policy digests, and content hashes.
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
