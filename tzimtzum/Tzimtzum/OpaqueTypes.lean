import Tzimtzum.Invariants

/-! # Shared opaque type aliases for TzimtzumV2 check modules

All `Check*.lean` files monomorphise the parametric state at the same seven
opaque sorts and the corresponding `KSt` abbreviation.  This module defines them
once so each check module can `import Tzimtzum.OpaqueTypes` and avoid
re-declaring them (which causes conflicts when multiple check modules are
co-imported in the aggregator or in `Audit.lean`).
-/

namespace Tzimtzum

opaque KAgent  : Type
opaque KTool   : Type
opaque KInv    : Type
opaque KCap    : Type
opaque KEgress : Type
opaque KIssuer : Type
opaque KInstr  : Type

abbrev KSt := St KAgent KTool KInv KCap KEgress KIssuer KInstr

end Tzimtzum
