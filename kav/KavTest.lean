-- Aggregator: imports all framework Test modules.
-- Build with: lake build KavTest
--
-- Note: CoreTest is intentionally excluded — it duplicates the Toy/flip/sys definitions
-- already in CheckTest (both are in Kav.Test namespace), causing co-import conflicts.
-- CheckTest covers CoreTest's testing surface by transitively importing Kav.Core.
--
-- The TzimtzumV2 port + its per-action VC checks now live in the `tzimtzum/` project
-- (which requires kav as a library); build them with `lake build TzimtzumTest` there.
import Kav.ActionTest
import Kav.CheckTest
import Kav.ModelCheckTest
import Kav.SolveTest
