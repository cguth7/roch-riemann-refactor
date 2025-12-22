/-
# Full Adele Ring - Main Import File

This file re-exports from the split files:
- FullAdelesBase.lean: General definitions, basic FqInstance (COMPILES ✅)
- FullAdelesCompact.lean: Compactness, weak approximation (COMPILES ✅, 1 sorry for bound<1 case)

Split for faster incremental builds.
-/

import RrLean.RiemannRochV2.Adelic.FullAdelesBase
import RrLean.RiemannRochV2.Adelic.FullAdelesCompact
