import RrLean.RiemannRochV2.SerreDuality.P1Specific.RatFuncPairing
import RrLean.RiemannRochV2.SerreDuality.DimensionCore
import RrLean.RiemannRochV2.SerreDuality.P1Specific.DimensionScratch
import RrLean.RiemannRochV2.SerreDuality.P1Specific.RatFuncFullRR

/-!
# Smoke Test for Riemann-Roch P¹ Critical Path

This file serves as a build hygiene guardrail. If this file compiles, then:
1. All critical-path modules for RR-for-P¹ are connected in the import graph
2. Lake is actually building them

To verify the proof is sorry-free, run:
```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
```

If `sorryAx` appears in the output, the proof chain uses sorries.
-/

namespace RiemannRochV2.Smoke

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq Fq]

-- Check that the main theorem is accessible
#check @ell_ratfunc_projective_eq_deg_plus_one
#check @ell_ratfunc_projective_single_linear
#check @RRSpace_ratfunc_projective_single_linear_finite

-- Check finiteness instance is properly registered
example (α : Fq) (n : ℕ) : Module.Finite Fq
    (RRSpace_ratfunc_projective ((n : ℤ) • DivisorV2.single (linearPlace α) 1)) :=
  inferInstance

-- Print axioms to verify no unexpected sorries
-- Note: Expected to see sorryAx until all proofs are filled
#print axioms ell_ratfunc_projective_eq_deg_plus_one
#print axioms ell_ratfunc_projective_single_linear
#print axioms RRSpace_ratfunc_projective_single_linear_finite

end RiemannRochV2.Smoke
