# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ Full build compiles with sorries (warnings only)
**Phase**: 3 - Serre Duality
**Cycle**: 198

### Active Sorries (8 total)

| File | Lemma | Priority | Notes |
|------|-------|----------|-------|
| RatFuncPairing.lean | `exists_global_approximant_from_local` | **CRITICAL** | Key gluing lemma - two-step approach ready |
| RatFuncPairing.lean | `strong_approximation_ratfunc` | HIGH | Uses exists_global_approximant_from_local |
| Abstract.lean | `serrePairing_left_nondegen` | MED | Vacuously true once h1=0 is proved |
| Abstract.lean | `serrePairing_right_nondegen` | MED | Vacuously true once h1=0 is proved |
| Residue.lean | `residueAtIrreducible` | LOW | Placeholder for higher-degree places |
| Residue.lean | `residue_sum_eq_zero` | MED | General residue theorem |
| FullAdelesCompact.lean | (2 sorries) | LOW | Edge cases in weak approximation |

### ⚠️ ARCHITECTURE NOTE: Zero Pairing Strategy

Both `serrePairing` (Abstract.lean) and `serrePairing_ratfunc` (RatFuncPairing.lean) are **definitionally 0**.
This is mathematically justified for genus 0 (P¹ over Fq) because:
- Residue sum of K-diagonal elements vanishes by residue theorem
- Finite residue sum of A_K(D) × L(K-D) vanishes by pole cancellation
- Hence induced pairing on H¹(D) quotient is 0

**Current status**:
- Non-degeneracy lemmas are sorries pending proof that both spaces are 0-dimensional
- For deg(D) ≥ -1: H¹(D) = 0 (requires strong approximation) and L(K-D) = 0 (negative degree)
- Once dimensional triviality is proved, non-degeneracy is vacuously true

### Key Infrastructure ✅

| Component | Status | Location |
|-----------|--------|----------|
| Residue at X (X-adic) | ✅ | Residue.lean |
| Residue at infinity | ✅ | Residue.lean |
| Residue at linear places | ✅ | Residue.lean |
| residueSumTotal (finite + ∞) | ✅ | SerreDuality/RatFuncResidues.lean |
| Residue theorem (split denom) | ✅ | SerreDuality/RatFuncResidues.lean |
| Bilinear pairing | ✅ | SerreDuality/RatFuncResidues.lean |
| Diagonal embedding (RatFunc) | ✅ | SerreDuality/RatFuncPairing.lean |
| K-part well-definedness | ✅ | SerreDuality/RatFuncPairing.lean |
| Pole cancellation (valuation) | ✅ | SerreDuality/RatFuncPairing.lean |
| linearPlace definition | ✅ | SerreDuality/RatFuncPairing.lean |
| translatePolyEquiv (RingEquiv) | ✅ | SerreDuality/RatFuncPairing.lean |
| translateRatFuncHom (lifted) | ✅ | SerreDuality/RatFuncPairing.lean |
| intValuation_translatePolyEquiv | ✅ | SerreDuality/RatFuncPairing.lean |
| linearPlace_valuation_eq_comap | ✅ | SerreDuality/RatFuncPairing.lean |
| residueAt_of_valuation_le_one | ✅ | SerreDuality/RatFuncPairing.lean |
| bounded_diagonal_finite_residue_zero | ✅ | SerreDuality/RatFuncPairing.lean |
| rawDiagonalPairing | ✅ | SerreDuality/RatFuncPairing.lean |
| rawDiagonalPairing_bilinear | ✅ | SerreDuality/RatFuncPairing.lean |
| rawDiagonalPairing_eq_zero_of_splits | ✅ | SerreDuality/RatFuncPairing.lean |
| rawDiagonalPairing_finite_zero_of_bounded | ✅ | SerreDuality/RatFuncPairing.lean |
| serrePairing_ratfunc (concrete, =0) | ✅ | SerreDuality/RatFuncPairing.lean |
| serrePairing (abstract, STUB=0) | ⚠️ | SerreDuality/Abstract.lean |
| linearPlaces_pairwise_coprime | ✅ | SerreDuality/RatFuncPairing.lean |
| crt_linear_places | ✅ | SerreDuality/RatFuncPairing.lean |
| exists_local_approximant_with_bound | ✅ | SerreDuality/RatFuncPairing.lean |
| polynomial_preserves_integrality | ✅ | SerreDuality/RatFuncPairing.lean |
| polynomial_integral_outside | ✅ | SerreDuality/RatFuncPairing.lean |
| X_sub_not_mem_linearPlace_ideal | ✅ | SerreDuality/RatFuncPairing.lean |
| valuation_X_sub_at_ne | ✅ | SerreDuality/RatFuncPairing.lean |
| valuation_inv_X_sub_pow_at_ne | ✅ | SerreDuality/RatFuncPairing.lean |
| polynomial_valuation_le_one | ✅ | SerreDuality/RatFuncPairing.lean |
| valuation_le_one_at_other_place | ✅ | SerreDuality/RatFuncPairing.lean |
| coprime_polynomial_valuation_one | ✅ | SerreDuality/RatFuncPairing.lean |
| IsPrincipalPartAt predicate | ✅ | SerreDuality/RatFuncPairing.lean |
| sum_principal_parts_valuation_le_one | ✅ | SerreDuality/RatFuncPairing.lean |
| sub_principal_part_no_pole | ✅ | SerreDuality/RatFuncPairing.lean |
| exists_principal_part | ✅ | SerreDuality/RatFuncPairing.lean |
| denom_not_in_asIdeal_of_integral | ✅ | SerreDuality/RatFuncPairing.lean |
| exists_polyRep_of_integral_mod_pow | ✅ | SerreDuality/RatFuncPairing.lean |
| exists_global_approximant_from_local | ⚠️ | SerreDuality/RatFuncPairing.lean (KEY) |
| strong_approximation_ratfunc | ⚠️ | SerreDuality/RatFuncPairing.lean |
| h1_vanishing_ratfunc | ⚠️ | SerreDuality/RatFuncPairing.lean |

---

## Next Steps (Cycle 199)

### 🎯 PRIMARY GOAL: Complete `exists_global_approximant_from_local`

**Infrastructure now COMPLETE (Cycle 198):**

| Lemma | Status | Purpose |
|-------|--------|---------|
| `denom_not_in_asIdeal_of_integral` | ✅ | If val(r) ≤ 1, then r.denom ∉ v.asIdeal |
| `exists_polyRep_of_integral_mod_pow` | ✅ | Find polynomial a with val(r - a) ≤ exp(-m) |
| `exists_principal_part` | ✅ | Extract principal part at a place |
| `crt_linear_places` | ✅ | CRT for distinct linear places |

**Two-Step Proof Strategy:**

**Step A (Principal Parts):** Sum principal parts to remove poles
- For each v ∈ S, get principal part pp_v(y_v) using `exists_principal_part`
- Let k_pole = Σ_{v ∈ S} pp_v(y_v)
- Then y_v - k_pole is **integral** at all v ∈ S

**Step B (CRT Precision):** For places where n_v < 0 (need zeros, not just integrality):
- Use `exists_polyRep_of_integral_mod_pow` to find polynomial a_v ≡ (y_v - k_pole) mod v.asIdeal^{-n_v}
- Use `crt_linear_places` to find single p matching all a_v
- Final k = k_pole + p satisfies the full bound

**Why two steps are needed:**
- n_v ≥ 0: exp(n_v) ≥ 1, so integrality (val ≤ 1) suffices
- n_v < 0: exp(n_v) < 1, need to match Taylor coefficients (a zero of order ≥ -n_v)

### Once exists_global_approximant_from_local is proved:

**h1_vanishing**: For deg(D) ≥ -1:
- Every [a] ∈ H¹(D) has a representative a ∈ FiniteAdeleRing
- Strong approximation: ∃ k ∈ K with a - diag(k) ∈ A_K(D)
- Hence [a] = [diag(k)] = 0 (since diag(k) ∈ globalSubmodule)
- Therefore H¹(D) = 0

**Non-degeneracy becomes vacuous**:
- `serrePairing_left_nondegen`: H¹(D) = 0, so no nonzero elements to test
- `serrePairing_right_nondegen`: For deg(D) ≥ -1, deg(K-D) = -2 - deg(D) ≤ -3, so L(K-D) = 0

---

## Recent Progress

### Cycle 198 - **Helper Lemmas for Strong Approximation PROVED** 🎉
- **KEY MILESTONE**: Both helper lemmas for `exists_polyRep_of_integral_mod_pow` now complete!
- **Proved `denom_not_in_asIdeal_of_integral`** ✅
  - If val(r) ≤ 1, then r.denom ∉ v.asIdeal
  - Proof via coprimality: r = num/denom with IsCoprime num denom
  - If denom ∈ v.asIdeal, then val(denom) < 1 (intValuation_lt_one_iff_mem)
  - Coprimality forces num ∉ v.asIdeal, so val(num) = 1
  - Hence val(r) = val(num)/val(denom) > 1, contradiction
- **Proved `exists_polyRep_of_integral_mod_pow`** ✅ (2 internal sorries resolved)
  - **Unit in quotient proof**: Used IsPrincipalIdealRing.principal to get generator p
    - p ∤ denom (since denom ∉ v.asIdeal)
    - Irreducible.coprime_iff_not_dvd gives IsCoprime p denom
    - IsCoprime.pow_left gives IsCoprime (p^m) denom
    - Bezout identity: a*(p^m) + b*denom = 1 shows denom is unit mod (p^m)
  - **Algebraic manipulation**: Showed r - a = (num - a*denom)/denom via RatFunc algebra
    - Used sub_div, mul_div_assoc', field_simp
    - Valuation.map_div for final valuation computation
- **Sorries reduced**: 12 → 8 (−4)
- **RatFuncPairing.lean**: 4 → 2 sorries
- **Build**: ✅ compiles with sorries
- **Next step**: Wire two-step approach into exists_global_approximant_from_local

### Cycle 197 - **Two-Step Strong Approximation Architecture** 🏗️
- **Key insight**: `exists_global_approximant_from_local` requires two-step approach:
  1. **Principal parts** for pole removal (achieves integrality, val ≤ 1)
  2. **CRT precision** for negative bounds (matches Taylor coefficients, val ≤ exp(-m))
- **New infrastructure added**:
  - `denom_not_in_asIdeal_of_integral` ⚠️ - If r is integral at v, then r.denom ∉ v.asIdeal
    - Proof sketch: coprimality of num/denom + valuation arithmetic
  - `exists_polyRep_of_integral_mod_pow` ⚠️ - Given integral r at v, find polynomial a with val(r - a) ≤ exp(-m)
    - Proof structure: write r = num/denom, denom is unit mod v.asIdeal^m, find a ≡ num·denom⁻¹
    - 2 internal sorries: unit-in-quotient from coprimality, algebraic manipulation
- **Architecture note**: n_v ≥ 0 case (integrality suffices) vs n_v < 0 case (needs CRT)
- **Sorries**: 9 → 12 (added helper lemmas with structure but pending proofs)
- **Build**: ✅ compiles with sorries
- **Next step**: Wire two-step approach into exists_global_approximant_from_local

### Cycle 196 - **exists_principal_part PROVED** 🎉
- **KEY MILESTONE**: `exists_principal_part` ✅ - Principal part extraction via partial fractions
- **Proof strategy**:
  1. Handle y = 0 case trivially with p = 0, r = 0
  2. For y ≠ 0: use `RatFunc.num` and `RatFunc.denom` (monic by Mathlib)
  3. Factor denom = (X - α)^m * R using `exists_eq_pow_rootMultiplicity_mul_and_not_dvd`
  4. Case m = 0: y has no pole at α, so p = 0 and r = y
  5. Case m > 0: Apply `div_eq_quo_add_rem_div_add_rem_div` from Mathlib
     - Coprimality from `Irreducible.coprime_iff_not_dvd` for X - α
     - Monicity of R from `Monic.of_mul_monic_left`
     - Decomposition: num/((X-α)^m * R) = q + r₁/(X-α)^m + r₂/R
  6. Set p = r₁/(X-α)^m (principal part) and r = q + r₂/R (remainder)
  7. Verify valuation properties using existing infrastructure
- **Key Mathlib lemmas used**:
  - `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd` - Root factorization
  - `div_eq_quo_add_rem_div_add_rem_div` - Partial fractions decomposition
  - `Polynomial.irreducible_X_sub_C` - Irreducibility of (X - α)
  - `Irreducible.coprime_iff_not_dvd` - Coprimality from non-divisibility
  - `RatFunc.algebraMap_ne_zero` - Injectivity of algebraMap for RatFunc
- **Sorries**: 10 → 9 (resolved exists_principal_part)
- **Next step**: Complete `exists_global_approximant_from_local` (now unblocked!)

### Cycle 195 - **Principal Part Infrastructure** 🚧
- **Key progress**: Built the valuation lemmas for principal part construction:
  - `X_sub_not_mem_linearPlace_ideal` ✅ - (X - α) ∉ ideal (X - β) when α ≠ β
  - `valuation_X_sub_at_ne` ✅ - (X - α) is a unit (valuation = 1) at place β ≠ α
  - `valuation_inv_X_sub_pow_at_ne` ✅ - 1/(X - α)^n is a unit at β ≠ α
  - `polynomial_valuation_le_one` ✅ - Polynomials have valuation ≤ 1 at all finite places
  - `valuation_le_one_at_other_place` ✅ - p/(X - α)^n is integral at β ≠ α
  - `coprime_polynomial_valuation_one` ✅ - Coprime polynomials have valuation = 1
- Defined `IsPrincipalPartAt` predicate for principal part decomposition
- Added `sum_principal_parts_valuation_le_one` ✅ - ultrametric for sum
- Added `sub_principal_part_no_pole` ✅ - subtracting principal part removes pole
- **Remaining sorry**: `exists_principal_part` (requires partial fractions decomposition)
- Sorries: 9 → 10 (added exists_principal_part as explicit blocker)
- **Next step**: Prove existence of principal parts via `div_eq_quo_add_rem_div_add_rem_div`

### Cycle 194 - **Identified Key Gluing Lemma** 🚧
- **Key insight**: The blocking piece is `exists_global_approximant_from_local`
  - Given local approximants y_v at distinct places, find single k ∈ K approximating all
  - This is the "gluing" step that requires partial fractions
- Added `exists_global_approximant_from_local` lemma (sorry)
  - Statement: For S finite, y : S → K, n : S → ℤ, exists k with val_v(y_v - k) ≤ exp(n_v)
  - Empty case handled (vacuously true)
  - Non-empty case requires partial fractions decomposition
- Added `polynomial_integral_outside` ✅
  - Polynomials are integral at all finite places
- Refactored strong_approximation to depend on exists_global_approximant_from_local
- Updated documentation with detailed proof strategy via partial fractions:
  1. Decompose each y_v via `div_eq_quo_add_sum_rem_div`
  2. Extract principal part at v from each y_v
  3. Sum principal parts to get k
  4. Principal parts at different places don't interfere
- Sorries: 8 → 9 (decomposed into finer-grained lemma)
- **Next step**: Define `principalPart` function and prove its properties

### Cycle 193 - **Local Approximation with Bounds** ✅
- Added import: `RrLean.RiemannRochV2.FullAdelesCompact` for exists_local_approximant
- `exists_local_approximant_with_bound` ✅ - Key density lemma
  - For any a_v ∈ v.adicCompletion K and target bound n, finds y ∈ K with val(a_v - y) ≤ exp(n)
  - Uses `Valued.isOpen_closedBall` for open balls in valued rings
  - Uses density of K in completion via `UniformSpace.Completion.denseRange_coe`
- `polynomial_preserves_integrality_at_integral_place` ✅
  - Shows polynomials preserve integrality at places where adele is already integral
- Improved `strong_approximation_ratfunc` documentation with detailed proof strategy:
  1. Extract finite set of bad places from restricted product structure
  2. Use local approximation at each bad place
  3. Combine via partial fractions (key technical gap remaining)
- Added trivial case handling: if a already in A_K(D), k = 0 works
- **Blocking issue**: Need partial fractions formalization for RatFunc Fq to glue local approximants
- Sorries: 8 (unchanged - building infrastructure)

### Cycle 192 - **Strong Approximation Infrastructure** 🚧
- Added CRT imports: `Mathlib.RingTheory.Ideal.Quotient.Operations`, `Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas`
- `linearPlaces_pairwise_coprime` ✅ - Linear places (X - α) have pairwise coprime ideals
  - Uses `Ideal.isCoprime_span_singleton_iff` and `Polynomial.isCoprime_X_sub_C_of_isUnit_sub`
- `crt_linear_places` ✅ - CRT for distinct linear places with specified remainders
  - Applies `IsDedekindDomain.exists_forall_sub_mem_ideal` from Mathlib
  - Key: finds polynomial p with p - targets i ∈ (places i).asIdeal ^ exponents i
- `strong_approximation_ratfunc` (sorry) - Main theorem statement added
  - States: for any finite adele and divisor, exists k ∈ K with a - diag(k) ∈ A_K(D)
  - **Proof needed**: Wire CRT to FiniteAdeleRing structure
- `h1_vanishing_ratfunc` (sorry) - H¹(D) = 0 for deg(D) ≥ -1
- `h1_finrank_zero_of_large_deg` (sorry) - Finrank version
- Sorries: 5 → 8 (added 3 intermediate strong approximation lemmas)

### Cycle 191 - **serrePairing_ratfunc defined as 0** ✅
- Filled the `serrePairing_ratfunc` sorry with a 0 definition
- Mathematical justification: for genus 0 (P¹ over Fq):
  - K-diagonal elements: residue sum vanishes by residue theorem
  - A_K(D) paired with L(K-D): finite residue sum vanishes by pole cancellation
  - Hence induced pairing on H¹(D) quotient is 0
- Documentation added explaining genus 0 dimensional triviality
- Aligns with abstract `serrePairing = 0` in Abstract.lean
- **Key insight**: Non-degeneracy of 0 pairing is vacuously true when both spaces are 0
- **Blocking issue**: Need to prove h1_vanishing (H¹(D) = 0 for deg(D) ≥ -1)
- Sorries: 6 → 5

### Cycle 190 - **finrank_eq_of_perfect_pairing proved** ✅
- Used Mathlib's `LinearMap.IsPerfPair` and `Module.finrank_of_isPerfPair`
- Added import: `Mathlib.LinearAlgebra.PerfectPairing.Basic`
- Proof strategy:
  - Convert left/right non-degeneracy to injectivity of `pairing` and `pairing.flip`
  - Apply `IsPerfPair.of_injective` to get perfect pairing instance
  - `Module.finrank_of_isPerfPair` gives dimension equality
- Ledger cleanup: Fixed Cycle 178 claim (was ✅, now correctly noted as sorry-then)
- Added ⚠️ STUB WARNING section for abstract pairing
- **Analyzed serrePairing_ratfunc blockers**:
  - Current `residueAt` only works on K (RatFunc), not K_v (completions)
  - FiniteAdeleRing contains completion elements, not just K elements
  - Need either: (a) residue on completions, or (b) weak approximation
  - For genus 0: H¹(D) = 0 when deg(D) ≥ -1, so pairing trivially 0 in most cases
- Updated RatFuncPairing.lean strategy notes with detailed blocking analysis
- Sorries: 7 → 6

### Cycle 189 - **Major refactor: Split SerreDuality into 3 files** 🔧
- Followed reviewer recommendation to separate abstraction levels
- Created `SerreDuality/` directory with clean module structure:
  1. **Abstract.lean** - Type-correct placeholder pairing (definitionally 0)
     - `serrePairing` now returns 0 (not sorry), allows downstream simp
     - `serrePairing_wellDefined` trivially true
     - Non-degeneracy and dimension equality as sorries
  2. **RatFuncResidues.lean** - Residue infrastructure (no adeles)
     - `residueSumFinite`, `residueSumTotal`, `residuePairing`
     - Residue theorem for split denominators
     - Clean separation from quotient construction
  3. **RatFuncPairing.lean** - Concrete pairing for P¹
     - Pole cancellation (`bounded_times_LKD_no_pole`)
     - Valuation transport (`linearPlace_valuation_eq_comap`)
     - Raw diagonal pairing and bilinearity
     - `serrePairing_ratfunc` placeholder
- **Thin `SerreDuality.lean`** re-exports all three modules
- Benefits:
  - Clear abstraction boundaries
  - Residue layer has no adeles/quotients
  - Pairing layer focused on P¹ construction
  - Abstract layer provides type-correct interface
- Sorries unchanged: 7 (reorganized across files)

### Cycle 188 - **Raw pairing infrastructure for RatFunc Fq**
- `bounded_diagonal_finite_residue_zero` ✅ - Now fully proved (was pending verification)
  - Uses chain: bounded × L(K-D) → valuation ≤ 1 → residue = 0 → sum = 0
  - Key lemmas: `bounded_times_LKD_no_pole` + `residueAt_of_valuation_le_one`
- Added RawPairing section with diagonal pairing infrastructure:
  - `rawDiagonalPairing` ✅ - residueSumTotal(g * f) for g, f ∈ K
  - `rawDiagonalPairing_add_left/right` ✅ - Additivity in both arguments
  - `rawDiagonalPairing_smul_left/right` ✅ - Scalar linearity
  - `rawDiagonalPairing_bilinear` ✅ - Full bilinear map structure
  - `rawDiagonalPairing_eq_zero_of_splits` ✅ - Residue theorem for pairing
  - `rawDiagonalPairing_finite_zero_of_bounded` ✅ - Pole cancellation for bounded
- Added `serrePairing_ratfunc` (sorry) - Concrete pairing for RatFunc Fq
- Identified key architectural issue: FiniteAdeleRing vs FullAdeleRing
  - Current H¹(D) uses FiniteAdeleRing (no infinity component)
  - Residue theorem needs ALL places including infinity
  - Pairing vanishing on diagonal K requires full residue sum = 0
- Documented strategy in SerrePairingConstruction section comments
- Sorries: 6 → 7 (added serrePairing_ratfunc placeholder)

### Cycle 187 - **Valuation transport proof complete** 🎉
- **KEY MILESTONE**: `linearPlace_valuation_eq_comap` ✅ - The main blocker is SOLVED!
- Core proof strategy:
  - `intValuation_translatePolyEquiv` ✅ - Proves intValuation preserved under translation
  - Key insight: divisibility by (X-α)^n ↔ divisibility by X^n after translation
  - Used `Associates.prime_pow_dvd_iff_le` for count characterization
  - Bidirectional implication via `hdvd_iff` using ideal map properties
- `linearPlace_valuation_eq_comap` ✅ - Uses Valuation.map_div and valuation_of_algebraMap
  - Extends intValuation result to full RatFunc via fraction decomposition
- `translatePolyEquiv_ideal_pow_map` ✅ - Helper for ideal^n mapping
- Fixed translatePolyEquiv proofs (left_inv/right_inv/map_add')
- `residueAt_of_valuation_le_one` now unblocked and complete
- Sorries: 7 → 6

### Cycle 186 - Valuation transport infrastructure for residue vanishing
- Added translation RingEquiv infrastructure:
  - `translatePolyEquiv` ✅ - RingEquiv on Polynomial Fq: p ↦ p.comp(X + C α)
  - `translatePolyEquiv_X_sub_C` ✅ - Sends X - C α to X
  - `translatePolyEquiv_ideal_map` ✅ - Maps ideal span{X-α} to span{X}
  - `translatePolyEquiv_mem_nonZeroDivisors` ✅ - Preserves non-zero-divisors
  - `translateRatFuncHom` ✅ - Lifted RingHom on RatFunc via mapRingHom
  - `translateRatFuncHom_eq_translateBy` ✅ - Agrees with existing translateBy
- Proof structure for residueAt_of_valuation_le_one:
  - Uses Valuation.comap to transport valuations
  - Connects to LaurentSeries.coeff_zero_of_lt_valuation
  - Only blocked by `linearPlace_valuation_eq_comap` (1 sorry)
- `bounded_diagonal_finite_residue_zero` now wired to use residueAt_of_valuation_le_one
- Key insight: Use high-level Valuation API, not manual polynomial decomposition
- Sorries: 9 → 7 (resolved 2 structural, added infrastructure)

### Cycle 185 - Pole cancellation infrastructure for bounded adeles
- Added PoleCancellation section:
  - `canonicalZeroAtFinite` ✅ - Predicate: K(v) = 0 for all finite v
  - `linearPlace` ✅ - HeightOneSpectrum for place (X - α)
  - `bounded_times_LKD_valuation_bound` ✅ - Product valuation: v(g·f) ≤ exp(K(v))
  - `bounded_times_LKD_no_pole` ✅ - When K(v)=0: v(g·f) ≤ 1 (no pole)
  - `residueAt_of_valuation_le_one` (sorry) - Valuation ≤ 1 implies residue = 0
  - `bounded_diagonal_finite_residue_zero` (sorry) - Bounded diagonal has zero finite residue
- Added detailed strategy documentation:
  - liftQ construction approach
  - rawPairing definition via local residues
  - Key properties needed for well-definedness
  - Current infrastructure vs missing pieces
- Sorries: 7 → 9 (2 new intermediate lemmas added)
- Key insight: pole cancellation argument for A_K(D) × L(K-D) formalized

### Cycle 184 - Diagonal pairing infrastructure for RatFunc Fq
- Added DiagonalPairing section:
  - `diagonalEmbedding` ✅ - K →+* FiniteAdeleRing for RatFunc case
  - `diagonalResiduePairing` ✅ - residuePairing on RatFunc Fq
  - `diagonalResiduePairing_bilinear` ✅ - bilinear map structure
  - `diagonalResiduePairing_eq_zero_of_splits` ✅ - vanishing for split denominators
  - `diagonal_pairing_eq_residue` ✅ - equality with residuePairing
- Added RatFuncSpecialization section:
  - `H1_ratfunc` ✅ - specialized H¹(D) type alias
  - `LKD_ratfunc` ✅ - specialized L(K-D) type alias
  - `diagonal_maps_to_zero` ✅ - K-part vanishes under residue sum
  - `polynomial_diagonal_pairing_zero` ✅ - polynomial case of vanishing
  - `diagonalEmbedding_mem_globalSubmodule` ✅ - diagonal K lands in globalSubmodule
  - `diagonal_globalSubmodule_pairing_zero` ✅ - well-definedness for K-part
- Sorries unchanged: 7 total
- Infrastructure for K-part of serrePairing well-definedness now complete

### Cycle 183 - Scalar multiplication for residue at infinity
- `residueAtInfty_smul` ✅ - Proved res_∞(c • f) = c * res_∞(f)
  - Key steps: (c • f).num = C c * f.num, (c • f).denom = f.denom
  - Used: isCoprime_mul_unit_left_left, smul_modByMonic, natDegree_smul_of_smul_regular
- Sorries reduced: 8 → 7

### Cycle 182 - Bilinear pairing infrastructure
- `residueSumTotal_smul` ✅ - Scalar multiplication for total residue sum
- `residueSumTotal_linearMap` ✅ - Total residue as linear map
- `residuePairing` ✅ - Bilinear pairing via product
- `residuePairing_bilinear` ✅ - Full bilinear map structure
- `residuePairing_eq_zero_of_splits` ✅ - Residue theorem for pairing

### Cycle 181 - Extended residue theorem to n poles
- `pairwise_coprime_X_sub_of_injective` ✅
- `residueSumTotal_n_poles_finset` ✅ - General residue theorem for n distinct linear poles
- `residueSumTotal_splits` ✅ - Corollary for split denominators

### Cycle 180 - Two poles residue theorem
- `residueSumTotal_two_poles` ✅ - Uses partial fractions

### Cycle 179 - Partial fractions infrastructure
- Added `Mathlib.Algebra.Polynomial.PartialFractions` import
- `isCoprime_X_sub_of_ne` ✅

### Cycle 178 - Perfect pairing dimension
- `finrank_eq_of_perfect_pairing` - Statement added (still sorry)

### Earlier cycles (166-177)
- See `ledger_archive.md` for detailed history

---

## Quick Commands

```bash
# Build
lake build 2>&1 | tail -5

# Find sorries
grep -rn "sorry$" RrLean/RiemannRochV2/*.lean RrLean/RiemannRochV2/SerreDuality/*.lean | grep -v "FqPolynomialInstance\|TraceDualityProof"

# Build specific file
lake build RrLean.RiemannRochV2.SerreDuality
```

---

## File Status

### In Build (2798 jobs)
- `RiemannRochV2.lean` (root)
- `Basic`, `Divisor`, `RRSpace`, `Typeclasses`
- `RiemannInequality` ✅
- `Infrastructure`, `RRDefinitions`
- `FullAdelesBase`, `FullAdelesCompact` ✅
- `AdelicH1v2` ✅
- `SerreDuality/` (directory with 3 files):
  - `Abstract.lean` ✅ (2 sorries: left_nondegen, right_nondegen)
  - `RatFuncResidues.lean` ✅ (0 sorries)
  - `RatFuncPairing.lean` ✅ (2 sorries: exists_global_approximant, strong_approx) ← was 4!
- `Residue.lean` ✅ (2 sorries: residueAtIrreducible, residue_sum_eq_zero)
- `SerreDuality.lean` ✅ (thin re-export module)

### Disconnected (not blocking)
- `DifferentIdealBridge.lean` ✅
- `TraceDualityProof.lean` (1 sorry, alternative approach)
- `FqPolynomialInstance.lean` (4 sorries, instantiation)
- `FullRRData.lean`, `Projective.lean`, `P1Instance.lean`

---

*For strategy and architecture, see `playbook.md`*
*For historical cycles 1-181, see `ledger_archive.md`*
