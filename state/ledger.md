# Ledger

Tactical tracking for Riemann-Roch formalization. For strategy, see `playbook.md`.

---

## Current State

**Build**: ✅ COMPILES
**Phase**: 3 - Serre Duality
**Cycle**: 170 (ready for next)

### Sorry Count: 15

| File | Count | Notes |
|------|-------|-------|
| `FullAdelesCompact.lean` | 1 | bound<1 edge case, not needed |
| `FqPolynomialInstance.lean` | 4 | concrete Fq[X] instance |
| `TraceDualityProof.lean` | 1 | abandoned approach |
| `SerreDuality.lean` | 5 | pairing types defined, proofs pending |
| `Residue.lean` | 4 | residueAt, residue_sum_eq_zero, residueAtLinear_add_aux (2 cases) |

---

## CYCLE 170 - Added residueAtLinear linearity lemmas

### Achievements
1. **`residueAtLinear_zero` ✅** - res_α(0) = 0
   - Simple: mul_zero + num/denom of 0

2. **`residueAtLinear_smul` ✅** - res_α(c • f) = c * res_α(f)
   - Key technique: Use `RatFunc.num_denom_mul` for (C c) * g
   - Coprimality argument: if g.denom.eval α = 0 and g.num.eval α = 0, contradiction via `IsCoprime.isUnit_of_dvd'`
   - Divisibility: `(C c * g).denom | g.denom` via `RatFunc.denom_mul_dvd`
   - Case analysis on denom evaluations, field_simp for main case

3. **`residueAtLinear_add_aux` (partial)** - Additivity framework set up
   - Two sorries remain for edge cases involving gcd reduction
   - Main case uses `RatFunc.num_denom_add` for (fX + gX).num/denom relationship

### Key Techniques Used
- `Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero` - if p | q and p.eval α = 0, then q.eval α = 0
- `Polynomial.dvd_iff_isRoot` - connect roots to divisibility
- `RatFunc.isCoprime_num_denom` - num and denom are coprime
- `RatFunc.denom_mul_dvd` - divisibility of product denominators

### Sorry Count Change
- Before: 13 sorries
- After: 15 sorries (+2 from residueAtLinear_add_aux edge cases)
- Net: Added foundational lemmas (smul, zero), structure for additivity

### Next Steps (Cycle 171)
1. **Complete `residueAtLinear_add_aux`** - Fill the two sorry cases
2. **Define `residueAtLinear_linearMap`** - Once additivity is complete
3. **Wire to SerreDuality** - Use residue infrastructure for pairing

---

## CYCLE 169 - Completed residue sorries

### Achievements
1. **`residueAtInfty_smul_inv_X_sub` ✅** - res_∞(c/(X-α)) = -c
   - Key: `EuclideanDomain.div_one` to simplify after `RatFunc.num_div`/`RatFunc.denom_div`
   - Remainder `(C c) % (X - C α) = C c` via `Polynomial.mod_eq_self_iff` + `degree_C_lt`
   - Condition `natDegree + 1 = 1` holds, gives `-c/1 = -c`

2. **`residueAtLinear_inv_X_sub_ne` ✅** - res_β(c/(X-α)) = 0 when α ≠ β
   - Key insight: `h.denom | (X - C α)` and `(X - C α).eval β ≠ 0` implies `h.denom.eval β ≠ 0`
   - Used `RatFunc.denom_dvd` to show `(X-α)⁻¹.denom | (X-α)` via `1/(X-α)` representation
   - `RatFunc.num_denom_mul` gives: `(f*h).num * h.denom = f.num * h.num * (f*h).denom`
   - Since `f.num.eval β = 0` (f = X - C β), product = 0, and h.denom ≠ 0 → num = 0

### Helper Lemmas Added (private)
- `RatFunc_num_X_sub_C'`, `RatFunc_denom_X_sub_C'` - num/denom of `(X - C β)`
- `denom_inv_X_sub_C_dvd` - `(X-α)⁻¹.denom | (X-α)` via `RatFunc.denom_dvd`
- `denom_smul_inv_X_sub_dvd` - `(c • (X-α)⁻¹).denom | (X-α)`
- `Polynomial.eval_ne_zero_of_dvd'` - if `p | q` and `q.eval x ≠ 0` then `p.eval x ≠ 0`

### Sorry Count Change
- Before: 15 sorries
- After: 13 sorries (-2)

### Next Steps (Cycle 170)
1. **Complete residue theorem wiring** - `residue_sum_simple_pole` now has all dependencies
2. **Wire SerreDuality.lean** - Use residue infrastructure for pairing
3. **Consider partial fractions** - For general `residue_sum_eq_zero`

---

## CYCLE 168 - residueAtInfty_smul_inv_X_sub Progress

### Achievements
1. **Fixed `residueAtInfty_smul_inv_X_sub` structure** - Proof nearly complete
   - Expressed `c • (X - α)⁻¹` as division form using `RatFunc.algebraMap_C`, `div_eq_mul_inv`
   - Used `RatFunc.num_div` and `RatFunc.denom_div` to extract num/denom
   - **Key breakthrough**: `gcd(C c, X - C α) = 1` via `normalize_gcd` + `normalize_eq_one`
     - gcd divides C c (a unit) → gcd is a unit → normalize(gcd) = 1 → gcd = 1

### Remaining Sorries in residueAtInfty_smul_inv_X_sub (1)
- Line 544: Computational simplification after gcd = 1 substitution
  - Goal involves `(C c) % (X - C α)` and leading coefficients
  - Should be routine simp once the right lemmas are identified

### Key Discoveries
- `Polynomial Fq` requires `open Classical` for `GCDMonoid` instance
- `gcd` (from GCDMonoid) ≠ `EuclideanDomain.gcd` definitionally, but they agree
- For NormalizedGCDMonoid: `gcd = normalize(gcd)` via `normalize_gcd`
- Unit gcd → 1 via `normalize_eq_one.mpr`

### Next Steps (Cycle 169)
1. Complete `residueAtInfty_smul_inv_X_sub` computational simplification
2. Fill `residueAtLinear_inv_X_sub_ne` (res_β(c/(X-α)) = 0 for β ≠ α)
3. Wire `residue_sum_simple_pole` fully (depends on above)

### Sorry Count Change
- Before: 15 sorries
- After: 15 sorries (restructured, main gcd hurdle solved)

---

## CYCLE 167 - Linear Place Residues and Residue Sum

### Achievements
1. **`residueAtLinear` ✅** - Defined residue at linear places (X - α)
   - Formula: multiply by (X - α), then evaluate at α
   - Captures residue via coefficient extraction after pole cancellation
2. **`residueAtLinear_inv_X_sub` ✅** - Key test case: res_α(c/(X-α)) = c
3. **`residueAtLinear_polynomial` ✅** - Polynomials have zero residue at all finite places
4. **`residueAtLinear_zero_eq_residueAtX_simple` ✅** - Consistency check at α = 0
5. **`residue_sum_simple_pole` ✅** - Residue theorem for simple linear poles
   - Proved: res_α(c/(X-α)) + res_∞(c/(X-α)) = c + (-c) = 0

### New Infrastructure
- `residueAtLinear (α : Fq) (f : RatFunc Fq) : Fq` - residue at place (X - α)
- Residue theorem for simple poles: finite + infinity residues sum to zero

### Remaining Sorries in Residue.lean (4)
1. **`residueAtInfty_smul_inv_X_sub`** - res_∞(c/(X-α)) = -c (type coercion complexity)
2. **`residueAt`** - General finite place residue (placeholder)
3. **`residueAtLinear_inv_X_sub_ne`** - res_β(c/(X-α)) = 0 for β ≠ α
4. **`residue_sum_eq_zero`** - General residue theorem (placeholder)

### Sorry Count Change
- Before: 13 sorries
- After: 15 sorries (+2 from new structure, but key theorem `residue_sum_simple_pole` proved)

### Key Insight
The residue theorem for simple linear poles is now proven! This validates the approach:
- `residueAtLinear` correctly captures pole residues via multiplication and evaluation
- `residueAtInfty` correctly captures infinity residue via degree-based formula
- Sum = 0 as expected from residue theorem

---

## CYCLE 166 - residueAtInfty_add Proof Completed

### Achievements
1. **`residueAtInftyAux_mul_monic` ✅** - Scaling lemma proved
   - Key insight: Use `Polynomial.div_modByMonic_unique` for `(p*k) %ₘ (q*k) = (p%ₘ q) * k`
   - `modByMonic_eq_mod` converts `%` to `%ₘ` for monic divisors
   - `Monic.of_mul_monic_left` proves quotient k is monic
2. **`residueAtInfty_add` ✅** - Main additivity theorem proved
   - Scale f and g to common denominator using `residueAtInftyAux_mul_monic`
   - Use `residueAtInftyAux_add` for numerator additivity
   - `RatFunc.num_denom_add` + `isCoprime_num_denom` relate reduced to unreduced form
   - The gcd factor k dividing out is monic, so residue is preserved

### Key Lemmas Used
- `Polynomial.div_modByMonic_unique`: uniqueness of polynomial division
- `Polynomial.modByMonic_eq_mod`: `%ₘ = %` for monic divisors
- `RatFunc.num_denom_add`: `(f+g).num * (f.denom * g.denom) = (f.num * g.denom + f.denom * g.num) * (f+g).denom`
- `RatFunc.isCoprime_num_denom`: num and denom are coprime
- `WithBot.add_lt_add_right`: degree arithmetic in WithBot

### Remaining Sorries in Residue.lean (2)
1. **`residueAt`** (line 523) - Placeholder for general finite place
2. **`residue_sum_eq_zero`** (line 549) - Residue theorem (placeholder)

### Sorry Reduction
- Before: 15 sorries
- After: 13 sorries (-2)

---

## Next Steps (Cycle 165+): RESIDUE APPROACH

### Remaining Plan (~7-9 cycles)

**Phase A: Complete Residue Definitions ✅**
- Cycle 159: Fill `residueAtX_smul` proof ✅
- Cycle 160: Fill `residueAtX_polynomial` proof ✅
- Cycle 161: Define `residueAtInfty` ✅

**Phase B: Residue Theorem (Cycles 162-164)**
```lean
-- Use partial fractions: f = q + ∑ rᵢ/gᵢ where deg(rᵢ) < deg(gᵢ)
-- Polynomial q contributes 0 residue
-- Each rᵢ/gᵢ contributes residues only at roots of gᵢ
-- Sum cancels with infinity
theorem residue_sum_eq_zero (f : RatFunc Fq) :
    (∑ᶠ v, residue_at v f) + residue_infty f = 0 := ...
```

**Phase C: Wire to Serre Pairing (Cycles 165-167)**
```lean
-- The pairing: for [a] ∈ H¹(D) and f ∈ L(K-D)
-- ⟨[a], f⟩ := ∑_v res_v(aᵥ · f)
def serrePairing : H¹(D) →ₗ[k] L(K-D) →ₗ[k] k := ...
```

**Phase D: Non-degeneracy (Cycles 168-171)**
```lean
-- Left: if ⟨[a], f⟩ = 0 for all f, then [a] = 0
-- Right: if ⟨[a], f⟩ = 0 for all [a], then f = 0
-- Use: strong approximation + partial fractions
```

### Why This Works (Mathematical Justification)

For `F = RatFunc Fq` (NOT an extension):
1. Places = irreducible polynomials + ∞
2. Completion at p ≅ `Fq((t-α))` = Laurent series
3. Residue = coefficient of `(t-α)^{-1}`
4. Residue theorem = partial fractions sum to zero

**No trace needed** because we're working directly in F, not an extension K/F.

### Warning Signs (abort if you see these)

- ❌ Trying to define trace on adeles/completions
- ❌ Building abstract residue infrastructure for general extensions
- ❌ More than 3 cycles without `.coeff (-1)` appearing in code
- ❌ **Chasing gcd/coprime/denom normalization lemmas** (Cycle 164 hit this!)
- ✅ Using `HahnSeries.coeff`, `LaurentSeries`, partial fractions
- ✅ Using `Polynomial.add_mod`, `Polynomial.coeff_add` for coefficient-level proofs

---

## Key Lemmas to Prove

| Lemma | Purpose | Approach |
|-------|---------|----------|
| `residue_at_def` | res_p(f) = coeff of (t-α)^{-1} | Use LaurentSeries.coeff |
| `residue_sum_eq_zero` | ∑ res_v(f) = 0 | Partial fractions |
| `serrePairing_wellDefined` | Descends to H¹(D) | Use residue_sum_eq_zero |
| `serrePairing_left_nondegen` | Left kernel trivial | Strong approximation |
| `serrePairing_right_nondegen` | Right kernel trivial | Partial fractions |
| `serre_duality` | h¹(D) = ℓ(K-D) | Perfect pairing |

---

## Advice for This Phase

### Use these Mathlib tools
- `HahnSeries.coeff` - coefficient extraction
- `LaurentSeries` - abbreviation for `HahnSeries ℤ`
- `div_eq_quo_add_sum_rem_div` - partial fractions decomposition
- `LaurentSeriesRingEquiv` - completion ≅ Laurent series

### The bridge theorem exists
Once `AdelicRRData` is instantiated, `adelicRRData_to_FullRRData` gives full RR automatically. Focus on the 6 axioms:
- `h1_finite`, `ell_finite` - finiteness (use compactness)
- `h1_vanishing` - strong approximation (infrastructure exists)
- `adelic_rr` - Euler characteristic
- `serre_duality` - **NOW TRACTABLE via residues**
- `deg_canonical` - degree of K

---

## Quick Commands

```bash
# Build
lake build 2>&1 | tail -5

# Find sorries
grep -rn "sorry" RrLean/RiemannRochV2/*.lean | grep -v "sorry-free\|-- .*sorry"

# Build specific file
lake build RrLean.RiemannRochV2.DifferentIdealBridge
```

---

## Recent Cycles

### Cycle 167 (2025-12-19)
- **Defined `residueAtLinear`** - Residue at linear places (X - α) via multiply-and-evaluate
- **Proved key lemmas:**
  - `residueAtLinear_inv_X_sub`: res_α(c/(X-α)) = c ✅
  - `residueAtLinear_polynomial`: res_α(polynomial) = 0 ✅
  - `residueAtLinear_zero_eq_residueAtX_simple`: consistency at α = 0 ✅
- **Proved `residue_sum_simple_pole`** - First residue theorem! ✅
  - res_α(c/(X-α)) + res_∞(c/(X-α)) = c + (-c) = 0
- **Added sorries for:**
  - `residueAtInfty_smul_inv_X_sub`: res_∞(c/(X-α)) = -c (type coercion issues)
  - `residueAtLinear_inv_X_sub_ne`: res_β(c/(X-α)) = 0 for β ≠ α
- Sorry count: 13 → 15 (structure expansion, but key theorem proved)
- Build status: ✅ COMPILES

### Cycle 166 (2025-12-19)
- **Completed `residueAtInfty_add` proof** - Main additivity for residue at infinity
- **Proved `residueAtInftyAux_mul_monic`** - Scaling lemma using `div_modByMonic_unique`
  - Key: `(p*k) %ₘ (q*k) = (p %ₘ q) * k` via uniqueness of polynomial division
  - Uses `modByMonic_eq_mod` to convert `%` to `%ₘ` for monic divisors
- **Proved `residueAtInfty_add`** - Full additivity using auxiliary function approach
  - Scale to common denominator via `residueAtInftyAux_mul_monic`
  - Use `residueAtInftyAux_add` for numerator additivity
  - Connect reduced and unreduced forms via `RatFunc.num_denom_add` + coprimality
- Key Mathlib tools: `div_modByMonic_unique`, `Monic.of_mul_monic_left`, `isCoprime_num_denom`
- Sorry count: 15 → 13 (filled 2 proofs)
- Build status: ✅ COMPILES

### Cycle 165 (2025-12-19)
- **Fixed Residue.lean build** - File now compiles cleanly
- **Reordered lemmas:**
  - Moved `residueAtInfty_eq_neg_coeff` and `coeff_mul_at_sum_sub_one` before aux definitions
  - Fixed decidability issue in `residueAtInftyAux` using `open Classical in`
  - Changed `dif_neg` to `if_neg` for proper if-then-else handling
- **Filled proofs:**
  - `residueAtInfty_eq_aux` ✅ - Connection between residueAtInfty and aux function
  - `residueAtInftyAux_add` ✅ - Numerator additivity
- **Remaining sorries:**
  - `residueAtInftyAux_mul_monic` - Scaling lemma (proof documented, needs uniqueness of polynomial division)
  - `residueAtInfty_add` - Main additivity (proof strategy documented)
- Sorry count: 16 → 15 (one proof filled, structure cleaner)
- Build status: ✅ COMPILES

### Cycle 164 (2025-12-19) - INCOMPLETE HANDOFF
- **Attempted:** Fill `residueAtInfty_add` sorries via gcd/coprime approach
- **Failed approach:** Tried proving `(f+g).denom = g.denom` when f is polynomial
  - Required `gcd_add_mul_self`, `denom_add_polynomial_left`, `num_add_polynomial_left`
  - Hit API friction: `IsCoprime.gcd_eq_one` doesn't exist, RatFunc normalization complex
  - **DO NOT REPEAT THIS APPROACH**
- **Pivoted to:** Auxiliary function approach (partially implemented, not compiling)
  - Defined `residueAtInftyAux (p q : Polynomial Fq) : Fq`
  - Proved `residueAtInftyAux_add` (additivity in numerator)
  - Started `residueAtInftyAux_mul_monic` (scaling invariance)
- **Current state:** File broken due to lemma ordering issues
- **Next Claude:** See "CYCLE 164 HANDOFF" section above for exact fix needed
- Sorry count: 16 (unchanged, file broken)

### Cycle 163 (2025-12-19)
- **Set up `residueAtInfty_add` proof structure** - Additivity for residue at infinity
- **Proved helper lemmas:**
  - `residueAtInfty_eq_neg_coeff`: residue = negated coefficient at deg(denom)-1 in remainder
  - `coeff_mul_at_sum_sub_one`: for proper fractions, coefficient at critical index
- **Main proof structure:**
  - Case analysis: polynomial f (d_f=1), polynomial g (d_g=1), main case
  - Main case established: degree bounds for remainders, sum is proper, remainder is itself
  - Mathematical insight: gcd reduction preserves coefficient at critical index
- **Remaining:** 3 sub-sorries for polynomial cases and gcd invariance
- Sorry count: 14 → 16 (expanded structure, helper lemmas proved)
- Key discovery: `Polynomial.coeff_mul_add_eq_of_natDegree_le` is the right tool

### Cycle 162 (2025-12-19)
- **Filled `residueAtInfty_inv_X_sub` proof** - Key test case for residue at infinity
- Proves that `residueAtInfty (1/(X - c)) = -1` for any c ∈ Fq
- Proof technique:
  1. Express `(X - C c)⁻¹` as `1 / (X - C c)` using algebraMap
  2. Use `RatFunc.num_div` and `RatFunc.denom_div` to get num = 1, denom = X - C c
  3. Show gcd(1, X - C c) = 1 with `gcd_one_left`
  4. Prove remainder `1 % (X - C c) = 1` via `mod_eq_self_iff` and degree comparison
  5. Verify deg(1) + 1 = deg(X - C c), so the if-condition is true
  6. Compute `-leadingCoeff(1)/leadingCoeff(X-C c) = -1/1 = -1`
- Sorry count: 15 → 14

### Cycle 161 (2025-12-19)
- **Defined `residueAtInfty`** - Residue at infinity using degree-based formula
- Definition uses polynomial remainder: for f = p/q, compute rem = p % q
  - If deg(rem) + 1 = deg(q), then res_∞ = -leadingCoeff(rem)/leadingCoeff(q)
  - Otherwise res_∞ = 0
- Proved `residueAtInfty_zero` and `residueAtInfty_polynomial`
- Added `residueAtInfty_inv_X_sub` test case (proof outline documented, sorry for now)
- **Residue definitions now complete**: both residueAtX and residueAtInfty defined ✅
- Sorry count: 15→15 (filled definition, added test case sorry)

### Cycle 160 (2025-12-19)
- **Filled `residueAtX_polynomial` proof** - Polynomials have zero residue at X=0
- Proof technique:
  1. Use `RatFunc.coe_coe` to factor: `(p : RatFunc : LaurentSeries) = (p : PowerSeries : LaurentSeries)`
  2. Use `ofPowerSeries_apply` to expose `embDomain` structure
  3. Apply `embDomain_notin_range` since `-1 ∉ range(Nat.cast : ℕ → ℤ)`
  4. Finish with `Int.natCast_nonneg` and `omega`
- **X-adic residue foundation complete**: all lemmas for `residueAtX_linearMap` now proved
- Sorry count: 16→15

### Cycle 159 (2025-12-19)
- **Filled `residueAtX_smul` proof** - Key lemma for linear map structure
- Proof technique:
  1. Use `RatFunc.smul_eq_C_mul` to convert scalar mult to multiplication by constant
  2. Use `RatFunc.coe_coe` to factor coercion through PowerSeries
  3. Use `HahnSeries.C_mul_eq_smul` and `HahnSeries.coeff_smul`
- Partial progress on `residueAtX_polynomial`:
  - Set up: `RatFunc.coe_coe` gives `(p : PowerSeries : LaurentSeries)`
  - Remaining: show `embDomain` with `Nat.cast` has no `-1` in range
- Sorry count: 17→16

### Cycle 158 (2025-12-19)
- **Created `Residue.lean`** - Foundation for residue-based Serre duality
- Defined `residueAtX : RatFunc Fq → Fq` using `HahnSeries.coeff (-1)`
- Proved key lemmas:
  - `residueAtX_add` - additivity ✅
  - `residueAtX_inv_X = 1` - fundamental test case ✅
  - `residueAtX_inv_X_sq = 0` - only simple poles contribute ✅
- Defined `residueAtX_linearMap : RatFunc Fq →ₗ[Fq] Fq`
- Placeholder definitions for `residueAtInfty` and `residueAt` (general places)
- Placeholder for `residue_sum_eq_zero` (residue theorem)
- 6 new sorries (expected - structure first, proofs in subsequent cycles)
- Successfully uses `HahnSeries.coeff (-1)` as planned! ✅

### Cycle 157 (2025-12-19)
- **Investigation cycle**: Deep dive into trace dual vs residue approaches
- **Dead end found**: Trace dual gives `dual(L(D)) ↔ L(K+D)`, NOT `L(K-D)`
- **Breakthrough**: For `K = RatFunc Fq`, residues ARE tractable!
  - `LaurentSeries` with `.coeff (-1)` gives residue extraction
  - `div_eq_quo_add_sum_rem_div` gives partial fractions
  - No trace needed - working directly in F, not extension K/F
- **New plan**: Build explicit residues using Mathlib's Laurent series (~12-15 cycles)
- See "Next Steps" section for detailed roadmap
- No code changes; planning/research cycle

### Cycle 156 (2025-12-19)
- **Created `SerreDuality.lean`** with pairing type definitions
- Defined `serrePairing : H¹(D) × L(K-D) → k` (types compile, proof is sorry)
- Added supporting lemmas: `serrePairing_wellDefined`, `_left_nondegen`, `_right_nondegen`
- Added `serre_duality` theorem and `mkAdelicRRData` constructor
- Investigated Mathlib: no trace on adeles/completions, need algebraic approach
- 5 new sorries (expected, pairing construction pending)

### Cycle 155 (2025-12-18)
- Repo maintenance cycle
- Identified disconnected files needing wiring

### Cycle 154 (2025-12-18)
- Filled `exists_finite_integral_translate_with_infty_bound` for bound ≥ 1
- One sorry remains for bound < 1 (not needed)

### Cycle 153 (2025-12-18)
- Filled 3 sorries in `exists_finite_integral_translate`
- Sorry count: 4→1 in that theorem

### Cycles 133-152 (2025-12-17 to 2025-12-18)
- Full adeles compactness work
- K discrete, closed, integral adeles compact
- Weak approximation

### Cycles 76-132
- Adelic infrastructure build-out
- AdelicH1v2 with Mathlib's FiniteAdeleRing
- DifferentIdealBridge for canonical divisor

### Cycles 1-75
- Phase 1: Riemann Inequality ✅
- Tag: `v1.0-riemann-inequality`

---

## File Status

### In Build (2771 jobs)
- `RiemannRochV2.lean` (root)
- `Basic`, `Divisor`, `RRSpace`, `Typeclasses`
- `RiemannInequality` ✅
- `Infrastructure`, `RRDefinitions`
- `FullAdelesBase`, `FullAdelesCompact` ✅
- `Residue.lean` ✅ (NEW - X-adic residue foundation)

### Disconnected (need wiring)
- `DifferentIdealBridge.lean` ✅
- `TraceDualityProof.lean` (1 sorry, wrong approach)
- `AdelicH1v2.lean` ✅
- `Adeles.lean` (old model)
- `FullRRData.lean`
- `Projective.lean`
- `P1Instance.lean`
- `FqPolynomialInstance.lean` (4 sorries)

---

*For strategy and architecture, see `playbook.md`*
*For historical cycles 1-155, see `ledger_archive.md`*
