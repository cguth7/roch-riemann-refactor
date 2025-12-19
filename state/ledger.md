# Ledger Vol. 3.3 (Cycles 133+) - Full Adeles Compactness

**Ultimate Goal**: Formalize Riemann-Roch for curves over finite fields in Lean 4 — **no axioms, no sorries**.

*For Cycles 1-34, see `state/ledger_archive.md` (Vol. 1)*
*For Cycles 35-79, see `state/ledger_archive.md` (Vol. 2)*
*For Cycles 80-99, see `state/ledger_archive.md` (Vol. 3.1)*
*For Cycles 100-117, see `state/ledger_archive.md` (Vol. 3.2 Part 1 - AllIntegersCompact)*
*For Cycles 118-132, see `state/ledger_archive.md` (Vol. 3.2 Part 2 - FullAdeles Foundation)*

---

## 🎯 NEXT CLAUDE: Start Here (Cycle 152)

### Current State
Build: ✅ **COMPILES** with **2 sorries** in FullAdelesCompact.lean

### What Cycle 151 Did
- ✅ **Filled `exists_translate_in_integralFullAdeles`** (3 → 2 sorries)
  - Uses `exists_approx_in_ball_infty` for infinity approximation
  - Uses `exists_finite_integral_translate_with_infty_bound` for finite places
  - Combines using ultrametric inequality
- ✅ **Found key API**: `Ideal.prime_of_isPrime v.ne_bot v.isPrime` for CRT

### Remaining Sorries (2 total)
1. `exists_finite_integral_translate` (line ~540) - CRT proof
2. `exists_finite_integral_translate_with_infty_bound` (line ~628) - polynomial division

### Strategy for Next Cycle

**For `exists_finite_integral_translate`**:
The CRT structure is documented inline. Key steps:
1. Get bad set S from restricted product property
2. Get approximants y_v via `exists_local_approximant`
3. Get common denominator D for all y_v
4. Build T = S ∪ {divisors of D}
5. Apply `IsDedekindDomain.exists_forall_sub_mem_ideal` (CRT)
6. Verify valuations using `intValuation_ge_exp_neg_natDegree`

**For `exists_finite_integral_translate_with_infty_bound`**:
1. Get k₀ from `exists_finite_integral_translate`
2. Use Euclidean division: k₀ = q + r/denom where deg(r) < deg(denom)
3. k = k₀ - q has |k|_∞ < 1 ≤ bound
4. q is polynomial, so finite integrality preserved

### Key Findings from Cycle 150: API Issues

The CRT proof structure is correct. The issues found are:

1. **`Ideal.IsPrime.prime` doesn't exist** - Need `v.isPrime.prime` or find correct API
   - HeightOneSpectrum.isPrime gives IsPrime, but CRT needs Prime
   - Try: `Ideal.isPrime_iff_prime` or work with prime directly

2. **`RatFunc.algebraMap_ne_zero.mpr` doesn't exist** - Need different form
   - Try: `RatFunc.algebraMap_ne_zero` without `.mpr`, or `map_ne_zero_of_mem_nonZeroDivisors`

3. **Type elaboration timeouts** with completions/valuations
   - Break complex expressions into intermediate steps
   - Add explicit type annotations: `(k : v.adicCompletion (RatFunc Fq))`
   - Use `set_option maxHeartbeats 400000` if needed

4. **`Polynomial.div_mul_eq_mul_div` pattern issues**
   - The polynomial division/multiplication order may differ from expected

### Proof Structure (CORRECT - needs API fixes)
```lean
-- Step 1: S = bad places (finite by restricted product)
have hS_finite := Filter.eventually_cofinite.mp a.property
let S := hS_finite.toFinset

-- Step 2: Get approximants y_v for each v ∈ S
choose y hy using (fun v => exists_local_approximant Fq v (a.val v))

-- Step 3: D = product of denominators
let D := S.prod (fun v => (y v).denom)

-- Step 4: T = S ∪ {divisors of D}
let T := S ∪ (HeightOneSpectrum.finite_divisors Fq D hD_zero).toFinset

-- Step 5: Apply CRT
obtain ⟨P, hP⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (fun v => v.asIdeal) e ...

-- Step 6: k = P/D, verify valuations
let k := algebraMap Fq[X] (RatFunc Fq) P / algebraMap Fq[X] (RatFunc Fq) D
```

### IMMEDIATE NEXT STEP: Fix API issues

1. Find correct API for `IsPrime → Prime` for ideals in HeightOneSpectrum
2. Find correct form of `RatFunc.algebraMap_ne_zero`
3. Add type annotations to avoid elaboration timeouts

### Alternative: Simplify the proof

If API issues persist, consider:
- Using `native_decide` for finite field computations
- Breaking the proof into smaller lemmas
- Using `set_option maxHeartbeats` temporarily

### Key Proofs Added in Cycle 147

**`intValuation_ge_exp_neg_natDegree`** (lines 316-363):
- For D ∈ v.asIdeal: bounds multiplicity n by natDegree D via g^n | D ⟹ n·deg(g) ≤ deg(D)
- For D ∉ v.asIdeal: intValuation = 1 ≥ exp(-natDegree D)
- Uses: `intValuation_if_neg`, `prime_generator_of_isPrime`, `natDegree_pow`, `natDegree_le_of_dvd`

**`polynomial_integral_at_finite_places`** (line 257-259):
- One-liner: `coe_algebraMap_mem Fq[X] (RatFunc Fq) v p`

**`isOpen_ball_le_one_FqtInfty`** (lines 206-211):
- Uses `@Valued.isOpen_integer` with `convert h using 1`

### File Split (for faster builds)
- **FullAdelesBase.lean** (~685 lines) - General defs → ✅ COMPILES
- **FullAdelesCompact.lean** (~762 lines) - Compactness, weak approx → ✅ COMPILES (2 sorries)
- **FullAdeles.lean** - Re-export hub

---

## Cycle 151 Summary - 1 SORRY FILLED

**Goal**: Fill remaining sorries in FullAdelesCompact.lean

**Status**: ✅ Reduced from 3 to 2 sorries

**Filled**:
1. `exists_translate_in_integralFullAdeles` - Weak approximation main theorem

**Key technique**:
- Get polynomial P approximating a.2 at infinity via `exists_approx_in_ball_infty`
- Work with b = a - diag(P), which has |b.2|_∞ ≤ 1
- Get z from `exists_finite_integral_translate_with_infty_bound` with bound = 1
- Combine x = P + z, verify using:
  - Finite: (a - diag(x)).1 v = (b - diag(z)).1 v = b.1 v - z ∈ O_v
  - Infinity: ultrametric inequality |b.2 - z|_∞ ≤ max(|b.2|_∞, |z|_∞) ≤ 1

**Key API discoveries**:
- `Ideal.prime_of_isPrime v.ne_bot v.isPrime` converts IsPrime to Prime for CRT
- `(fqFullDiagonalEmbedding Fq).map_add` for ring hom property
- `Valued.v.map_sub` for ultrametric inequality
- `(v.adicCompletionIntegers K).add_mem` for integral element addition

**Remaining sorries (2)**:
1. `exists_finite_integral_translate` - CRT-based proof (complex, API-intensive)
2. `exists_finite_integral_translate_with_infty_bound` - Polynomial division argument

---

## Cycle 150 Summary - API INVESTIGATION

**Goal**: Fill `exists_finite_integral_translate` using CRT approach

**Status**: 🔶 PARTIAL - Proof structure complete, API issues identified

**Attempted**:
1. Wrote full CRT-based proof following the documented approach
2. Identified 4 key API issues blocking compilation:
   - `Ideal.IsPrime.prime` doesn't exist
   - `RatFunc.algebraMap_ne_zero.mpr` has different form
   - Type elaboration timeouts with completions
   - Polynomial division API mismatches

**Key insight**: The proof structure is mathematically correct:
- Use `Filter.eventually_cofinite.mp a.property` to get finite bad set S
- Use `choose` to get approximants y_v from `exists_local_approximant`
- Build D = ∏ denom(y_v), then T = S ∪ {divisors of D}
- Apply `IsDedekindDomain.exists_forall_sub_mem_ideal` for CRT
- Verify valuations using `intValuation_ge_exp_neg_natDegree`

**What's needed for Cycle 151**:
1. Search for correct `IsPrime → Prime` API (try `Ideal.isPrime_iff_prime`)
2. Find correct form of RatFunc algebraMap non-zero lemma
3. Add explicit type annotations to avoid timeouts
4. Consider breaking into smaller helper lemmas

---

## Cycle 149 Summary - 2 SORRIES FILLED

**Goal**: Fill remaining sorries in FullAdelesCompact.lean

**Status**: ✅ Reduced from 5 to 3 sorries

**Filled**:
1. `isPrincipalIdealRing_integer_FqtInfty` - Value group is cyclic + nontrivial ⟹ PIR
2. `isDiscreteValuationRing_integer_FqtInfty` - Same approach gives DVR

**Key technique**: Working with the value group of a discrete valuation
- Value group is a subgroup of `(WithZero (Multiplicative ℤ))ˣ ≅ Multiplicative ℤ`
- Use `isCyclic_multiplicative` (from `IsAddCyclic ℤ`) and `Subgroup.isCyclic`
- Prove nontriviality by exhibiting an element ≠ 1 via `isNontrivial_FqtInfty`
- Key API: `Valuation.ne_zero_iff`, `MonoidWithZeroHom.mem_valueGroup`, `Units.mk0`

**Key code patterns**:
```lean
-- Get IsCyclic via inference chain
haveI hCyclic : IsCyclic (MonoidWithZeroHom.valueGroup Valued.v) := inferInstance

-- Prove Nontrivial explicitly
obtain ⟨x, hx_ne, hx_lt⟩ := Valuation.isNontrivial_iff_exists_lt_one Valued.v |>.mp hnt
have hx_vne : Valued.v x ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hx_ne
let vx : (WithZero (Multiplicative ℤ))ˣ := Units.mk0 (Valued.v x) hx_vne
have hvx_mem := MonoidWithZeroHom.mem_valueGroup Valued.v (Set.mem_range.mpr ⟨x, rfl⟩)
exact ⟨⟨1, Subgroup.one_mem _⟩, ⟨⟨vx, hvx_mem⟩, proof_that_vx_ne_1⟩⟩

-- Apply mathlib's instance
exact Valuation.valuationSubring_isPrincipalIdealRing Valued.v
```

---

## Cycle 148 Summary - 2 SORRIES FILLED

**Goal**: Fill sorries in FullAdelesCompact.lean

**Status**: ✅ Reduced from 7 to 5 sorries

**Filled**:
1. `exists_local_approximant` - Density argument via WithVal type synonym
2. `HeightOneSpectrum.finite_divisors` - Injective map to normalizedFactors

**Key techniques**:
- **WithVal factoring**: To avoid UniformSpace instance mismatch, factor density through `WithVal`:
  - `algebraMap K (adicCompletion K v)` factors as `coeRingHom ∘ algebraMap K (WithVal ...)`
  - Since `WithVal` is a type synonym, `algebraMap K (WithVal ...)` is surjective
  - `coeRingHom` has dense range by `denseRange_coe`
  - Composition of surjective + dense range = dense range

- **UFM normalizedFactors API**:
  - `exists_mem_normalizedFactors_of_dvd` gives `q ∈ normalizedFactors D` with `p ~ᵤ q`
  - `normalize_normalized_factor` gives `normalize q = q` for normalized factors
  - `normalize_eq_normalize` gives equality from divisibility both ways
  - `Ideal.span_singleton_eq_span_singleton` for associated → same ideal

---

## Cycle 147 Summary - 5 SORRIES FILLED

**Goal**: Fill sorries in FullAdelesCompact.lean

**Status**: ✅ Reduced from 12 to 7 sorries

**Filled**:
1. `intValuation_ge_exp_neg_natDegree` - Full proof using multiplicity bounds
2. `polynomial_integral_at_finite_places` - Using `coe_algebraMap_mem`
3. `isOpen_ball_le_one_FqtInfty` - Using `Valued.isOpen_integer`

**Almost filled** (needs instance fix):
4. `exists_local_approximant` - Density argument structure complete

**Key APIs discovered**:
- `coe_algebraMap_mem R K v r` - Elements of R are integral in adicCompletion
- `Valued.isOpen_integer` - {v x ≤ 1} is open
- `intValuation_if_neg` - Computes intValuation via Associates.count
- `Ideal.span_singleton_generator` - Generator of principal ideal
- `prime_generator_of_isPrime` - Generator of prime ideal is prime

---

## Cycle 146 Summary - FILE NOW COMPILES

**Goal**: Get FullAdelesCompact.lean to compile (was 15 errors)

**Status**: ✅ COMPILES with ~12 sorries

**Fixed APIs**:
- `Finset.prod_ne_zero` → `Finset.prod_ne_zero_iff.mpr`
- `Submodule.Prime` → `Ideal.IsPrime` (via `v.isPrime`)
- `Valuation.map_sub_le_max'` → `Valued.v.map_sub`
- `Valuation.map_add_le` → `Valued.v.map_add_le`
- `RingHom.map_div₀` → `map_div₀`
- Removed redundant `h1` rewrite that broke after earlier changes

**Key decision**: Converted broken proofs to documented sorries
- Each proof has inline block comment explaining:
  - The mathematical approach
  - Key steps and lemmas needed
  - Specific API issues blocking completion
- This preserves knowledge for future filling while unblocking build

**Sorried proofs with documented approaches**:
- `exists_finite_integral_translate` - Full CRT proof outline
- `exists_finite_integral_translate_with_infty_bound` - Polynomial division outline
- `exists_translate_in_integralFullAdeles` - Combination outline

---

## Cycle 145 Summary - API FIXES (PARTIAL)

**Goal**: Fix 41 build errors in FullAdelesCompact.lean

**Status**: ⚠️ Reduced to ~15 errors, 4 proofs sorried

**Fixed APIs**:
- `isCompact_of_compactSpace_subtype` → `isCompact_iff_compactSpace.mpr`
- `valuation_of_algebraMap_le` → `valuation_of_algebraMap` + `intValuation_le_one`
- `Finset.Finite` → `finite_toSet` (Finsets are always finite)
- `Valuation.pos_iff` usage corrected
- Added explicit `completeSpace_FqtInfty` instance
- Added `open scoped WithZero` for notation

**Sorried** (API mismatch investigation needed):
- `isPrincipalIdealRing_integer_FqtInfty`
- `isDiscreteValuationRing_integer_FqtInfty`
- `exists_local_approximant`
- `intValuation_ge_exp_neg_natDegree`

**Remaining errors**: ~15, mostly in `exists_finite_integral_translate` and polynomial division

---

## Cycle 144 Summary - CODE WRITTEN BUT NOT COMPILING

**Goal**: Re-implement lost Cycle 143 solution

**Status**: ⚠️ Code written but discovered file has 41 build errors (stale cache issue)

**Key accomplishments**:
1. ✅ Added `intValuation_ge_exp_neg_natDegree` lemma (bounds multiplicity by degree)
2. ✅ Filled v ∈ S case using valuation division and ultrametric inequality
3. ✅ Filled v ∈ T \ S case using same technique
4. ✅ Filled `exists_finite_integral_translate_with_infty_bound` for bound ≥ 1

**Remaining sorry**: bound < 1 case in `exists_finite_integral_translate_with_infty_bound`
- This is not needed since main theorem uses bound = 1
- Could be filled with more refined polynomial division if needed

**Key technique**: For k = P/D where P - target ∈ v^{deg(D)+1}, we have:
- val_v(P - target) ≤ exp(-(deg(D)+1))
- val_v(D) ≥ exp(-deg(D)) by `intValuation_ge_exp_neg_natDegree`
- So val_v((P-target)/D) ≤ exp(-1) ≤ 1, meaning the quotient is integral

---

## 🔧 ARCHIVED: Recovery Plan (Cycle 143 solution)

### Step 1: Add key lemma `intValuation_ge_exp_neg_natDegree`

**Location**: Insert just before `exists_finite_integral_translate` (around line 1089, after `finite_divisors`)

**Purpose**: Bounds multiplicity of any prime v in polynomial D by natDegree D

```lean
/-- The intValuation of D is at least exp(-natDegree D).
This bounds the multiplicity of any prime in D by the degree of D.
Proof: g is irreducible so deg(g) ≥ 1, and g^n | D implies n·deg(g) ≤ deg(D). -/
lemma intValuation_ge_exp_neg_natDegree (v : HeightOneSpectrum Fq[X]) (D : Fq[X]) (hD : D ≠ 0) :
    v.intValuation D ≥ WithZero.exp (-(D.natDegree : ℤ)) := by
  by_cases hD_mem : D ∈ v.asIdeal
  · -- D ∈ v.asIdeal: bound the multiplicity
    haveI : v.asIdeal.IsPrincipal := IsPrincipalIdealRing.principal v.asIdeal
    let g := Submodule.IsPrincipal.generator v.asIdeal
    have hg_irr : Irreducible g := (Submodule.IsPrincipal.prime_generator_of_isPrime v.asIdeal v.ne_bot).irreducible
    have hg_deg : 1 ≤ g.natDegree := Polynomial.Irreducible.natDegree_pos hg_irr
    let n := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {D})).factors
    have hval : v.intValuation D = WithZero.exp (-(n : ℤ)) := v.intValuation_if_neg hD
    rw [hval]
    apply WithZero.exp_le_exp.mpr
    simp only [neg_le_neg_iff, Int.ofNat_le]
    by_cases hn : n = 0
    · simp [hn]
    · -- g^n | D, so n * deg(g) = deg(g^n) ≤ deg(D), hence n ≤ deg(D)
      have hgn_dvd : g ^ n ∣ D := by
        have hmem : D ∈ v.asIdeal ^ n := by rw [v.intValuation_le_pow_iff_mem, hval]
        have hpow_eq : v.asIdeal ^ n = Ideal.span {g ^ n} := by
          rw [← Ideal.span_singleton_generator v.asIdeal, Ideal.span_singleton_pow]
        rw [hpow_eq] at hmem
        exact Ideal.mem_span_singleton.mp hmem
      have hdeg : (g ^ n).natDegree ≤ D.natDegree := Polynomial.natDegree_le_of_dvd hgn_dvd hD
      calc n ≤ n * g.natDegree := Nat.le_mul_of_pos_right n hg_deg
        _ = (g ^ n).natDegree := (Polynomial.natDegree_pow g n).symm
        _ ≤ D.natDegree := hdeg
  · -- D ∉ v.asIdeal: valuation is 1
    have hval : v.intValuation D = 1 := by
      by_contra h
      exact hD_mem ((v.intValuation_lt_one_iff_mem D).mp (lt_of_le_of_ne (v.intValuation_le_one D) h))
    rw [hval]
    exact le_of_lt (WithZero.exp_lt_one_iff.mpr (by linarith [D.natDegree.cast_nonneg] : -(D.natDegree : ℤ) < 0))
```

### Step 2: Fill v ∈ T \ S sorry (line ~1215 after adding lemma)

**Key idea**: Show k = P/D is integral at v using valuation division

```lean
-- Replace the sorry with:
-- Use the key bound: v.intValuation D ≥ exp(-natDegree D)
have hD_val_bound : v.intValuation D ≥ WithZero.exp (-(D.natDegree : ℤ)) :=
  intValuation_ge_exp_neg_natDegree Fq v D hD_ne
-- Show k = P/D is integral at v
have hk_val : v.valuation k ≤ 1 := by
  simp only [k]
  rw [map_div₀]
  -- val(P) ≤ exp(-(D.natDegree + 1)), val(D) ≥ exp(-D.natDegree)
  -- So val(P)/val(D) ≤ exp(-1) ≤ 1
  have hP_val' : v.valuation (algebraMap Fq[X] (RatFunc Fq) P) ≤ WithZero.exp (-(D.natDegree + 1 : ℤ)) := by
    rw [v.valuation_of_algebraMap]; exact hP_val
  have hD_val' : v.valuation (algebraMap Fq[X] (RatFunc Fq) D) ≥ WithZero.exp (-(D.natDegree : ℤ)) := by
    rw [v.valuation_of_algebraMap]; exact hD_val_bound
  have hD_ne' : v.valuation (algebraMap Fq[X] (RatFunc Fq) D) ≠ 0 := by
    rw [v.valuation_of_algebraMap]; exact v.intValuation_ne_zero hD_ne
  calc v.valuation (algebraMap _ _ P) / v.valuation (algebraMap _ _ D)
      ≤ WithZero.exp (-(D.natDegree + 1 : ℤ)) / v.valuation (algebraMap _ _ D) := by
        apply div_le_div_of_nonneg_right hP_val' (zero_lt_iff.mpr hD_ne')
    _ ≤ WithZero.exp (-(D.natDegree + 1 : ℤ)) / WithZero.exp (-(D.natDegree : ℤ)) := by
        apply div_le_div_of_nonneg_left _ (WithZero.exp_ne_zero _) hD_val'
        exact le_of_lt (WithZero.exp_lt_one_iff.mpr (by linarith))
    _ = WithZero.exp (-1) := by rw [← WithZero.exp_sub]; congr 1; ring
    _ ≤ 1 := le_of_lt (WithZero.exp_lt_one_iff.mpr (by norm_num))
-- Now use ultrametric inequality
rw [mem_adicCompletionIntegers]
have hk_coe : Valued.v (k : v.adicCompletion (RatFunc Fq)) ≤ 1 := by
  rw [valuedAdicCompletion_eq_valuation]; exact hk_val
have ha_coe : Valued.v (a.val v) ≤ 1 := by
  rw [← mem_adicCompletionIntegers]; exact ha_int
exact Valuation.map_sub_le ha_coe hk_coe
```

### Step 3: Fill v ∈ S sorry (line ~1193 after adding lemma)

**Key idea**: Show `k - y_v = (P - Py_v)/D` is integral, use ultrametric

Same valuation division argument but for `P - Py v hvS` instead of just `P`.
Then: `a_v - k = (a_v - y_v) - (k - y_v)` with both terms integral → sum integral.

### Step 4: Fill line ~1302 (exists_finite_integral_translate_with_infty_bound)

For bound ≥ 1: subtract polynomial part of k₀ to get |k|_∞ < 1.
For bound < 1: leave as sorry (not needed for main application).

---

## 🗺️ Overall RR Roadmap (After Recovery)

| Track | Status |
|-------|--------|
| **Riemann Inequality** (ℓ(D) ≤ deg+1) | ✅ COMPLETE |
| **Full RR from axioms** | ✅ PROVEN (FullRRData.lean) |
| **FullAdeles sorries** | 🔧 RECOVERY NEEDED |
| **Cocompactness** | ⬜ Next after recovery |
| **h¹(D) finiteness** | ⬜ Enables Serre duality |
| **Serre Duality** | ⬜ Final step |

---

### What's Done
- ✅ `fq_discrete_in_fullAdeles` - K is discrete in full adeles
- ✅ `fq_closed_in_fullAdeles` - K is closed in full adeles
- ✅ `isCompact_integralFullAdeles` - Integral adeles are compact (Cycle 136!)
- ✅ `HeightOneSpectrum.finite_divisors` - Set of primes dividing D is finite
- ✅ `exists_local_approximant` - For any a_v ∈ K_v, ∃ y ∈ K with a_v - y ∈ O_v
- ✅ **Cycle 141**: CRT structure applied! P exists via `exists_forall_sub_mem_ideal`
- ✅ **Cycle 141**: v ∉ T case fully proven (k integral when D is unit)

### What's Needed (3 sorries remain)

**Line 1193 - v ∈ S case**:
- Need: a_v - k ∈ O_v where k = P/D
- Have: a_v - y_v ∈ O_v and P ≡ Py_v (mod v^{e})
- Key: Show (P - Py_v)/D ∈ O_v using val_v(P - Py_v) ≥ e > val_v(D)

**Line 1215 - v ∈ T \ S case**:
- Need: a_v - k ∈ O_v where a_v ∈ O_v and k = P/D
- Have: P ≡ 0 (mod v^{e}) from CRT
- Key: Need lemma `val_v(D) ≤ D.natDegree` (multiplicity bounded by degree)
  - This is true: D = ∏ p_i^{m_i}, deg(D) = ∑ m_i·deg(p_i) ≥ m_v = val_v(D)

**Line 1302 - second theorem**:
- Depends on first theorem; inherits sorry

### CRT Structure (Cycle 141 - APPLIED)
```lean
let e : HeightOneSpectrum Fq[X] → ℕ := fun _ => D.natDegree + 1  -- uniform exponent
let target : T → Fq[X] := fun ⟨v, hv⟩ => if v ∈ S then Py v else 0
obtain ⟨P, hP⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal ... target
let k : RatFunc Fq := P / D
```

### Key Lemma Needed for Cycle 142
```lean
lemma intValuation_le_natDegree (v : HeightOneSpectrum Fq[X]) (D : Fq[X]) (hD : D ≠ 0) :
    v.intValuation D ≥ WithZero.exp (-(D.natDegree : ℤ)) := by
  -- Proof: val_v(D) counts multiplicity of v in D
  -- D = ∏ p_i^{m_i}, so deg(D) = ∑ m_i·deg(p_i) ≥ m_v = val_v(D)
  sorry
```

### Axioms Used
| Axiom | Purpose |
|-------|---------|
| `[AllIntegersCompact Fq[X] (RatFunc Fq)]` | Finite adeles compactness |
| `[Finite (Valued.ResidueField (FqtInfty Fq))]` | Infinity compactness |

---

## Cycle 141 Summary

**Goal**: Apply CRT to fill `exists_finite_integral_translate`

**Status**: 🔶 PARTIAL - CRT applied, v ∉ T case complete, 2 valuation sorries remain

**Key accomplishments**:
1. ✅ Fixed Mathlib cache issue (was missing, causing false build errors)
2. ✅ Set up CRT index type T with uniform exponent e = D.natDegree + 1
3. ✅ Applied `IsDedekindDomain.exists_forall_sub_mem_ideal` successfully
4. ✅ Defined k = P/D as the CRT solution
5. ✅ Completely filled v ∉ T case using ultrametric inequality
6. 🔶 Structured v ∈ T \ S case (needs multiplicity-degree bound)
7. 🔶 Structured v ∈ S case (needs similar valuation calculation)

**Key insight from Cycle 141**:
- The exponent e = D.natDegree + 1 is a uniform bound that works for all v ∈ T
- The key lemma needed: val_v(D) ≤ D.natDegree for any prime v dividing D
- This follows from degree additivity: deg(ab) = deg(a) + deg(b)

---

## Cycle 140 Summary

**Goal**: Fill sorries in weak approximation proofs

**Status**: 🔶 PARTIAL - Key helper proven, CRT application remains

**Key accomplishments**:
1. ✅ Proved `HeightOneSpectrum.finite_divisors`: {v | v.intValuation D < 1}.Finite
   - Uses `normalizedFactors D` which is a finite multiset
   - Maps prime factors to HeightOneSpectrum via `v.asIdeal = span {p}`
   - Key lemmas: `intValuation_lt_one_iff_mem`, `exists_mem_normalizedFactors_of_dvd`
2. ✅ Cleaned up proof structure for `exists_finite_integral_translate`
3. ✅ Documented exact CRT setup needed

**Key insight from Cycle 140**:
- The finiteness of T = S ∪ {divisors of D} was the "key lemma needed" from Cycle 139
- Now proven! Uses PID structure: height-one primes are principal, generated by irreducibles
- The CRT application is straightforward given T is finite

**Proof for `HeightOneSpectrum.finite_divisors`**:
```lean
-- v.intValuation D < 1 iff D ∈ v.asIdeal (intValuation_lt_one_iff_mem)
-- In PID: v.asIdeal = span {g} for some irreducible g
-- g | D implies normalize(g) ∈ normalizedFactors D
-- normalizedFactors D is finite
-- So {v | v.intValuation D < 1} ⊆ {v | ∃ p ∈ nF(D), v.asIdeal = span {p}}
```

---

## Cycle 139 Summary

**Goal**: Prove `exists_finite_integral_translate` via CRT approach

**Status**: 🔶 PARTIAL - Proof structure complete, CRT application pending

**Key accomplishments**:
1. Rejected principal parts / pole degree approaches (too complex for Lean)
2. Identified correct approach: CRT with enlarged set T
3. Set up proof structure with D = product of denominators
4. Proved `hDy_in_R`: D · y_v ∈ R for all v ∈ S (key intermediate step)
5. Documented the CRT application strategy

**Key insight**:
- Don't try to define n_v = ⌈-val_v(a_v)⌉ for a_v ∈ K_v (completion elements)
- Work entirely with global elements y_v ∈ K from density
- Enlarge the set to include ALL primes dividing D, not just S
- CRT gives P with the right divisibility properties, then k = P/D works

**What remains for Cycle 140**:
1. Construct T = {v : HeightOneSpectrum | v.intValuation D < 1} and prove finite
2. Set up CRT index type and targets
3. Apply `exists_forall_sub_mem_ideal`
4. Verify the valuation conditions

**Mathlib APIs needed**:
- `UniqueFactorizationMonoid.normalizedFactors` or `primeFactors` for factorization
- `exists_forall_sub_mem_ideal` for CRT
- `intValuation` properties for relating polynomial primes to HeightOneSpectrum

---

## Cycle 138 Summary

**Goal**: Prove weak approximation lemmas (`exists_finite_integral_translate`)

**Status**: 🔶 PARTIAL - Proved density step, CRT gluing still needed

**Key accomplishments**:
1. Proved `exists_local_approximant` - For any a_v ∈ K_v, ∃ y ∈ K with a_v - y ∈ O_v
   - Uses `UniformSpace.Completion.denseRange_coe` for density of K in K_v
   - Uses `Valued.isOpen_valuationSubring` to show O_v is open
   - Uses `DenseRange.exists_mem_open` to get the approximant

2. Restructured proof approach based on external feedback:
   - **Abandoned**: Principal part extraction (requires Laurent series machinery)
   - **Abandoned**: Induction on bad set (plumbing hell, bad set depends on a)
   - **Adopted**: Density + CRT gluing approach

**Key insight discovered**:
- The naive density approach doesn't quite work: each y_v from `exists_local_approximant`
  might have poles outside S, creating new bad places
- To avoid this, we actually NEED y_v with poles only at v (i.e., principal parts)
- This means partial fractions are unavoidable for the global gluing step
- The density lemma IS useful as a stepping stone, but not sufficient alone

**What remains for Cycle 139**:
- Either formalize partial fractions for RatFunc Fq, OR
- Find an alternative approach that controls pole locations

**Key mathlib APIs used**:
- `UniformSpace.Completion.denseRange_coe` - K is dense in completion
- `Valued.isOpen_valuationSubring` - valuation ring is open
- `DenseRange.exists_mem_open` - density implies intersection with open sets

---

## Cycle 137 Summary

**Goal**: Work on weak approximation (`exists_translate_in_integralFullAdeles`)

**Status**: 🔶 PARTIAL - Main structure complete, 2 helper sorries remain

**Key accomplishments**:
1. Proved `isOpen_ball_le_one_FqtInfty` - {v ≤ 1} = {v < exp(1)} for discrete valuation
2. Proved `denseRange_inftyRingHom` - density of K in completion
3. Proved `exists_approx_in_ball_infty` - existence of approximation at infinity
4. Proved `polynomial_integral_at_finite_places` - polynomials integral at finite places
5. Structured main theorem proof using:
   - Step 1: Find P with |a.2 - P|_∞ ≤ 1 (done via density)
   - Step 2: Work with b = a - diag(P)
   - Step 3: Find z clearing finite places with |z|_∞ ≤ 1 (needs CRT lemma)
   - Step 4: Combine x = P + z, verify via ultrametric inequality

**Key techniques used**:
- `UniformSpace.Completion.denseRange_coe` for density
- `Valued.isClopen_ball` for openness of valuation balls
- `WithZero.exp_lt_exp` and `omega` for discrete value group reasoning
- `Valued.v.map_sub_le_max'` for ultrametric inequality

**Remaining work for Cycle 138**:
- Prove CRT-based lemmas using `IsDedekindDomain.exists_forall_sub_mem_ideal`
- Key challenge: targets are in K_v (completion), need density argument

---

## Cycle 136 Summary

**Goal**: Prove infinity compactness (`isCompact_integralFullAdeles`)

**Status**: ✅ COMPLETE

**Key accomplishments**:
1. Proved `valued_FqtInfty_eq_inftyValuationDef` - connects Valued.v to inftyValuationDef
2. Proved `isNontrivial_FqtInfty` - 1/X has valuation exp(-1) < 1
3. Defined `rankOne_FqtInfty` - from MulArchimedean via `nonempty_rankOne_iff_mulArchimedean`
4. Proved `range_nontrivial_FqtInfty` - valuation range is nontrivial
5. Proved `isPrincipalIdealRing_integer_FqtInfty` - PID from non-dense ordering
6. Proved `isDiscreteValuationRing_integer_FqtInfty` - DVR with 1/X as uniformizer
7. Proved `completeSpace_integer_FqtInfty` - closed subset of complete space
8. Proved `isCompact_integralFullAdeles` - using compactSpace_iff theorem

**Pattern used** (same as AllIntegersCompactProof.lean):
```
CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ DVR 𝒪[K] ∧ Finite 𝓀[K]
```

**Key mathlib APIs**:
- `Valued.extension_extends` - connects valuation on completion to original
- `FunctionField.inftyValuation.X_inv` - v(1/X) = exp(-1)
- `Valuation.nonempty_rankOne_iff_mulArchimedean` - RankOne without ℝ≥0 literals
- `WithZero.exp_lt_exp` - ordering on exp values

---

## Cycle 135 Summary

**Goal**: Work on weak approximation (`exists_translate_in_integralFullAdeles`)

**Status**: ⚠️ DISCOVERED BUILD REGRESSION

**Findings**:
1. Cycle 134 commit (799bb5d) introduced broken code that never compiled
2. Used non-existent mathlib APIs:
   - `UniformSpace.Completion.coeRingHom_apply` ❌
   - `RatFunc.inv_X_ne_zero` ❌ (correct: `RatFunc.X_ne_zero`)
   - `WithZero.map_inv` ❌
3. Reverted FullAdeles.lean to Cycle 133 (aaa7633) which builds correctly

**Action Taken**: Reverted to Cycle 133 state

---

## Cycle 134 Postmortem

**What was attempted**:
- Prove `inftyValuation_isNontrivial` (X⁻¹ has valuation exp(-1) < 1)
- Get `rankOne_FqtInfty` via MulArchimedean
- Prove `instDVR_FqtInfty` (DVR with X⁻¹ as uniformizer)
- Prove `completeSpace_integer_FqtInfty`

**Why it failed**:
- Code used mathlib APIs that don't exist
- Commit was made without running build (stale cache issue?)

**Correct approach for Cycle 136**:
1. Use `RatFunc.X_ne_zero` (not `inv_X_ne_zero`)
2. For completion embedding, use `UniformSpace.Completion.coe_inj`
3. For valuation of inverse, use `map_inv₀` or direct calculation
4. Test build BEFORE committing

---

## Cycle 133 Summary

**Goal**: Complete infinity compactness for `isCompact_integralFullAdeles`

**Status**: 🔶 PARTIAL - Structure complete, blocked on ℝ≥0 tactics

**Progress**:
- Added imports for `WithZeroMulInt.toNNReal` and `LocallyCompact`
- Wrote full proof strategy in code comments
- Identified key approach: use `nonempty_rankOne_iff_mulArchimedean`

---

## Architecture Summary

```
FullAdeleRing Fq := FiniteAdeleRing Fq[X] (RatFunc Fq) × FqtInfty Fq

K = RatFunc Fq embeds diagonally:
  fqFullDiagonalEmbedding : K →+* FullAdeleRing

Key theorems (in FullAdeles.lean):
  ✅ fq_discrete_in_fullAdeles  -- K is discrete
  ✅ fq_closed_in_fullAdeles    -- K is closed
  ✅ isCompact_integralFullAdeles  -- integral adeles compact
  ⚪ exists_translate_in_integralFullAdeles  -- weak approximation (sorry)
```

---

## References

- `AllIntegersCompactProof.lean` - Pattern for compactness via DVR+complete+finite
- `Mathlib/Topology/Algebra/Valued/LocallyCompact.lean` - compactSpace_iff lemma
- `Valuation.nonempty_rankOne_iff_mulArchimedean` - KEY: gets RankOne without ℝ≥0 literals
