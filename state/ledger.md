# Ledger

Tactical tracking for Riemann-Roch formalization.

---

## Current State

**Build**: ✅ Compiles (2 sorries in DimensionGeneral.lean + 1 sorry in PlaceDegree.lean)
**Result**: Riemann-Roch for P¹ (linear places) + Generalized gap bound + Finiteness for all effective D
**Cycle**: 261 (In Progress)

---

## What's Proved

```lean
theorem riemann_roch_p1 (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    (ell_ratfunc_projective D : ℤ) -
      (ellV3 (k := Fq) (R := Polynomial Fq) (K := RatFunc Fq)
        (p1Canonical Fq - DivisorV3.ofAffine D) : ℤ) =
    D.deg + 1 - (p1Genus : ℤ)
```

The full Riemann-Roch formula for P¹ with:
- ℓ(D) = deg(D) + 1 for effective D with linear support
- ℓ(K-D) = 0 for effective D
- g = 0 (genus)

---

## Limitations

**This is NOT full P¹ Riemann-Roch.**

The `IsLinearPlaceSupport` hypothesis restricts to divisors supported at Fq-rational points:

```lean
def IsLinearPlaceSupport (D : DivisorV2 (Polynomial Fq)) : Prop :=
  ∀ v ∈ D.support, ∃ α : Fq, v = linearPlace α
```

Not covered:
- Places of degree > 1 (e.g., (X² + X + 1) over F₂)
- Divisors mixing linear and non-linear places

Full P¹ RR is mathematically trivial - the "vibe coding" methodology is more interesting than the result.

---

## Cycle 261 Summary

**Task**: Add helper lemmas for uniformizer valuation at other primes (prerequisite for evaluationMapAt_surj)

**Status**: 🔄 In Progress - Helper lemmas added, 1 sorry remains

**What was done**:

Added to `PlaceDegree.lean`:
```lean
-- Coprimality of distinct primes (sorry-free)
lemma generator_not_mem_other_prime (v w : HeightOneSpectrum (Polynomial k))
    (hw : w ≠ v) : generator k v ∉ w.asIdeal

lemma generator_intValuation_at_other_prime (v w : HeightOneSpectrum (Polynomial k))
    (hw : w ≠ v) : w.intValuation (generator k v) = 1

-- Uniformizer at other primes (1 sorry - proving π | generator in UFD)
lemma uniformizerAt_not_mem_other_prime (v w : HeightOneSpectrum (Polynomial k))
    (hw : w ≠ v) : uniformizerAt v ∉ w.asIdeal

lemma uniformizerAt_intValuation_at_other_prime (v w : HeightOneSpectrum (Polynomial k))
    (hw : w ≠ v) : w.intValuation (uniformizerAt v) = 1
```

**The remaining sorry** (line 255 in PlaceDegree.lean):
```lean
-- Need: π | generator(v)
-- Both have v-valuation exp(-1), so they're associates
-- In k[X], valuation exp(-1) means exactly one factor of the prime
-- π = u * generator(v) for some unit u
```

This is a UFD argument: in k[X], elements with the same v-valuation (both = exp(-1)) differ by units coprime to the prime. The proof requires extracting the unit from valuation equality.

**Next**: Either fill this sorry or proceed with evaluationMapAt_surj using these lemmas.

---

## Cycle 260 Summary

**Task**: Fill sorries in DimensionGeneral.lean - finiteness instance

**Status**: ✅ Partial - Finiteness instance complete, 2 sorries remain

**What was done**:

1. **Added helper lemmas to PlaceDegree.lean** (as planned):
```lean
lemma degWeighted_neg (D : DivisorV2 (Polynomial k)) :
    degWeighted k (-D) = -degWeighted k D

lemma degWeighted_sub (D E : DivisorV2 (Polynomial k)) :
    degWeighted k (D - E) = degWeighted k D - degWeighted k E
```

2. **Filled degWeighted subtraction sorry** (was line 201, now trivial with degWeighted_sub)

3. **Filled RRSpace_ratfunc_projective_effective_finite** (the finiteness instance):
   - Strong induction on degWeighted(D)
   - Base case: degWeighted = 0 ⟹ D = 0 ⟹ L(0) is finite
   - Inductive step: D = D' + [v] where D' has smaller degWeighted
     - L(D') finite by IH
     - Built evaluation map ψ : L(D' + [v]) → κ(v)
     - Proved ker(ψ) = LD (comap of L(D'))
     - Used `Module.Finite.of_injective` + `Module.Finite.of_submodule_quotient`

**Key technical insight** (from Gemini):
```lean
-- 1. Descended map is injective
have hinj : Function.Injective desc :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ h_ker_le_LD)

-- 2. Quotient is finite (injection into finite κ(v))
haveI : Module.Finite k (L(D') ⧸ LD) := Module.Finite.of_injective desc hinj

-- 3. Extension of finite by finite is finite
exact Module.Finite.of_submodule_quotient LD
```

**Remaining sorries (2 total)**:
| Line | Lemma | What's needed |
|------|-------|---------------|
| 114 | `evaluationMapAt_surj` | Construct q/generator(v)^{D(v)+1} preimages |
| 137 | `ell_ratfunc_projective_gap_eq` | Combine surjectivity with upper bound |

**Progress**: 4 sorries → 2 sorries

---

## Cycle 259 Summary

**Task**: Remove `IsLinearPlaceSupport` - dimension formula generalization

**Status**: ✅ Partial - DimensionGeneral.lean skeleton created

**New file**: `RrLean/RiemannRochV2/P1Instance/DimensionGeneral.lean` (4 sorries)

**What was done**:
Created the structure for proving `ℓ(D) = degWeighted(D) + 1` for all effective divisors:

```lean
-- Main theorem (depends on sorries)
theorem ell_ratfunc_projective_eq_degWeighted_plus_one (D : DivisorV2 (Polynomial k))
    (hD : D.Effective) :
    ell_ratfunc_projective D = (degWeighted k D).toNat + 1

-- Key intermediate results:
theorem evaluationMapAt_surj  -- surjectivity for tight gap bound
theorem ell_ratfunc_projective_gap_eq  -- gap = deg(v) exactly
instance RRSpace_ratfunc_projective_effective_finite  -- finiteness for all effective D
```

**Helper lemmas proved (sorry-free)**:
- `degWeighted_nonneg_of_effective` - degWeighted(D) ≥ 0 for effective D
- `effective_degWeighted_zero_imp_zero` - degWeighted = 0 ⟹ D = 0
- `exists_pos_of_degWeighted_pos` - degWeighted > 0 ⟹ ∃ v, D(v) > 0

**Remaining sorries (4 total)**:
| Line | Lemma | What's needed |
|------|-------|---------------|
| 56 | `evaluationMapAt_surj` | Construct q/generator(v) preimages |
| 79 | `ell_ratfunc_projective_gap_eq` | Combine surjectivity with gap bound |
| 87 | `RRSpace_ratfunc_projective_effective_finite` | Induction on degWeighted |
| 201 | degWeighted subtraction | Technical Finsupp calculation |

**CRITICAL: Finsupp Arithmetic Hell**

The cycle got stuck on line 201 trying to prove:
```lean
degWeighted k (D - single v 1) = degWeighted k D - deg(v)
```

**The fix** (for Cycle 260): Add these lemmas to `PlaceDegree.lean`:

```lean
-- Add to PlaceDegree.lean
lemma degWeighted_neg (D : DivisorV2 (Polynomial k)) :
    degWeighted k (-D) = - degWeighted k D := by
  unfold degWeighted
  rw [Finsupp.sum_neg_index]
  · simp only [neg_mul, Finsupp.sum_neg]
  · intro _; ring

lemma degWeighted_sub (D E : DivisorV2 (Polynomial k)) :
    degWeighted k (D - E) = degWeighted k D - degWeighted k E := by
  rw [sub_eq_add_neg, degWeighted_add, degWeighted_neg, sub_eq_add_neg]
```

This lifts the proof above raw Finsupp manipulation, avoiding the fragile `calc` blocks.

---

## Cycle 258 Summary

**Task**: Generalize gap bound from linear places to arbitrary places

**Status**: ✅ Complete - GapBoundGeneral.lean finished

**New file completed**: `RrLean/RiemannRochV2/P1Instance/GapBoundGeneral.lean` ✅ (0 sorries)

**What was done**:
Extended the gap bound theorem from linear places (where gap ≤ 1) to arbitrary places (where gap ≤ deg(v)):

```lean
-- Generalized gap bound: ℓ(D + [v]) ≤ ℓ(D) + deg(v)
theorem ell_ratfunc_projective_gap_le_general (D : DivisorV2 (Polynomial k))
    (v : HeightOneSpectrum (Polynomial k))
    [hfin : Module.Finite k (RRSpace_ratfunc_projective (D + DivisorV2.single v 1))] :
    ell_ratfunc_projective (D + DivisorV2.single v 1) ≤
    ell_ratfunc_projective D + degree k v
```

**Key lemmas (all sorry-free)**:
```lean
-- Monotonicity for arbitrary places
lemma RRSpace_ratfunc_projective_mono_general : L(D) ⊆ L(D + [v])

-- Residue field finiteness for arbitrary places
instance residueField_finite : Module.Finite k (k[X] ⧸ v.asIdeal)
instance residueFieldAtPrime_finite : Module.Finite k (κ(v))

-- Residue field dimension = place degree
lemma finrank_residueFieldAtPrime_eq_degree : finrank k (κ(v)) = deg(v)
```

**Technical notes**:
- Used `Polynomial.Monic.finite_adjoinRoot` for quotient finiteness
- The proof follows the same structure as the linear case: evaluation map with kernel = L(D), quotient embeds in κ(v)
- For linear places, deg(v) = 1, recovering the original gap bound

**Verification**:
```bash
lake build RrLean.RiemannRochV2.P1Instance.GapBoundGeneral  # ✅
grep -n "sorry" .../GapBoundGeneral.lean  # (no output)
```

---

## Cycle 257 Summary

**Task**: Remove `IsLinearPlaceSupport` restriction - infrastructure phase

**Status**: ✅ Complete - PlaceDegree.lean finished

**What was done**:
The Mathlib API issues from the previous WIP session were resolved:
- `IsUnit.mul_iff` field notation → replaced with `irreducible_isUnit_mul`
- `Ideal.span_singleton_eq_span_singleton` notation → used `Submodule.span_singleton_eq_span_singleton` with proper conversion

**New file completed**: `RrLean/RiemannRochV2/P1Instance/PlaceDegree.lean` ✅ (0 sorries)

**Key definitions and lemmas (all sorry-free)**:
```lean
-- Generator of a HeightOneSpectrum (monic irreducible polynomial)
noncomputable def generator (v : HeightOneSpectrum (Polynomial k)) : Polynomial k

-- Degree of a place = natDegree of its generator
def degree (v : HeightOneSpectrum (Polynomial k)) : ℕ := (generator k v).natDegree

-- Weighted degree of a divisor
def degWeighted (D : DivisorV2 (Polynomial k)) : ℤ :=
  D.sum (fun v n => n * (degree k v : ℤ))

-- Key lemmas:
lemma degree_pos : 0 < degree k v
lemma linearPlace_degree_eq_one (α : k) : degree k (linearPlace α) = 1
theorem finrank_residueField_eq_degree : finrank k (Polynomial k ⧸ v.asIdeal) = degree k v
lemma degWeighted_eq_deg_of_linear : degWeighted k D = D.deg  -- when all places are linear
lemma degWeighted_single : degWeighted k (single v n) = n * (degree k v : ℤ)
lemma degWeighted_add : degWeighted k (D + E) = degWeighted k D + degWeighted k E
```

**Verification**:
```bash
lake build RrLean.RiemannRochV2.P1Instance.PlaceDegree  # ✅
grep -c "sorry" .../PlaceDegree.lean  # 0
```

---

## Cycle 256 Summary

**Task**: Assemble full Riemann-Roch theorem for P¹

**New File**: `RrLean/RiemannRochV2/P1Instance/P1RiemannRoch.lean`

**Key results**:
```lean
-- Main Riemann-Roch theorem
theorem riemann_roch_p1 (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    (ell_ratfunc_projective D : ℤ) -
      (ellV3 (k := Fq) (R := Polynomial Fq) (K := RatFunc Fq)
        (p1Canonical Fq - DivisorV3.ofAffine D) : ℤ) =
    D.deg + 1 - (p1Genus : ℤ)

-- Alternative formulation
theorem riemann_roch_p1' (D : DivisorV2 (Polynomial Fq))
    (hD : D.Effective) (hDlin : IsLinearPlaceSupport D) :
    (ell_ratfunc_projective D : ℤ) -
      (ellV3 (k := Fq) ... (p1Canonical Fq - DivisorV3.ofAffine D) : ℤ) =
    D.deg + 1
```

**Mathematical content**:
- Combined results from two frameworks:
  - `ell_ratfunc_projective_eq_deg_plus_one`: ℓ(D) = deg(D) + 1
  - `ellV3_p1Canonical_sub_ofAffine_eq_zero`: ℓ(K-D) = 0
- This gives the full Riemann-Roch formula: ℓ(D) - ℓ(K-D) = deg(D) + 1 - g

**Verification**:
```bash
lake build RrLean.RiemannRochV2.P1Instance.P1RiemannRoch  # ✅
grep -n "sorry" RrLean/RiemannRochV2/P1Instance/P1RiemannRoch.lean  # (no output)
#print axioms riemann_roch_p1  # [propext, Classical.choice, Quot.sound] - no sorryAx!
```

---

## Cycle 255 Summary (Previous)

**Task**: Complete L(K-D) vanishing proof by filling the sorry in P1VanishingLKD.lean

**Key insight**: The bottleneck was proving "v(f) ≤ 1 at all finite places ⟹ f is a polynomial".

**Strategy** (suggested by Gemini):
Instead of fighting `WithZero (Multiplicative ℤ)` arithmetic, work with polynomial structure:
1. For f = num/denom (coprime, monic denom), if denom ≠ 1:
2. Some irreducible q divides denom (UFD property)
3. At the HeightOneSpectrum for q: v(denom) < 1 but v(num) = 1 (coprimality)
4. So v(num) > v(denom), which means ¬(v(f) ≤ 1), contradiction

**New lemmas added to P1VanishingLKD.lean**:
```lean
def heightOneSpectrum_of_prime (q : Polynomial K) (hprime : Prime q) :
    HeightOneSpectrum (Polynomial K)

theorem exists_valuation_not_le_one_of_denom_ne_one (f : RatFunc K) (hdenom : f.denom ≠ 1) :
    ∃ v : HeightOneSpectrum (Polynomial K), ¬(v.valuation (RatFunc K) f ≤ 1)

theorem denom_eq_one_of_valuation_le_one_forall (f : RatFunc K)
    (hf : ∀ v : HeightOneSpectrum (Polynomial K), v.valuation (RatFunc K) f ≤ 1) :
    f.denom = 1

theorem eq_algebraMap_of_valuation_le_one_forall (f : RatFunc K)
    (hf : ∀ v : HeightOneSpectrum (Polynomial K), v.valuation (RatFunc K) f ≤ 1) :
    f = algebraMap (Polynomial K) (RatFunc K) f.num
```

**Main theorem now sorry-free**:
```lean
theorem RRSpaceV3_p1Canonical_sub_ofAffine_eq_zero
    {D : DivisorV2 (Polynomial Fq)} (hD : D.Effective) :
    RRSpaceV3 (Polynomial Fq) (RatFunc Fq) (p1Canonical Fq - DivisorV3.ofAffine D) = {0}
```

**Verification**:
```bash
lake build RrLean.RiemannRochV2.P1Instance.P1VanishingLKD  # ✅
lake build RrLean.RiemannRochV2.SerreDuality.Smoke  # ✅ Still passes
grep -n "sorry" RrLean/RiemannRochV2/P1Instance/P1VanishingLKD.lean  # (no output)
```

---

## Cycle 254 Summary (Previous)

**Task**: Prove L(K-D) vanishing for effective D on P¹

**New File**: `RrLean/RiemannRochV2/P1Instance/P1VanishingLKD.lean`

**Key insight**: For P¹, the Mathlib convention for infinity valuation is:
```lean
v_∞(p) = exp(deg(p)) for nonzero polynomial p
```
This means higher degree polynomials have LARGER valuations at infinity, not smaller.

**Key lemmas**:
```lean
lemma p1InftyValuation_polynomial (p : Polynomial Fq) (hp : p ≠ 0) :
    (p1InftyPlace Fq).valuation (algebraMap (Polynomial Fq) (RatFunc Fq) p) =
    WithZero.exp (p.natDegree : ℤ)

lemma p1InftyValuation_polynomial_not_le_exp_neg2 (p : Polynomial Fq) (hp : p ≠ 0) :
    ¬ (p1InftyPlace Fq).valuation (algebraMap (Polynomial Fq) (RatFunc Fq) p) ≤
      WithZero.exp (-2 : ℤ)
```

---

## Cycle 253 Summary (Previous)

**Task**: Define the canonical divisor K = -2[∞] for P¹

**New File**: `RrLean/RiemannRochV2/P1Instance/P1Canonical.lean`

**Key definitions**:
```lean
/-- The canonical divisor on P¹ = RatFunc Fq. K = -2[∞]. -/
def p1Canonical : DivisorV3 Fq[X] (RatFunc Fq) :=
  DivisorV3.singleInfinite (p1InftyPlace Fq) (-2)

/-- The genus of P¹ is 0. -/
def p1Genus : ℕ := 0
```

**Key lemmas**:
- `deg_p1Canonical` : degree is -2
- `p1Canonical_at_infty` : coefficient at ∞ is -2
- `p1Canonical_at_finite` : coefficient at finite places is 0
- `p1_genus_formula` : deg(K) = 2g - 2 holds for P¹
- `deg_p1Canonical_sub` : deg(K - D) = -2 - deg(D)
- `deg_p1Canonical_sub_neg` : if deg(D) ≥ -1, then deg(K - D) ≤ -1

**Insight**: The canonical divisor for P¹ arises entirely from the place at infinity.
Mathlib's `differentIdeal` machinery only captures finite places (the "Affine Trap"),
so there's no useful connection for P¹. For P¹, we define K = -2[∞] directly.

**Verification**:
```bash
lake build RrLean.RiemannRochV2.P1Instance.P1Canonical  # ✅
lake build RrLean.RiemannRochV2.SerreDuality.Smoke  # ✅ Still passes
```

*For cycles 241-252, see `ledger_archive.md`.*

---

## Sorries

**6 sorries total** in non-archived code:
- `Abstract.lean`: 3 (placeholder `AdelicRRData` instance fields)
- `DimensionGeneral.lean`: 2 (evaluationMapAt_surj, ell_ratfunc_projective_gap_eq)
- `PlaceDegree.lean`: 1 (uniformizerAt_not_mem_other_prime - π | generator(v) in UFD)

**Files with sorries** (Cycle 261):
- PlaceDegree.lean: ⚠️ 1 sorry (uniformizerAt_not_mem_other_prime - π | generator(v) in UFD)

**Sorry-free files** (confirmed Cycle 261):
- GapBoundGeneral.lean ✅ (Generalized gap bound)
- P1RiemannRoch.lean ✅ (Full Riemann-Roch theorem)
- P1VanishingLKD.lean ✅
- DimensionCore.lean ✅
- AdelicH1Full.lean ✅
- DimensionScratch.lean ✅
- Place.lean ✅
- DivisorV3.lean ✅
- RRSpaceV3.lean ✅
- P1Place.lean ✅
- P1Canonical.lean ✅
- All other SerreDuality files ✅

6 dead-code lemmas in `RrLean/Archive/SorriedLemmas.lean`.

---

## Build Commands

```bash
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "sorryAx"
lake build RrLean.RiemannRochV2.SerreDuality.Smoke 2>&1 | grep "depends on axioms"
```

**See also**: `state/PROOF_CHAIN.md` for the full import chain and verification details.

---

## Next Steps

### Removing `IsLinearPlaceSupport` - In Progress

**Cycle 260 complete**: Finiteness instance filled, 2 sorries remain.

**What's been done**:
- ✅ PlaceDegree.degree - place degree infrastructure
- ✅ PlaceDegree.degWeighted_neg, degWeighted_sub - arithmetic lemmas
- ✅ GapBoundGeneral - gap ≤ deg(v) for arbitrary places
- ✅ DimensionGeneral skeleton - induction structure
- ✅ Helper lemmas: degWeighted_nonneg, effective_zero, exists_pos
- ✅ **RRSpace_ratfunc_projective_effective_finite** - finiteness for all effective D

**Immediate (Cycle 261)**: Fill remaining 2 sorries

1. `evaluationMapAt_surj` (line 114) - construct q/generator(v)^{D(v)+1} preimages
   - For any c ∈ κ(v), represented by polynomial q with deg(q) < deg(generator)
   - The element q/generator(v)^{D(v)+1} ∈ L(D+[v]) and maps to c

2. `ell_ratfunc_projective_gap_eq` (line 137) - tight gap bound
   - Upper bound: already have gap ≤ deg(v) from GapBoundGeneral
   - Lower bound: surjectivity implies quotient ≅ κ(v), so gap = deg(v)

**After**: Update `riemann_roch_p1` to use degWeighted instead of deg

### Alternative Directions

**Option B**: Fill Abstract.lean sorries
- Connect P¹ projective infrastructure to the abstract framework

**Option C**: Move to higher genus curves
- Elliptic curves (g = 1)
- Requires different coordinate ring structure

---

## Refactor Status

**Phase**: 0 (Cleanup) - mostly complete
**Docs created**: `INVENTORY_REPORT.md`, `REFACTOR_PLAN.md`
**Next phase**: 1 (Complete incomplete infrastructure)

See `REFACTOR_PLAN.md` for full roadmap.

---

*For historical cycles 1-240, see `ledger_archive.md`*
