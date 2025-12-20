import RrLean.RiemannRochV2.AdelicH1v2
import RrLean.RiemannRochV2.DifferentIdealBridge
import RrLean.RiemannRochV2.Residue
import Mathlib.Algebra.Polynomial.PartialFractions

/-!
# Serre Duality Pairing

This module defines the Serre duality pairing between H¹(D) and L(K-D).

## Strategy

The goal is to construct a perfect pairing:
```
⟨·,·⟩ : H¹(D) × L(K-D) → k
```

that proves `h¹(D) = ℓ(K-D)`.

### Mathematical Background

In the classical setting, the pairing is constructed via residues:
```
⟨[a], f⟩ := ∑_v res_v(a_v · f)
```

where `res_v : K_v → k` is the local residue at place v.

### Implementation Approach

Mathlib does not provide geometric residue maps for function fields.
Instead, we explore using the algebraic trace dual machinery:
- `Algebra.traceForm K L` : the bilinear form `(x, y) ↦ trace K L (x * y)`
- `Submodule.traceDual A K I` : elements whose trace with I lands in A
- `FractionalIdeal.dual A K I` : the dual fractional ideal

The key question is whether we can define the global pairing using
`Algebra.trace` on adeles, avoiding explicit residue maps.

## Main Definitions

* `serrePairing` : The bilinear pairing H¹(D) × L(K-D) → k (types only, proof is sorry)

## Status (Cycle 156)

This module defines TYPES ONLY. The goal is to get the pairing definition
to typecheck. Proofs will be added in subsequent cycles.

## References

* Mathlib: `RingTheory.DedekindDomain.Different` for trace dual
* Liu "Algebraic Geometry and Arithmetic Curves" Chapter 7
-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra k R]
variable (K : Type*) [Field K] [Algebra k K] [Algebra R K] [IsFractionRing R K]
variable [IsScalarTower k R K]

/-! ## The Serre Duality Pairing (Types Only)

We define the bilinear pairing between H¹(D) and L(K-D).

The domain is `SpaceModule k R K D` = H¹(D) = 𝔸_K / (K + A_K(D))
The codomain argument is `RRSpace_proj k R K (canonical - D)` = L(K-D)
The result is in the base field k.
-/

section PairingDefinition

variable (canonical : DivisorV2 R)

/-- The Serre duality pairing between H¹(D) and L(K-D).

This bilinear map will be shown to be a perfect pairing, proving h¹(D) = ℓ(K-D).

**Construction idea (to be implemented):**
1. For `[a] ∈ H¹(D)` (class of adele a) and `f ∈ L(K-D)`:
2. Consider the product `a · f` where f is embedded diagonally in adeles
3. Apply a "global trace/residue" operation to get an element of k
4. Show this is well-defined on the quotient H¹(D)

**Key mathematical facts needed:**
- Residue theorem: ∑_v res_v(g) = 0 for any global g ∈ K
- Product conditions: if a ∈ A_K(D) and f ∈ L(K-D), then a·f has no residues

**Current status:** Definition only, proof is sorry.
-/
def serrePairing (D : DivisorV2 R) :
    AdelicH1v2.SpaceModule k R K D →ₗ[k]
    (RRSpace_proj k R K (canonical - D)) →ₗ[k] k := by
  -- This construction will be filled in future cycles
  -- For now we just need the types to compile
  sorry

/-- The pairing is well-defined: independent of representative in H¹(D).

This will use the residue theorem: if `a ∈ K` (global element),
then the "residue sum" of `a · f` is zero for any `f`.
-/
lemma serrePairing_wellDefined (D : DivisorV2 R)
    (a : FiniteAdeleRing R K)
    (ha : a ∈ AdelicH1v2.globalPlusBoundedSubmodule k R K D)
    (f : RRSpace_proj k R K (canonical - D)) :
    serrePairing k R K canonical D (Submodule.Quotient.mk a) f = 0 := by
  sorry

/-- Left non-degeneracy: if ⟨[a], f⟩ = 0 for all f ∈ L(K-D), then [a] = 0 in H¹(D).

This is the key content of Serre duality on the H¹ side.
-/
lemma serrePairing_left_nondegen (D : DivisorV2 R)
    (x : AdelicH1v2.SpaceModule k R K D)
    (hx : ∀ f : RRSpace_proj k R K (canonical - D),
          serrePairing k R K canonical D x f = 0) :
    x = 0 := by
  sorry

/-- Right non-degeneracy: if ⟨[a], f⟩ = 0 for all [a] ∈ H¹(D), then f = 0 in L(K-D).

This is the key content of Serre duality on the L(K-D) side.
-/
lemma serrePairing_right_nondegen (D : DivisorV2 R)
    (f : RRSpace_proj k R K (canonical - D))
    (hf : ∀ x : AdelicH1v2.SpaceModule k R K D,
          serrePairing k R K canonical D x f = 0) :
    f = 0 := by
  sorry

end PairingDefinition

/-! ## Dimension Equality from Perfect Pairing

Once we establish non-degeneracy, the perfect pairing gives dimension equality.
-/

section DimensionEquality

variable (canonical : DivisorV2 R)

/-- A perfect pairing between finite-dimensional spaces implies equal dimensions.

This is the abstract linear algebra fact:
If V × W → k is a perfect (non-degenerate) bilinear pairing
with V, W finite-dimensional over k, then dim V = dim W.
-/
lemma finrank_eq_of_perfect_pairing
    (D : DivisorV2 R)
    [Module.Finite k (AdelicH1v2.SpaceModule k R K D)]
    [Module.Finite k (RRSpace_proj k R K (canonical - D))]
    (hleft : ∀ x : AdelicH1v2.SpaceModule k R K D,
             (∀ f, serrePairing k R K canonical D x f = 0) → x = 0)
    (hright : ∀ f : RRSpace_proj k R K (canonical - D),
              (∀ x, serrePairing k R K canonical D x f = 0) → f = 0) :
    Module.finrank k (AdelicH1v2.SpaceModule k R K D) =
    Module.finrank k (RRSpace_proj k R K (canonical - D)) := by
  -- The pairing gives us two linear maps:
  -- φ : V → Dual k W (from serrePairing directly)
  -- ψ : W → Dual k V (the transpose)
  -- Left non-deg implies φ is injective ⟹ finrank V ≤ finrank W
  -- Right non-deg implies ψ is injective ⟹ finrank W ≤ finrank V
  -- Hence equality.
  set V := AdelicH1v2.SpaceModule k R K D with hV_def
  set W := RRSpace_proj k R K (canonical - D) with hW_def
  -- φ : V →ₗ[k] (W →ₗ[k] k) = serrePairing
  let φ : V →ₗ[k] (Module.Dual k W) := serrePairing k R K canonical D
  -- ψ : W →ₗ[k] (V →ₗ[k] k) : flip of the pairing
  let ψ : W →ₗ[k] (Module.Dual k V) :=
    LinearMap.flip (serrePairing k R K canonical D)
  -- hleft says φ is injective
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have h : x - y = 0 := hleft (x - y) (fun f => by
      have heq : φ x = φ y := hxy
      have := LinearMap.ext_iff.mp heq f
      simp only [φ] at this
      rw [map_sub, LinearMap.sub_apply, this, sub_self])
    exact sub_eq_zero.mp h
  -- hright says ψ is injective
  have hψ_inj : Function.Injective ψ := by
    intro f g hfg
    have h : f - g = 0 := hright (f - g) (fun x => by
      have heq : ψ f = ψ g := hfg
      have := LinearMap.ext_iff.mp heq x
      simp only [ψ, LinearMap.flip_apply] at this
      rw [(serrePairing k R K canonical D x).map_sub, this, sub_self])
    exact sub_eq_zero.mp h
  -- finrank V ≤ finrank (Dual k W) = finrank W
  have h1 : Module.finrank k V ≤ Module.finrank k W := by
    calc Module.finrank k V
        ≤ Module.finrank k (Module.Dual k W) :=
          LinearMap.finrank_le_finrank_of_injective hφ_inj
      _ = Module.finrank k W := Subspace.dual_finrank_eq
  -- finrank W ≤ finrank (Dual k V) = finrank V
  have h2 : Module.finrank k W ≤ Module.finrank k V := by
    calc Module.finrank k W
        ≤ Module.finrank k (Module.Dual k V) :=
          LinearMap.finrank_le_finrank_of_injective hψ_inj
      _ = Module.finrank k V := Subspace.dual_finrank_eq
  exact Nat.le_antisymm h1 h2

/-- Serre duality: h¹(D) = ℓ(K - D).

This is the main theorem that connects adelic cohomology to Riemann-Roch spaces.
Combined with the adelic Riemann-Roch equation `ℓ(D) - h¹(D) = deg(D) + 1 - g`,
this gives the full Riemann-Roch theorem.
-/
theorem serre_duality
    (D : DivisorV2 R)
    [Module.Finite k (AdelicH1v2.SpaceModule k R K D)]
    [Module.Finite k (RRSpace_proj k R K (canonical - D))] :
    AdelicH1v2.h1_finrank k R K D = ell_proj k R K (canonical - D) := by
  unfold AdelicH1v2.h1_finrank ell_proj
  exact finrank_eq_of_perfect_pairing k R K canonical D
    (serrePairing_left_nondegen k R K canonical D)
    (serrePairing_right_nondegen k R K canonical D)

end DimensionEquality

/-! ## Instantiating AdelicRRData

The Serre duality theorem allows us to instantiate `AdelicRRData`,
which then gives the full Riemann-Roch theorem via `adelicRRData_to_FullRRData`.
-/

section InstantiateAdelicRRData

variable (canonical : DivisorV2 R) (genus : ℕ)

/-- Instantiate AdelicRRData using Serre duality.

This requires proving all six axioms of AdelicRRData:
1. h1_finite : H¹(D) is finite-dimensional
2. ell_finite : L(D) is finite-dimensional
3. h1_vanishing : h¹(D) = 0 for deg(D) >> 0
4. adelic_rr : ℓ(D) - h¹(D) = deg(D) + 1 - g
5. serre_duality : h¹(D) = ℓ(K-D)
6. deg_canonical : deg(K) = 2g - 2

The serre_duality axiom comes from our theorem above.
The other axioms require additional infrastructure.
-/
def mkAdelicRRData
    (h1_finite : ∀ D, Module.Finite k (AdelicH1v2.SpaceModule k R K D))
    (ell_finite : ∀ D, Module.Finite k (RRSpace_proj k R K D))
    (h1_vanishing : ∀ D, D.deg > 2 * (genus : ℤ) - 2 →
                    AdelicH1v2.h1_finrank k R K D = 0)
    (adelic_rr : ∀ D, (ell_proj k R K D : ℤ) - AdelicH1v2.h1_finrank k R K D =
                 D.deg + 1 - genus)
    (deg_canonical : canonical.deg = 2 * (genus : ℤ) - 2) :
    AdelicH1v2.AdelicRRData k R K canonical genus where
  h1_finite := h1_finite
  ell_finite := ell_finite
  h1_vanishing := h1_vanishing
  adelic_rr := adelic_rr
  serre_duality := fun D => by
    haveI := h1_finite D
    haveI := ell_finite (canonical - D)
    exact serre_duality k R K canonical D
  deg_canonical := deg_canonical

end InstantiateAdelicRRData

/-! ## Next Steps (Future Cycles)

To complete the Serre duality proof, we need:

### Step 1: Define the pairing construction
Replace the sorry in `serrePairing` with an actual construction.
Options:
- Use local traces on completions + sum over places
- Use global trace on a suitable subspace
- Use fractional ideal duality machinery

### Step 2: Prove well-definedness
Show the pairing descends to the quotient H¹(D).
Key tool: residue theorem (∑_v res_v = 0 on K).

### Step 3: Prove non-degeneracy
Show both left and right kernels are trivial.
Key tools:
- `FractionalIdeal.dual_dual` : involution property
- `differentIdeal_ne_bot` : non-vanishing of different
- Strong approximation for H¹ vanishing

### Step 4: Prove supporting axioms
- h1_finite : compactness of integral adeles + discreteness of K
- h1_vanishing : strong approximation for large degree
- adelic_rr : Euler characteristic computation

### Warning Signs (abort if you see these)
- Trying to define res_v via Laurent series expansion
- Building coefficient extraction for local fields
- More than 100 lines without a compiling definition
- Needing to construct uniformizers explicitly
-/

/-! ## Concrete Pairing for RatFunc Fq

For the specific case K = RatFunc Fq, we can define the Serre pairing explicitly
using the residue infrastructure from Residue.lean.

The pairing is:
  ⟨[a], f⟩ = ∑_v res_v(a_v · f)

where the sum is over all places v (linear places + infinity).

This section provides the concrete implementation that will be used to
instantiate the abstract serrePairing.
-/

section ConcreteRatFuncPairing

variable {Fq : Type*} [Field Fq]

open RiemannRochV2.Residue
open Classical

/-- Residue sum over all linear places for a rational function.

This sums res_α(f) over all α ∈ Fq (the linear places (X - α)).
For a finite field Fq, this is a finite sum.

Note: This captures residues at all degree-1 places. For a complete
residue theorem, we also need residues at higher-degree irreducible
places (handled by residueAtIrreducible) and infinity (residueAtInfty).
-/
def residueSumFinite [Fintype Fq] (f : RatFunc Fq) : Fq :=
  ∑ α : Fq, residueAt α f

/-- The finite residue sum is linear: respects addition. -/
theorem residueSumFinite_add [Fintype Fq] (f g : RatFunc Fq) :
    residueSumFinite (f + g) = residueSumFinite f + residueSumFinite g := by
  simp only [residueSumFinite, residueAt_add]
  rw [Finset.sum_add_distrib]

/-- The finite residue sum is linear: respects scalar multiplication. -/
theorem residueSumFinite_smul [Fintype Fq] (c : Fq) (f : RatFunc Fq) :
    residueSumFinite (c • f) = c * residueSumFinite f := by
  simp only [residueSumFinite, residueAt_smul]
  rw [← Finset.mul_sum]

/-- The finite residue sum as a linear map. -/
def residueSumFinite_linearMap [Fintype Fq] : RatFunc Fq →ₗ[Fq] Fq where
  toFun := residueSumFinite
  map_add' := residueSumFinite_add
  map_smul' := residueSumFinite_smul

/-- Total residue sum: linear places + infinity.

For the residue theorem, this should equal zero for any f ∈ RatFunc Fq.
Note: This currently only captures linear places. A complete treatment
would include residues at higher-degree irreducible places.
-/
def residueSumTotal [Fintype Fq] (f : RatFunc Fq) : Fq :=
  residueSumFinite f + residueAtInfty f

/-- The total residue sum is linear (mod the residue theorem).

Once we prove residue_sum_eq_zero, this function should always return 0.
-/
theorem residueSumTotal_add [Fintype Fq] (f g : RatFunc Fq) :
    residueSumTotal (f + g) = residueSumTotal f + residueSumTotal g := by
  simp only [residueSumTotal, residueSumFinite_add, residueAtInfty_add]
  ring

/-- Key lemma: for a global element f ∈ RatFunc Fq viewed as a diagonal adele,
    the total residue sum is zero (residue theorem for linear places + ∞).

This is a partial residue theorem covering only linear places.
For the full theorem, we'd need to include higher-degree irreducibles.

Proof uses: each f has at most finitely many poles, and the pole
contributions from finite places cancel with infinity.
-/
theorem residueSumTotal_eq_zero_simple [Fintype Fq] (c : Fq) (α : Fq) :
    residueSumTotal (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) = 0 := by
  simp only [residueSumTotal]
  -- Use residue_sum_simple_pole: res_α + res_∞ = 0
  -- Plus: res_β = 0 for β ≠ α (from residueAtLinear_inv_X_sub_ne)
  -- residueSumFinite = ∑_β res_β = res_α + ∑_{β ≠ α} res_β = c + 0 = c
  have h_finite : residueSumFinite (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) = c := by
    simp only [residueSumFinite]
    -- Split sum into α and the rest
    rw [← Finset.insert_erase (Finset.mem_univ α)]
    rw [Finset.sum_insert (Finset.not_mem_erase α Finset.univ)]
    -- res_α = c
    have h1 : residueAt α (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) = c :=
      residueAt_eq_residueAtLinear_simple α c
    rw [h1]
    -- Sum over β ≠ α is zero
    have h2 : ∑ β ∈ Finset.univ.erase α,
              residueAt β (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) = 0 := by
      apply Finset.sum_eq_zero
      intro β hβ
      have hne : α ≠ β := by
        rw [Finset.mem_erase] at hβ
        exact hβ.1.symm
      -- Use the new lemma residueAt_inv_X_sub_ne
      exact residueAt_inv_X_sub_ne α β c hne
    rw [h2, add_zero]
  -- res_∞ = -c
  have h_infty : residueAtInfty (c • (RatFunc.X - RatFunc.C α)⁻¹ : RatFunc Fq) = -c :=
    residueAtInfty_smul_inv_X_sub α c
  rw [h_finite, h_infty]
  ring

/-- The total residue sum distributes over finite sums. -/
theorem residueSumTotal_sum [Fintype Fq] {ι : Type*} (s : Finset ι) (f : ι → RatFunc Fq) :
    residueSumTotal (∑ i ∈ s, f i) = ∑ i ∈ s, residueSumTotal (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    -- residueSumTotal 0 = 0
    simp only [residueSumTotal, residueSumFinite]
    rw [Finset.sum_eq_zero (fun α _ => residueAt_zero' (Fq := Fq) α)]
    simp [residueAtInfty_zero]
  | insert a s' ha ih =>
    simp only [Finset.sum_insert ha]
    rw [residueSumTotal_add, ih]

/-- The total residue of a sum of simple poles is zero.

This extends `residueSumTotal_eq_zero_simple` to finite sums: if each term
c_i • (X - α_i)⁻¹ has zero total residue, so does their sum by linearity.
-/
theorem residueSumTotal_eq_zero_sum_simple [Fintype Fq] {ι : Type*} (s : Finset ι)
    (coeffs : ι → Fq) (poles : ι → Fq) :
    residueSumTotal (∑ i ∈ s, coeffs i • (RatFunc.X - RatFunc.C (poles i))⁻¹ : RatFunc Fq) = 0 := by
  rw [residueSumTotal_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact residueSumTotal_eq_zero_simple (coeffs i) (poles i)

/-- The total residue of a polynomial is zero.

Polynomials have no poles at linear places (residueAtX_polynomial),
and the residue at infinity is zero for deg(rem) + 1 ≠ deg(denom).
For a polynomial p viewed as p/1, rem = p % 1 = 0, so deg(rem) = 0
and deg(denom) = deg(1) = 0. Thus 0 + 1 ≠ 0 and residue is 0.
-/
theorem residueSumTotal_polynomial [Fintype Fq] (p : Polynomial Fq) :
    residueSumTotal (algebraMap (Polynomial Fq) (RatFunc Fq) p) = 0 := by
  simp only [residueSumTotal, residueSumFinite]
  -- All finite residues are zero: residueAt α (polynomial) = 0
  -- Proof: translateBy α of a polynomial is still a polynomial, then residueAtX_polynomial
  have h_finite : ∑ α : Fq, residueAt α (algebraMap (Polynomial Fq) (RatFunc Fq) p) = 0 := by
    apply Finset.sum_eq_zero
    intro α _
    exact residueAt_polynomial α p
  rw [h_finite, residueAtInfty_polynomial, add_zero]

/-! ## Residue Theorem via Partial Fractions

For rational functions whose denominator splits into distinct linear factors,
we can prove the residue theorem using partial fractions decomposition.

The key theorem from Mathlib is `div_eq_quo_add_sum_rem_div`:
If f, g₁, ..., gₙ ∈ R[X] and the gᵢ are monic and pairwise coprime, then
f / (g₁ ⋯ gₙ) = q + r₁/g₁ + ... + rₙ/gₙ where deg(rᵢ) < deg(gᵢ).

For linear factors (X - αᵢ), deg(rᵢ) < 1 means rᵢ is a constant.
-/

/-- Coprimality of distinct linear factors: if α ≠ β, then (X - α) and (X - β) are coprime. -/
lemma isCoprime_X_sub_of_ne (α β : Fq) (h : α ≠ β) :
    IsCoprime (Polynomial.X - Polynomial.C α) (Polynomial.X - Polynomial.C β) :=
  Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit

/-- For a constant polynomial c (viewed as degree < 1), c/(X - α) = c • (X - α)⁻¹. -/
lemma const_div_X_sub_eq_smul (c α : Fq) :
    (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c)) /
    (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α)) =
    c • (RatFunc.X - RatFunc.C α)⁻¹ := by
  rw [div_eq_mul_inv, Algebra.smul_def, RatFunc.algebraMap_eq_C]
  congr 1
  simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]

/-- A polynomial of degree < 1 is a constant. -/
lemma polynomial_degree_lt_one_eq_C (p : Polynomial Fq) (h : p.degree < 1) :
    ∃ c : Fq, p = Polynomial.C c := by
  have hle : p.degree ≤ 0 := by
    by_cases hp : p = 0
    · simp only [hp, Polynomial.degree_zero, bot_le]
    · have hne : p.degree ≠ ⊥ := Polynomial.degree_ne_bot.mpr hp
      obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hne
      rw [← hn] at h ⊢
      have h' : n < 1 := by simpa using h
      have h'' : n = 0 := Nat.lt_one_iff.mp h'
      simp [h'']
  exact ⟨p.coeff 0, Polynomial.eq_C_of_degree_le_zero hle⟩

/-- The residue theorem for simple linear poles: version with two poles.

If a rational function has poles only at α and β (both simple, α ≠ β),
then its total residue is zero.

Proof approach:
1. Use partial fractions (div_eq_quo_add_rem_div_add_rem_div) to decompose:
   f/((X-α)(X-β)) = q + c₁/(X-α) + c₂/(X-β)
2. Apply residueSumTotal_polynomial to q (contributes 0)
3. Apply residueSumTotal_eq_zero_simple to each simple pole term (contributes 0)
-/
theorem residueSumTotal_two_poles [Fintype Fq] (f : Polynomial Fq) (α β : Fq) (hne : α ≠ β) :
    residueSumTotal ((algebraMap _ (RatFunc Fq) f) /
                     ((RatFunc.X - RatFunc.C α) * (RatFunc.X - RatFunc.C β))) = 0 := by
  -- Apply partial fractions: f/((X-α)(X-β)) = q + r₁/(X-α) + r₂/(X-β)
  have hcop : IsCoprime (Polynomial.X - Polynomial.C α) (Polynomial.X - Polynomial.C β) :=
    isCoprime_X_sub_of_ne α β hne
  have hmonic1 : (Polynomial.X - Polynomial.C α).Monic := Polynomial.monic_X_sub_C α
  have hmonic2 : (Polynomial.X - Polynomial.C β).Monic := Polynomial.monic_X_sub_C β
  obtain ⟨q, r₁, r₂, hdeg1, hdeg2, heq⟩ :=
    div_eq_quo_add_rem_div_add_rem_div Fq (RatFunc Fq) f hmonic1 hmonic2 hcop
  -- r₁ and r₂ are constants since deg < 1
  have hdeg_Xα : (Polynomial.X - Polynomial.C α).degree = 1 := Polynomial.degree_X_sub_C α
  have hdeg_Xβ : (Polynomial.X - Polynomial.C β).degree = 1 := Polynomial.degree_X_sub_C β
  rw [hdeg_Xα] at hdeg1
  rw [hdeg_Xβ] at hdeg2
  obtain ⟨c₁, hc₁⟩ := polynomial_degree_lt_one_eq_C r₁ hdeg1
  obtain ⟨c₂, hc₂⟩ := polynomial_degree_lt_one_eq_C r₂ hdeg2
  -- Substitute constants into heq
  rw [hc₁, hc₂] at heq
  -- Convert const_div_X_sub to smul form
  have h_c₁_div : (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c₁)) /
                  (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α)) =
                  c₁ • (RatFunc.X - RatFunc.C α)⁻¹ := const_div_X_sub_eq_smul c₁ α
  have h_c₂_div : (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c₂)) /
                  (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C β)) =
                  c₂ • (RatFunc.X - RatFunc.C β)⁻¹ := const_div_X_sub_eq_smul c₂ β
  rw [h_c₁_div, h_c₂_div] at heq
  -- heq: ↑f / (↑(X-α) * ↑(X-β)) = ↑q + c₁ • (RatFunc.X - RatFunc.C α)⁻¹ + c₂ • (RatFunc.X - RatFunc.C β)⁻¹
  -- Goal: residueSumTotal (algebraMap f / ((RatFunc.X - RatFunc.C α) * (RatFunc.X - RatFunc.C β))) = 0
  -- Align goal with heq's LHS: RatFunc.X - RatFunc.C α = ↑(X - C α)
  have hXα : RatFunc.X - RatFunc.C α =
             (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C α)) := by
    simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]
  have hXβ : RatFunc.X - RatFunc.C β =
             (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.X - Polynomial.C β)) := by
    simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]
  rw [hXα, hXβ]
  -- Now goal matches heq's LHS exactly
  rw [heq]
  -- Now goal is: residueSumTotal (↑q + c₁ • _ + c₂ • _) = 0
  rw [residueSumTotal_add, residueSumTotal_add]
  rw [residueSumTotal_polynomial q]
  rw [residueSumTotal_eq_zero_simple c₁ α]
  rw [residueSumTotal_eq_zero_simple c₂ β]
  ring

/-- Pairwise coprimality of distinct linear factors.

If all elements of a finset are distinct (injective on indices),
then the linear factors (X - αᵢ) are pairwise coprime.
-/
lemma pairwise_coprime_X_sub_of_injective {ι : Type*} (poles : ι → Fq) (s : Finset ι)
    (hinj : Set.InjOn poles s) :
    Set.Pairwise (s : Set ι) fun i j => IsCoprime
      (Polynomial.X - Polynomial.C (poles i))
      (Polynomial.X - Polynomial.C (poles j)) := by
  intro i hi j hj hij
  apply isCoprime_X_sub_of_ne
  intro heq
  exact hij (hinj hi hj heq)

/-- The residue theorem for n distinct linear poles (direct version with Finset Fq).

For a finite set of distinct poles (elements of Fq), the total residue is zero.
This is the most usable form for the Serre duality application.
-/
theorem residueSumTotal_n_poles_finset [Fintype Fq] (f : Polynomial Fq) (poles : Finset Fq) :
    residueSumTotal ((algebraMap _ (RatFunc Fq) f) /
                     (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) = 0 := by
  -- Induct on poles, generalizing f so the IH works for r₂
  induction poles using Finset.induction_on generalizing f with
  | empty =>
    -- Empty product is 1, so f/1 = f which is a polynomial
    simp only [Finset.prod_empty]
    rw [div_one]
    exact residueSumTotal_polynomial f
  | insert α s hα ih =>
    -- f/((X-α) * ∏ s) = ? We need to show residue is 0
    -- Strategy: use two-pole decomposition iteratively
    rw [Finset.prod_insert hα]
    -- We have f / ((X-α) * ∏_{β∈s} (X-β))
    -- Use partial fractions: f / (g₁ * g₂) = q + r₁/g₁ + r₂/g₂
    set g₁ := Polynomial.X - Polynomial.C α with hg₁_def
    set g₂ := ∏ β ∈ s, (Polynomial.X - Polynomial.C β) with hg₂_def
    by_cases hs : s = ∅
    · -- s is empty, so g₂ = 1 and this reduces to f/(X-α)
      subst hs
      simp only [Finset.prod_empty, mul_one] at hg₂_def ⊢
      -- f / (X-α) = q + r/(X-α) where deg r < 1
      have hmonic1 : g₁.Monic := Polynomial.monic_X_sub_C α
      have hmonic2 : (1 : Polynomial Fq).Monic := Polynomial.monic_one
      have hcop : IsCoprime g₁ (1 : Polynomial Fq) := isCoprime_one_right
      obtain ⟨q, r₁, r₂, hdeg1, _, heq⟩ :=
        div_eq_quo_add_rem_div_add_rem_div Fq (RatFunc Fq) f hmonic1 hmonic2 hcop
      have hdeg_g1 : g₁.degree = 1 := Polynomial.degree_X_sub_C α
      rw [hdeg_g1] at hdeg1
      obtain ⟨c, hc⟩ := polynomial_degree_lt_one_eq_C r₁ hdeg1
      rw [hc] at heq
      -- heq has form: ↑f / (↑g₁ * 1) = ↑q + ↑(C c) / ↑g₁ + ↑r₂ / 1
      have h_c_div : (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c)) /
                      (algebraMap (Polynomial Fq) (RatFunc Fq) g₁) =
                      c • (RatFunc.X - RatFunc.C α)⁻¹ := by
        rw [hg₁_def]; exact const_div_X_sub_eq_smul c α
      simp only [mul_one, map_one, div_one] at heq
      rw [h_c_div] at heq
      have hXα : RatFunc.X - RatFunc.C α =
                 (algebraMap (Polynomial Fq) (RatFunc Fq) g₁) := by
        rw [hg₁_def]; simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]
      rw [hXα, heq, residueSumTotal_add, residueSumTotal_add]
      rw [residueSumTotal_polynomial q]
      rw [residueSumTotal_eq_zero_simple c α]
      rw [residueSumTotal_polynomial r₂]
      ring
    · -- s is nonempty
      -- g₂ is a product of monic coprime linear factors
      have hmonic1 : g₁.Monic := Polynomial.monic_X_sub_C α
      have hmonic2 : g₂.Monic := by
        rw [hg₂_def]
        apply Polynomial.monic_prod_of_monic
        intro β _
        exact Polynomial.monic_X_sub_C β
      -- g₁ and g₂ are coprime because α ∉ s
      have hcop : IsCoprime g₁ g₂ := by
        rw [hg₁_def, hg₂_def]
        apply IsCoprime.prod_right
        intro β hβ
        apply isCoprime_X_sub_of_ne
        intro heq
        rw [heq] at hα
        exact hα hβ
      obtain ⟨q, r₁, r₂, hdeg1, _, heq⟩ :=
        div_eq_quo_add_rem_div_add_rem_div Fq (RatFunc Fq) f hmonic1 hmonic2 hcop
      -- r₁ is constant since deg r₁ < deg g₁ = 1
      have hdeg_g1 : g₁.degree = 1 := Polynomial.degree_X_sub_C α
      rw [hdeg_g1] at hdeg1
      obtain ⟨c, hc⟩ := polynomial_degree_lt_one_eq_C r₁ hdeg1
      rw [hc] at heq
      have h_c_div : (algebraMap (Polynomial Fq) (RatFunc Fq) (Polynomial.C c)) /
                      (algebraMap (Polynomial Fq) (RatFunc Fq) g₁) =
                      c • (RatFunc.X - RatFunc.C α)⁻¹ := by
        rw [hg₁_def]; exact const_div_X_sub_eq_smul c α
      rw [h_c_div] at heq
      -- Align goal with heq
      have hXα : RatFunc.X - RatFunc.C α =
                 (algebraMap (Polynomial Fq) (RatFunc Fq) g₁) := by
        rw [hg₁_def]; simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]
      have hprod_eq : ∏ β ∈ s, (RatFunc.X - RatFunc.C β) =
                      (algebraMap (Polynomial Fq) (RatFunc Fq) g₂) := by
        rw [hg₂_def, map_prod]
        apply Finset.prod_congr rfl
        intro β _
        simp only [RatFunc.X, ← RatFunc.algebraMap_C, ← map_sub]
      rw [hXα, hprod_eq, heq]
      rw [residueSumTotal_add, residueSumTotal_add]
      rw [residueSumTotal_polynomial q]
      rw [residueSumTotal_eq_zero_simple c α]
      -- The remaining term is r₂/g₂ where g₂ = ∏ β∈s (X-β)
      -- Apply IH with r₂ (now works because we generalized over f)
      -- The coercion ↑ and algebraMap are the same for polynomials
      simp only [zero_add]
      convert (ih r₂) using 1
      rw [hprod_eq]

/-- Corollary: Any rational function whose denominator splits into distinct linear factors
has zero total residue. -/
theorem residueSumTotal_splits [Fintype Fq] (f : RatFunc Fq)
    (h : ∃ (p : Polynomial Fq) (poles : Finset Fq),
         f = (algebraMap _ (RatFunc Fq) p) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residueSumTotal f = 0 := by
  obtain ⟨p, poles, hf⟩ := h
  rw [hf]
  exact residueSumTotal_n_poles_finset p poles

/-! ## Multiplicative Pairing via Residue Sum

The Serre pairing `⟨[a], f⟩ = ∑_v res_v(a_v · f)` for adele class [a] and f ∈ L(K-D)
requires computing residue sums of products.

For the diagonal embedding of K into adeles, this reduces to:
  ⟨diag(g), f⟩ = residueSumTotal(g · f)

By the residue theorem, this is 0 for any g, f ∈ K with split denominators.
This establishes well-definedness on the quotient H¹(D) = Adeles / (K + A_K(D)).
-/

/-- The residue sum respects scalar multiplication (full version).

This extends residueSumTotal_add to show that residueSumTotal is Fq-linear.
-/
theorem residueSumTotal_smul [Fintype Fq] (c : Fq) (f : RatFunc Fq) :
    residueSumTotal (c • f) = c * residueSumTotal f := by
  simp only [residueSumTotal]
  conv_lhs => rw [show residueSumFinite (c • f) = c * residueSumFinite f from residueSumFinite_smul c f]
  rw [residueAtInfty_smul, mul_add]

/-- The total residue sum as a linear map. -/
def residueSumTotal_linearMap [Fintype Fq] : RatFunc Fq →ₗ[Fq] Fq where
  toFun := residueSumTotal
  map_add' := residueSumTotal_add
  map_smul' := residueSumTotal_smul

/-- For products that split into distinct linear poles, the residue theorem applies.

If `g * f = p / ∏_{α ∈ poles} (X - α)` for some polynomial p and finite set of poles,
then `residueSumTotal(g * f) = 0`.

This is the key well-definedness lemma for the Serre pairing on diagonal K.
-/
theorem residueSumTotal_mul_splits [Fintype Fq] (g f : RatFunc Fq)
    (h : ∃ (p : Polynomial Fq) (poles : Finset Fq),
         g * f = (algebraMap _ (RatFunc Fq) p) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residueSumTotal (g * f) = 0 :=
  residueSumTotal_splits (g * f) h

/-- The pairing on K × K via residue sum of products.

For g, f ∈ RatFunc Fq, define ⟨g, f⟩ := residueSumTotal(g * f).

This pairing is bilinear and vanishes whenever g * f has split denominator
(which includes all products of rational functions with distinct linear poles).
-/
def residuePairing [Fintype Fq] (g f : RatFunc Fq) : Fq :=
  residueSumTotal (g * f)

/-- The residue pairing is additive in the first argument. -/
theorem residuePairing_add_left [Fintype Fq] (g₁ g₂ f : RatFunc Fq) :
    residuePairing (g₁ + g₂) f = residuePairing g₁ f + residuePairing g₂ f := by
  simp only [residuePairing, add_mul, residueSumTotal_add]

/-- The residue pairing is additive in the second argument. -/
theorem residuePairing_add_right [Fintype Fq] (g f₁ f₂ : RatFunc Fq) :
    residuePairing g (f₁ + f₂) = residuePairing g f₁ + residuePairing g f₂ := by
  simp only [residuePairing, mul_add, residueSumTotal_add]

/-- The residue pairing respects scalar multiplication on the left. -/
theorem residuePairing_smul_left [Fintype Fq] (c : Fq) (g f : RatFunc Fq) :
    residuePairing (c • g) f = c * residuePairing g f := by
  simp only [residuePairing]
  rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, mul_assoc]
  conv_lhs => rw [show RatFunc.C c * (g * f) = c • (g * f) by
    rw [Algebra.smul_def, RatFunc.algebraMap_eq_C]]
  exact residueSumTotal_smul c (g * f)

/-- The residue pairing respects scalar multiplication on the right. -/
theorem residuePairing_smul_right [Fintype Fq] (c : Fq) (g f : RatFunc Fq) :
    residuePairing g (c • f) = c * residuePairing g f := by
  simp only [residuePairing]
  rw [Algebra.smul_def, RatFunc.algebraMap_eq_C, ← mul_assoc, mul_comm g (RatFunc.C c), mul_assoc]
  conv_lhs => rw [show RatFunc.C c * (g * f) = c • (g * f) by
    rw [Algebra.smul_def, RatFunc.algebraMap_eq_C]]
  exact residueSumTotal_smul c (g * f)

/-- The residue pairing as a bilinear map RatFunc Fq → RatFunc Fq → Fq.

This captures the multiplication structure needed for the Serre pairing.
-/
def residuePairing_bilinear [Fintype Fq] : RatFunc Fq →ₗ[Fq] RatFunc Fq →ₗ[Fq] Fq where
  toFun := fun g =>
    { toFun := fun f => residuePairing g f
      map_add' := fun f₁ f₂ => residuePairing_add_right g f₁ f₂
      map_smul' := fun c f => residuePairing_smul_right c g f }
  map_add' := fun g₁ g₂ => by
    ext f
    exact residuePairing_add_left g₁ g₂ f
  map_smul' := fun c g => by
    ext f
    exact residuePairing_smul_left c g f

/-- Key property: the residue pairing vanishes for products with split denominators.

This is the residue theorem restated for the pairing.
-/
theorem residuePairing_eq_zero_of_splits [Fintype Fq] (g f : RatFunc Fq)
    (h : ∃ (p : Polynomial Fq) (poles : Finset Fq),
         g * f = (algebraMap _ (RatFunc Fq) p) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residuePairing g f = 0 :=
  residueSumTotal_mul_splits g f h

/-! ## Diagonal Well-Definedness

For the Serre pairing to be well-defined on H¹(D) = Adeles / (K + A_K(D)),
we need to show that the pairing vanishes on:
1. Global elements (diagonal K) - handled by residue theorem
2. Bounded adeles A_K(D) - requires valuation analysis

This section establishes (1) for the case of split denominators.
-/

/-- The residue pairing of any element with a polynomial is zero.

Polynomials have no poles, so multiplying by them doesn't introduce new poles.
The product g * (polynomial p) can only have poles from g.
If g's poles are linear and finite, the residue theorem applies.
-/
theorem residuePairing_polynomial_right [Fintype Fq] (g : RatFunc Fq) (p : Polynomial Fq)
    (hg : ∃ (q : Polynomial Fq) (poles : Finset Fq),
          g = (algebraMap _ (RatFunc Fq) q) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residuePairing g (algebraMap _ (RatFunc Fq) p) = 0 := by
  obtain ⟨q, poles, hg_eq⟩ := hg
  apply residuePairing_eq_zero_of_splits
  use q * p, poles
  rw [hg_eq, div_mul_eq_mul_div, map_mul]

/-- The residue pairing of a polynomial with any element is zero.

Similar to the above, but for polynomial on the left.
-/
theorem residuePairing_polynomial_left [Fintype Fq] (p : Polynomial Fq) (f : RatFunc Fq)
    (hf : ∃ (q : Polynomial Fq) (poles : Finset Fq),
          f = (algebraMap _ (RatFunc Fq) q) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residuePairing (algebraMap _ (RatFunc Fq) p) f = 0 := by
  obtain ⟨q, poles, hf_eq⟩ := hf
  apply residuePairing_eq_zero_of_splits
  use p * q, poles
  rw [hf_eq, mul_div_assoc', map_mul]

end ConcreteRatFuncPairing

/-! ## Diagonal Embedding and Pairing

For the serrePairing to be well-defined on H¹(D) = FiniteAdeleRing / (K + A_K(D)),
we need to show the pairing vanishes on globalPlusBoundedSubmodule.

This requires:
1. Global elements (K diagonally embedded) → residue theorem gives 0
2. Bounded adeles A_K(D) with f ∈ L(K-D) → pole cancellation gives 0

This section provides the RatFunc Fq specialization that uses residuePairing.
-/

section DiagonalPairing

variable {Fq : Type*} [Field Fq] [Fintype Fq]

open RiemannRochV2.Residue AdelicH1v2

/-- The diagonal embedding K → FiniteAdeleRing for RatFunc case.
This is just FiniteAdeleRing.algebraMap specialized. -/
def diagonalEmbedding : RatFunc Fq →+* FiniteAdeleRing (Polynomial Fq) (RatFunc Fq) :=
  FiniteAdeleRing.algebraMap (Polynomial Fq) (RatFunc Fq)

/-- The pairing on diagonal elements: for g ∈ K and f ∈ K,
the "diagonal pairing" is residuePairing g f.

This captures the pairing ⟨diag(g), f⟩ = ∑_v res_v(g · f).
-/
def diagonalResiduePairing (g f : RatFunc Fq) : Fq :=
  residuePairing g f

/-- Diagonal pairing is bilinear (inherited from residuePairing_bilinear). -/
def diagonalResiduePairing_bilinear :
    RatFunc Fq →ₗ[Fq] RatFunc Fq →ₗ[Fq] Fq :=
  residuePairing_bilinear

/-- Key lemma: diagonal pairing with split denominators is zero.

If g, f ∈ RatFunc Fq and g * f has split denominator (distinct linear poles),
then the diagonal pairing is zero by the residue theorem.
-/
theorem diagonalResiduePairing_eq_zero_of_splits (g f : RatFunc Fq)
    (h : ∃ (p : Polynomial Fq) (poles : Finset Fq),
         g * f = (algebraMap _ (RatFunc Fq) p) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    diagonalResiduePairing g f = 0 :=
  residuePairing_eq_zero_of_splits g f h

/-- For the diagonal embedding, the pairing factors through residuePairing.

This is the key observation: ⟨diag(g), f⟩ = residuePairing g f.
Combined with the residue theorem, this shows the pairing vanishes
on the K part of globalPlusBoundedSubmodule.
-/
theorem diagonal_pairing_eq_residue (g f : RatFunc Fq) :
    diagonalResiduePairing g f = residuePairing g f := rfl

end DiagonalPairing

/-! ## Specialization to RatFunc Fq

For the concrete case K = RatFunc Fq, R = Polynomial Fq, k = Fq,
we can instantiate the serrePairing using our residue infrastructure.

The construction:
1. Define the pairing on representatives: FiniteAdeleRing × RRSpace_proj → Fq
2. Show it descends to quotient H¹(D) (vanishes on K + A_K(D))
3. Show non-degeneracy (perfect pairing)

For now, we set up the specialized types and leave the full construction
for future cycles when the residue-on-completions infrastructure is ready.
-/

section RatFuncSpecialization

variable {Fq : Type*} [Field Fq] [Fintype Fq]
variable (canonical : DivisorV2 (Polynomial Fq))

open AdelicH1v2

/-- Specialized H¹(D) for RatFunc case. -/
abbrev H1_ratfunc (D : DivisorV2 (Polynomial Fq)) : Type _ :=
  SpaceModule Fq (Polynomial Fq) (RatFunc Fq) D

/-- Specialized L(K-D) for RatFunc case. -/
abbrev LKD_ratfunc (D : DivisorV2 (Polynomial Fq)) : Type _ :=
  RRSpace_proj Fq (Polynomial Fq) (RatFunc Fq) (canonical - D)

/-- The key property for well-definedness: diagonal K maps to zero under the pairing.

For g ∈ RatFunc Fq and f ∈ L(K-D), if g * f has split denominator,
then the pairing ⟨diag(g), f⟩ = 0 by the residue theorem.

This handles the K-part of the well-definedness condition for serrePairing.
-/
theorem diagonal_maps_to_zero (g : RatFunc Fq) (f : RatFunc Fq)
    (h : ∃ (p : Polynomial Fq) (poles : Finset Fq),
         g * f = (algebraMap _ (RatFunc Fq) p) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residueSumTotal (g * f) = 0 :=
  residueSumTotal_splits (g * f) h

/-- For polynomial g and any f, the diagonal pairing vanishes.

Polynomials have no poles at finite places, so g*f only has poles from f.
-/
theorem polynomial_diagonal_pairing_zero (p : Polynomial Fq) (f : RatFunc Fq)
    (hf : ∃ (q : Polynomial Fq) (poles : Finset Fq),
          f = (algebraMap _ (RatFunc Fq) q) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    diagonalResiduePairing (algebraMap _ (RatFunc Fq) p) f = 0 :=
  residuePairing_polynomial_left p f hf

/-- The diagonal embedding of K lands in globalSubmodule.

For any g ∈ RatFunc Fq, diagonalEmbedding g ∈ globalSubmodule.
-/
theorem diagonalEmbedding_mem_globalSubmodule (g : RatFunc Fq) :
    diagonalEmbedding g ∈
      globalSubmodule Fq (Polynomial Fq) (RatFunc Fq) := by
  use g
  rfl

/-- Key well-definedness lemma: diagonal K pairs to zero with L(K-D).

For g ∈ K (RatFunc Fq) embedded diagonally into FiniteAdeleRing,
and f ∈ L(K-D) (assumed to have split denominator),
the residue pairing is zero by the residue theorem.

This is the main step for showing serrePairing is well-defined on H¹(D).
-/
theorem diagonal_globalSubmodule_pairing_zero (g : RatFunc Fq)
    (f : RatFunc Fq)
    (hgf_splits : ∃ (p : Polynomial Fq) (poles : Finset Fq),
                  g * f = (algebraMap _ (RatFunc Fq) p) / (∏ α ∈ poles, (RatFunc.X - RatFunc.C α))) :
    residuePairing g f = 0 :=
  residuePairing_eq_zero_of_splits g f hgf_splits

end RatFuncSpecialization

/-! ## Pole Cancellation for Bounded Adeles

For the bounded adele part of serrePairing well-definedness, we need to show that
if `a ∈ A_K(D)` and `f ∈ L(K-D)`, then the "pairing" of `a` with `f` is zero.

The key mathematical insight is **pole cancellation**:
- If `a ∈ A_K(D)`, then `ord_v(a_v) ≥ -D(v)` for all finite places v
- If `f ∈ L(K-D)`, then `ord_v(f) ≥ D(v) - K(v)` for all finite places v
- Product: `ord_v(a_v · f) ≥ -D(v) + D(v) - K(v) = -K(v)`

For the residue at v to be zero, we need `ord_v(a_v · f) ≥ 0`.
This holds when `K(v) ≤ 0`, i.e., the canonical divisor has no poles at v.

For RatFunc Fq (projective line P¹ over Fq):
- The canonical divisor K = -2·[∞] has degree -2
- At all **finite** places v, K(v) = 0 (no contribution)
- Therefore `ord_v(a_v · f) ≥ 0` for all finite v
- Thus `res_v(a_v · f) = 0` for all finite v
- The sum over finite places (residueSumFinite) is zero!

This section formalizes the pole cancellation argument for the bounded part.
-/

section PoleCancellation

variable {Fq : Type*} [Field Fq] [Fintype Fq]
variable (canonical : DivisorV2 (Polynomial Fq))

open RiemannRochV2.Residue AdelicH1v2

/-- For P¹ over Fq, the canonical divisor has K(v) = 0 at all finite places.

This is a key property: the canonical divisor -2·[∞] has no contribution
at any finite place (X - α) or higher-degree irreducible.

Note: This is specific to genus 0 curves (P¹). For higher genus curves,
the canonical divisor can have non-trivial finite part.
-/
def canonicalZeroAtFinite (K : DivisorV2 (Polynomial Fq)) : Prop :=
  ∀ v : HeightOneSpectrum (Polynomial Fq), K v = 0

/-- If canonical(v) = 0 for all finite v, then elements of bounded × L(K-D)
have controlled valuation at all finite places.

For a ∈ A_K(D) (meaning ord_v(a) ≥ -D(v)) and f ∈ L(K-D) (meaning ord_v(f) ≥ D(v) - K(v)),
the product satisfies:
  ord_v(a · f) ≥ -D(v) + D(v) - K(v) = -K(v) = 0

when K(v) = 0. This means a · f has no poles at finite places.
-/
theorem bounded_times_LKD_valuation_bound
    (D : DivisorV2 (Polynomial Fq))
    (g f : RatFunc Fq)
    (hg : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) g ≤ WithZero.exp (D v))
    (hf : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) f ≤ WithZero.exp ((canonical - D) v))
    (v : HeightOneSpectrum (Polynomial Fq)) :
    v.valuation (RatFunc Fq) (g * f) ≤ WithZero.exp (canonical v) := by
  -- v(g * f) = v(g) * v(f) ≤ exp(D v) * exp((K-D) v)
  --          = exp(D v + (K-D) v) = exp(K v)
  rw [Valuation.map_mul]
  have h1 := hg v
  have h2 := hf v
  have heq : D v + (canonical - D) v = canonical v := by
    simp only [Finsupp.sub_apply]
    ring
  calc v.valuation (RatFunc Fq) g * v.valuation (RatFunc Fq) f
      ≤ WithZero.exp (D v) * WithZero.exp ((canonical - D) v) := by
        apply mul_le_mul' h1 h2
    _ = WithZero.exp (D v + (canonical - D) v) := by rw [← WithZero.exp_add]
    _ = WithZero.exp (canonical v) := by rw [heq]

/-- Corollary: when canonical(v) = 0 for all finite v, the product has no poles.

This is the key lemma for residue vanishing: if v(g*f) ≤ 1, then g*f has no pole
at v, so its residue at v is zero.
-/
theorem bounded_times_LKD_no_pole
    (D : DivisorV2 (Polynomial Fq))
    (hK : canonicalZeroAtFinite canonical)
    (g f : RatFunc Fq)
    (hg : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) g ≤ WithZero.exp (D v))
    (hf : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) f ≤ WithZero.exp ((canonical - D) v))
    (v : HeightOneSpectrum (Polynomial Fq)) :
    v.valuation (RatFunc Fq) (g * f) ≤ 1 := by
  have h := bounded_times_LKD_valuation_bound canonical D g f hg hf v
  -- K(v) = 0 by hK, so exp(K(v)) = exp(0) = 1
  rw [hK v] at h
  simp only [WithZero.exp_zero] at h
  exact h

/-- The HeightOneSpectrum corresponding to the place (X - α).

For a polynomial ring Fq[X], the ideal (X - α) is prime and nonzero,
so it defines a height-one prime.
-/
def linearPlace (α : Fq) : HeightOneSpectrum (Polynomial Fq) where
  asIdeal := Ideal.span {Polynomial.X - Polynomial.C α}
  isPrime := Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero α) |>.mpr
              (Polynomial.irreducible_X_sub_C α).prime
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Polynomial.X_sub_C_ne_zero α

/-- The translation RingEquiv on polynomials: p ↦ p.comp(X + C α).

This is a ring automorphism of Fq[X] that shifts the variable by α.
Its inverse is p ↦ p.comp(X - C α).
-/
def translatePolyEquiv (α : Fq) : Polynomial Fq ≃+* Polynomial Fq where
  toFun := fun p => p.comp (Polynomial.X + Polynomial.C α)
  invFun := fun p => p.comp (Polynomial.X - Polynomial.C α)
  left_inv := fun p => by
    simp only [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.sub_comp,
               Polynomial.X_comp, Polynomial.C_comp, add_sub_cancel, Polynomial.comp_X]
  right_inv := fun p => by
    simp only [Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.add_comp,
               Polynomial.X_comp, Polynomial.C_comp, sub_add_cancel, Polynomial.comp_X]
  map_mul' := fun p q => Polynomial.mul_comp p q _
  map_add' := fun p q => Polynomial.add_comp p q _

/-- Translation sends X - C α to X. -/
lemma translatePolyEquiv_X_sub_C (α : Fq) :
    translatePolyEquiv α (Polynomial.X - Polynomial.C α) = Polynomial.X := by
  simp [translatePolyEquiv, Polynomial.sub_comp, Polynomial.add_comp]

/-- Translation sends the ideal span{X - C α} to span{X}. -/
lemma translatePolyEquiv_ideal_map (α : Fq) :
    Ideal.map (translatePolyEquiv α) (Ideal.span {Polynomial.X - Polynomial.C α}) =
    Ideal.span {Polynomial.X} := by
  rw [Ideal.map_span, Set.image_singleton, translatePolyEquiv_X_sub_C]

/-- translatePolyEquiv preserves non-zero-divisors. -/
lemma translatePolyEquiv_mem_nonZeroDivisors (α : Fq) :
    nonZeroDivisors (Polynomial Fq) ≤
    (nonZeroDivisors (Polynomial Fq)).comap (translatePolyEquiv α).toRingHom := by
  intro p hp
  simp only [Submonoid.mem_comap, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  -- p is a non-zero-divisor, so p ≠ 0
  have hp_ne : p ≠ 0 := nonZeroDivisors.ne_zero hp
  -- translatePolyEquiv α is an isomorphism, so (translatePolyEquiv α p) ≠ 0
  have h_ne : translatePolyEquiv α p ≠ 0 := by
    simp only [ne_eq, map_eq_zero_iff (translatePolyEquiv α) (translatePolyEquiv α).injective]
    exact hp_ne
  -- Non-zero elements are non-zero-divisors in a domain
  exact mem_nonZeroDivisors_of_ne_zero h_ne

/-- The lifted translation RingHom on RatFunc. -/
def translateRatFuncHom (α : Fq) : RatFunc Fq →+* RatFunc Fq :=
  RatFunc.mapRingHom (translatePolyEquiv α).toRingHom (translatePolyEquiv_mem_nonZeroDivisors α)

/-- translateRatFuncHom agrees with translateBy on all elements.

This shows that the abstract lifting via mapRingHom gives the same result
as the explicit definition via num/denom composition.
-/
lemma translateRatFuncHom_eq_translateBy (α : Fq) (g : RatFunc Fq) :
    translateRatFuncHom α g = translateBy α g := by
  rw [translateRatFuncHom, RatFunc.coe_mapRingHom_eq_coe_map]
  rw [← RatFunc.num_div_denom g]
  simp only [RatFunc.map_apply_div, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  simp only [translatePolyEquiv, RingEquiv.coe_mk, Equiv.coe_fn_mk]
  -- Now both sides are: ↑(num.comp(X+α)) / ↑(denom.comp(X+α))
  -- translateBy is defined as the same thing
  rw [translateBy, RatFunc.num_div_denom]

/-- The key valuation transport lemma:
    The valuation at (X - α) equals the comap of the valuation at X along translation.

    This uses the fact that ring automorphisms transport valuations:
    if φ sends the prime ideal p to q, then v_p = v_q ∘ φ.
-/
lemma linearPlace_valuation_eq_comap (α : Fq) :
    (linearPlace α).valuation (RatFunc Fq) =
    ((Polynomial.idealX Fq).valuation (RatFunc Fq)).comap (translateRatFuncHom α) := by
  -- Both valuations are defined via intValuation extended to localization
  -- The key is that the ideals are related by the automorphism:
  -- span{X - α} maps to span{X} under translatePolyEquiv α
  ext g
  simp only [Valuation.comap_apply]
  -- Need to show: (linearPlace α).valuation g = (idealX).valuation (translateRatFuncHom α g)
  -- The valuation is defined via intValuation counting prime factors
  -- translatePolyEquiv α sends (X - α) to X, so counts are preserved
  sorry -- Key: valuation transport under automorphism that maps the prime ideal

/-- The valuation at linearPlace α equals idealX valuation after translation.

This is the key bridge: translation intertwines the valuations.
-/
theorem linearPlace_valuation_eq_idealX_translated (α : Fq) (g : RatFunc Fq) :
    (linearPlace α).valuation (RatFunc Fq) g =
    (Polynomial.idealX Fq).valuation (RatFunc Fq) (translateBy α g) := by
  rw [linearPlace_valuation_eq_comap, Valuation.comap_apply, translateRatFuncHom_eq_translateBy]

/-- If the valuation at a linear place (X - α) is ≤ 1, then the residue is zero.

Proof strategy:
1. Valuation ≤ 1 at (X - α) means valuation ≤ 1 at X for the translated function
2. By valuation_eq_LaurentSeries_valuation, this equals the Laurent series valuation
3. Valuation ≤ 1 = exp(0) implies all coefficients at degree < 0 are zero
4. In particular, coeff(-1) = 0, which is the residue
-/
theorem residueAt_of_valuation_le_one (α : Fq) (g : RatFunc Fq)
    (hv : (linearPlace α).valuation (RatFunc Fq) g ≤ 1) :
    residueAt α g = 0 := by
  -- Step 1: Translate the valuation condition
  have hv_trans : (Polynomial.idealX Fq).valuation (RatFunc Fq) (translateBy α g) ≤ 1 := by
    rw [← linearPlace_valuation_eq_idealX_translated]
    exact hv
  -- Step 2: Connect to Laurent series valuation
  -- RatFunc.valuation_eq_LaurentSeries_valuation : (Polynomial.idealX).valuation P = Valued.v (P : LS)
  have hv_laurent : Valued.v (translateBy α g : LaurentSeries Fq) ≤ 1 := by
    -- The Laurent series valuation equals the idealX valuation on RatFunc
    have h := RatFunc.valuation_eq_LaurentSeries_valuation (K := Fq) (translateBy α g)
    -- h : (Polynomial.idealX Fq).valuation (RatFunc Fq) (translateBy α g) =
    --     (PowerSeries.idealX Fq).valuation (LaurentSeries Fq) (translateBy α g)
    -- And Valued.v on LaurentSeries is defined as (PowerSeries.idealX).valuation
    rw [LaurentSeries.valuation_def, ← h]
    exact hv_trans
  -- Step 3: Valuation ≤ 1 = exp(0) means all coefficients at degree < 0 are zero
  -- Use valuation_le_iff_coeff_lt_eq_zero with D = 0
  have h_coeff : (translateBy α g : LaurentSeries Fq).coeff (-1) = 0 := by
    apply LaurentSeries.coeff_zero_of_lt_valuation Fq (D := 0)
    · simp only [neg_zero, WithZero.exp_zero]
      exact hv_laurent
    · norm_num
  -- Step 4: residueAt = residueAtX ∘ translateBy = coeff(-1) = 0
  rw [residueAt, residueAtX]
  exact h_coeff

/-- When canonical = 0 at all finite places, bounded adeles paired with L(K-D)
give zero finite residue sum.

This is the key lemma for the bounded part of serrePairing well-definedness.
Combined with the K-part (diagonal_globalSubmodule_pairing_zero), this shows
the pairing vanishes on globalPlusBoundedSubmodule.

Note: This is stated for diagonal elements (g ∈ RatFunc Fq embedded diagonally).
For general finite adeles, the argument is similar but requires local residue infrastructure.
-/
theorem bounded_diagonal_finite_residue_zero
    (D : DivisorV2 (Polynomial Fq))
    (hK : canonicalZeroAtFinite canonical)
    (g f : RatFunc Fq)
    (hg : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) g ≤ WithZero.exp (D v))
    (hf : ∀ v : HeightOneSpectrum (Polynomial Fq),
          v.valuation (RatFunc Fq) f ≤ WithZero.exp ((canonical - D) v)) :
    residueSumFinite (g * f) = 0 := by
  -- By bounded_times_LKD_no_pole, v(g*f) ≤ 1 at all finite v
  -- This means g*f has no poles at any linear place (X - α)
  -- Therefore residueAt α (g*f) = 0 for all α
  -- And residueSumFinite = ∑_α residueAt α = 0
  simp only [residueSumFinite]
  apply Finset.sum_eq_zero
  intro α _
  -- Apply residueAt_of_valuation_le_one with v = linearPlace α
  apply residueAt_of_valuation_le_one
  -- Need: (linearPlace α).valuation (RatFunc Fq) (g * f) ≤ 1
  -- Use bounded_times_LKD_no_pole which gives this bound when canonical = 0 at all finite v
  exact bounded_times_LKD_no_pole canonical D hK g f hg hf (linearPlace α)

end PoleCancellation

/-! ## Strategy for Completing serrePairing

The serrePairing construction requires defining a bilinear map:
  H¹(D) × L(K-D) → k

where H¹(D) = FiniteAdeleRing / (K + A_K(D)).

### Construction via liftQ

To define a linear map on the quotient, we use `Submodule.liftQ`:
1. Define a linear map `rawPairing : FiniteAdeleRing →ₗ[k] (L(K-D) →ₗ[k] k)`
2. Show `globalPlusBoundedSubmodule ≤ ker rawPairing`
3. Apply `Submodule.liftQ` to get `serrePairing : H¹(D) →ₗ[k] (L(K-D) →ₗ[k] k)`

### The rawPairing Definition

For `a ∈ FiniteAdeleRing` and `f ∈ L(K-D)`:
  `rawPairing a f = ∑_v res_v(a_v · f)`

where `res_v : K_v → k` is the local residue at place v.

For the RatFunc Fq case:
- At linear place v = (X - α): res_v = coefficient of (X - α)^{-1}
- At infinity: res_∞ = coefficient as defined in Residue.lean
- The sum is finite because a_v is integral at almost all v

### Key Properties to Prove

1. **K-part vanishes**: For diagonal `g ∈ K`:
   - `rawPairing (diag g) f = residueSumTotal(g * f) = 0` by residue theorem
   - ✅ Established via `diagonal_globalSubmodule_pairing_zero` (for split denominators)

2. **A_K(D)-part vanishes**: For `a ∈ A_K(D)`:
   - By pole cancellation: `a_v · f` has no poles at finite v when K(v) ≤ 0
   - For P¹ (genus 0): K(v) = 0 for all finite v, so all finite residues are 0
   - What remains is the residue at infinity, which needs separate treatment

3. **Residue at infinity for bounded adeles**:
   - For a ∈ A_K(D), what is res_∞(a · f)?
   - This requires understanding the infinity completion
   - For P¹: the infinity place is handled by residueAtInfty

### Current Infrastructure

For RatFunc Fq:
- `residuePairing` works on K × K (diagonal case)
- `residueSumTotal` = residueSumFinite + residueAtInfty
- Residue theorem proved for split denominators

Missing:
- Local residue on completion elements (not just K)
- Connection between HeightOneSpectrum.valuation and residueAt
- Handling of higher-degree irreducible places

### Next Steps

1. Complete the bridge `residueAt_of_valuation_le_one`
2. Define `rawPairing` using local residues (for RatFunc Fq case)
3. Wire the construction via liftQ
4. Handle non-degeneracy proofs
-/

end RiemannRochV2
