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

end ConcreteRatFuncPairing

end RiemannRochV2
