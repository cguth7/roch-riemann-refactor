import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.FieldTheory.Finiteness
import RrLean.RiemannRochV2.ResidueTheory.ResidueLinearCorrect
import RrLean.RiemannRochV2.ResidueTheory.ResidueAtInfinity
import RrLean.RiemannRochV2.SerreDuality.RatFuncResidues
import RrLean.RiemannRochV2.P1Instance.PlaceDegree
import RrLean.RiemannRochV2.P1Instance.GapBoundGeneral

/-!
# Traced Residues for Higher-Degree Places

For a place v of degree d = [κ(v) : k] > 1, the "local residue" gives an element
of the residue field κ(v), not the base field k. To get a value in k, we need
to apply the trace map Tr_{κ(v)/k}.

## Mathematical Background

For a curve C over a finite field k = Fq:
- Places v correspond to prime ideals in the coordinate ring R
- The residue field κ(v) = R/v is a finite extension of k
- deg(v) = [κ(v) : k]

For the residue theorem ∑_v res_v(ω) = 0 with values in k, we need:
- For degree-1 places: res_v ∈ k directly
- For higher-degree places: Tr_{κ(v)/k}(local_res_v) ∈ k

## Key Insight for P¹

For P¹ = RatFunc Fq, ALL finite places have κ(v) ≅ Fq (degree 1).
This means Tr_{κ(v)/Fq} = id, so traced residue = local residue.

For other curves (elliptic, hyperelliptic), there may be higher-degree places
where the trace is non-trivial.

## References

- Rosen "Number Theory in Function Fields" Chapter 5
- Stichtenoth "Algebraic Function Fields and Codes" Section 3.1
-/

noncomputable section

open scoped LaurentSeries
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace RiemannRochV2.ResidueTrace

/-! ## Residue Field as k-Algebra

The residue field κ(v) = R ⧸ v.asIdeal inherits an algebra structure from k → R.
-/

variable {k : Type*} [Field k]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra k R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [Algebra k K]
  [IsScalarTower k R K]

/-- The residue field κ(v) = R/v as a k-algebra.

The algebra structure comes from the composition k → R → R/v. -/
instance residueField_algebra (v : HeightOneSpectrum R) :
    Algebra k (R ⧸ v.asIdeal) :=
  Ideal.Quotient.algebra k

/-! ## Degree of a Place

The degree of a place v is the dimension [κ(v) : k].
For P¹ over k, all places have degree 1 (linear places).
-/

/-- The degree of a finite place v is [κ(v) : k].
This is 1 for "rational" points (where κ(v) ≅ k). -/
def residueFieldDegree (v : HeightOneSpectrum R) : ℕ :=
  Module.finrank k (R ⧸ v.asIdeal)

/-- A place is degree-1 (rational) if κ(v) ≅ k. -/
def isRationalPlace (v : HeightOneSpectrum R) : Prop :=
  residueFieldDegree (k := k) v = 1

/-! ## Traced Residue Framework

The traced residue is defined for places where κ(v) is a finite extension of k.
It combines:
1. Local residue at v (an element of κ(v))
2. Trace from κ(v) to k
-/

section TracedResidue

variable (Fq : Type*) [Field Fq]

/-- The trace map from the residue field to the base field.

For a place v where κ(v) is a finite-dimensional k-algebra, this is
the standard algebraic trace Tr_{κ(v)/k}. -/
def traceToBase (v : HeightOneSpectrum (Polynomial Fq))
    [FiniteDimensional Fq (Polynomial Fq ⧸ v.asIdeal)] :
    (Polynomial Fq ⧸ v.asIdeal) →ₗ[Fq] Fq :=
  Algebra.trace Fq (Polynomial Fq ⧸ v.asIdeal)

/-- For a degree-1 place, the trace map acts as the identity (after
identifying κ(v) with Fq via the canonical isomorphism).

More precisely, if [κ(v) : Fq] = 1, then Tr(x) = x for all x ∈ κ(v). -/
theorem trace_degree_one_eq (v : HeightOneSpectrum (Polynomial Fq))
    [FiniteDimensional Fq (Polynomial Fq ⧸ v.asIdeal)]
    (hv : residueFieldDegree (k := Fq) v = 1) (x : Polynomial Fq ⧸ v.asIdeal) :
    ∃ (e : (Polynomial Fq ⧸ v.asIdeal) ≃ₐ[Fq] Fq),
      Algebra.trace Fq (Polynomial Fq ⧸ v.asIdeal) x = e x := by
  -- v.asIdeal is prime and nonzero, hence maximal in a Dedekind domain
  haveI hmax : v.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal v.isPrime v.ne_bot
  -- κ(v) is a field (since v.asIdeal is maximal)
  letI : Field (Polynomial Fq ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  -- Any vector space over a field is free
  haveI : Module.Free Fq (Polynomial Fq ⧸ v.asIdeal) := inferInstance
  -- finrank = 1 implies ⊥ = ⊤ as subalgebras
  have hbot_eq_top : (⊥ : Subalgebra Fq (Polynomial Fq ⧸ v.asIdeal)) = ⊤ :=
    Subalgebra.bot_eq_top_of_finrank_eq_one hv
  -- Build the isomorphism κ(v) ≃ₐ Fq by composing: κ(v) ≃ ⊤ ≃ ⊥ ≃ Fq
  let e₁ : (Polynomial Fq ⧸ v.asIdeal) ≃ₐ[Fq] (⊤ : Subalgebra Fq (Polynomial Fq ⧸ v.asIdeal)) :=
    Subalgebra.topEquiv.symm
  let e₂ : (⊤ : Subalgebra Fq (Polynomial Fq ⧸ v.asIdeal)) ≃ₐ[Fq]
           (⊥ : Subalgebra Fq (Polynomial Fq ⧸ v.asIdeal)) :=
    Subalgebra.equivOfEq _ _ hbot_eq_top.symm
  let e₃ : (⊥ : Subalgebra Fq (Polynomial Fq ⧸ v.asIdeal)) ≃ₐ[Fq] Fq :=
    Algebra.botEquiv Fq (Polynomial Fq ⧸ v.asIdeal)
  let e := e₁.trans (e₂.trans e₃)
  -- Show trace = e via trace_eq_of_algEquiv and trace_self
  refine ⟨e, ?_⟩
  -- trace Fq κ(v) x = trace Fq Fq (e x) = e x
  rw [← Algebra.trace_eq_of_algEquiv e x, Algebra.trace_self_apply]

/-! ## P¹-Specific: Linear Places

For P¹ = RatFunc Fq, all finite places correspond to irreducible polynomials.
Linear places correspond to (X - α) for α ∈ Fq.
-/

/-- HeightOneSpectrum for linear place (X - α). -/
def linearPlace (α : Fq) : HeightOneSpectrum (Polynomial Fq) where
  asIdeal := Ideal.span {Polynomial.X - Polynomial.C α}
  isPrime := Ideal.span_singleton_prime (Polynomial.X_sub_C_ne_zero α) |>.mpr
              (Polynomial.irreducible_X_sub_C α).prime
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact Polynomial.X_sub_C_ne_zero α

/-- The residue field at a linear place is isomorphic to Fq.

This is the evaluation map: Fq[X]/(X - α) → Fq via p ↦ p(α). -/
def linearPlace_residueField_equiv (α : Fq) :
    (Polynomial Fq ⧸ (linearPlace Fq α).asIdeal) ≃ₐ[Fq] Fq :=
  -- (linearPlace Fq α).asIdeal = Ideal.span {X - C α} by definition
  Polynomial.quotientSpanXSubCAlgEquiv α

/-- Linear places have degree 1. -/
theorem linearPlace_degree_eq_one (α : Fq) :
    residueFieldDegree (k := Fq) (linearPlace Fq α) = 1 := by
  unfold residueFieldDegree
  have e := linearPlace_residueField_equiv Fq α
  have h1 : Module.finrank Fq Fq = 1 := Module.finrank_self Fq
  rw [← h1]
  exact LinearEquiv.finrank_eq e.toLinearEquiv

/-- Linear places are rational. -/
theorem linearPlace_isRational (α : Fq) :
    isRationalPlace (k := Fq) (linearPlace Fq α) :=
  linearPlace_degree_eq_one Fq α

/-- The residue field at a linear place is finite-dimensional over Fq.

This is required for the trace map to be well-defined. -/
instance linearPlace_finiteDimensional (α : Fq) :
    FiniteDimensional Fq (Polynomial Fq ⧸ (linearPlace Fq α).asIdeal) := by
  have e := linearPlace_residueField_equiv Fq α
  -- Fq over Fq is finite-dimensional (dimension 1)
  haveI : FiniteDimensional Fq Fq := inferInstance
  -- Transfer via the linear equivalence: if W is fin-dim and V ≃ₗ W, then V is fin-dim
  exact LinearEquiv.finiteDimensional e.symm.toLinearEquiv

/-! ## Traced Residue Definition -/

/-- The traced residue at a linear place α.

For linear places, this equals the standard residue because the trace
from a degree-1 extension is the identity.

IMPLEMENTATION: We use the existing `residueAt` and show equality with
the traced version for linear places. -/
def residueAtLinearTraced (α : Fq) (f : RatFunc Fq) : Fq :=
  RiemannRochV2.Residue.residueAt α f

/-- The traced residue at a linear place equals the standard residue.

This is the key compatibility theorem for P¹. -/
theorem residueAtLinearTraced_eq_residueAt (α : Fq) (f : RatFunc Fq) :
    residueAtLinearTraced Fq α f = RiemannRochV2.Residue.residueAt α f :=
  rfl

/-- Traced residue at linear place is additive. -/
theorem residueAtLinearTraced_add (α : Fq) (f g : RatFunc Fq) :
    residueAtLinearTraced Fq α (f + g) =
    residueAtLinearTraced Fq α f + residueAtLinearTraced Fq α g := by
  simp only [residueAtLinearTraced]
  exact RiemannRochV2.Residue.residueAt_add α f g

/-- Traced residue at linear place respects scalar multiplication. -/
theorem residueAtLinearTraced_smul (α : Fq) (c : Fq) (f : RatFunc Fq) :
    residueAtLinearTraced Fq α (c • f) = c * residueAtLinearTraced Fq α f := by
  simp only [residueAtLinearTraced]
  exact RiemannRochV2.Residue.residueAt_smul α c f

end TracedResidue

/-! ## Global Residue Theorem with Traced Residues

For P¹, where all finite places are linear, the traced residue theorem
reduces to the standard residue theorem.

The general formulation (for arbitrary curves with higher-degree places)
would sum Tr_{κ(v)/k}(res_v(f)) over all finite places v.
-/

section GlobalResidueTheorem

variable (Fq : Type*) [Field Fq]

/-- Sum of traced residues at specified linear places.

This is the finite part of the residue sum for P¹. -/
def tracedResidueSum (S : Finset Fq) (f : RatFunc Fq) : Fq :=
  S.sum fun α => residueAtLinearTraced Fq α f

/-- Traced residue sum is additive. -/
theorem tracedResidueSum_add (S : Finset Fq) (f g : RatFunc Fq) :
    tracedResidueSum Fq S (f + g) =
    tracedResidueSum Fq S f + tracedResidueSum Fq S g := by
  unfold tracedResidueSum
  simp only [residueAtLinearTraced_add]
  rw [← Finset.sum_add_distrib]

/-- The global residue theorem for P¹ with traced residues.

This is equivalent to the standard residue theorem since all places are linear.

∑_{α ∈ S} Tr(res_α(f)) + res_∞(f) = 0

For P¹, Tr = id, so this is just:
∑_{α ∈ S} res_α(f) + res_∞(f) = 0
-/
theorem residue_sum_traced_eq_zero_P1 [Fintype Fq] (f : RatFunc Fq) (S : Finset Fq)
    (hS : ∀ α, α ∉ S → RiemannRochV2.Residue.residueAt α f = 0)
    (hsplit : ∃ p : Polynomial Fq, ∃ poles : Finset Fq, f =
      (algebraMap (Polynomial Fq) (RatFunc Fq) p) /
      (poles.prod fun a => RatFunc.X - RatFunc.C a)) :
    tracedResidueSum Fq S f + RiemannRochV2.Residue.residueAtInfty f = 0 := by
  -- The traced residue sum over S equals the full sum over Fq
  -- because residues outside S are zero by hypothesis hS
  have h_sum_eq : tracedResidueSum Fq S f =
      Finset.univ.sum (fun α => RiemannRochV2.Residue.residueAt α f) := by
    unfold tracedResidueSum residueAtLinearTraced
    rw [Finset.sum_subset (Finset.subset_univ S)]
    intro α _ hα
    exact hS α hα
  rw [h_sum_eq]
  -- The sum over Finset.univ equals residueSumFinite
  have h_eq_finite : Finset.univ.sum (fun α => RiemannRochV2.Residue.residueAt α f) =
      RiemannRochV2.residueSumFinite f := by
    rfl
  rw [h_eq_finite]
  -- Now residueSumFinite + residueAtInfty = residueSumTotal = 0 for split denominators
  have h_total : RiemannRochV2.residueSumFinite f + RiemannRochV2.Residue.residueAtInfty f =
      RiemannRochV2.residueSumTotal f := rfl
  rw [h_total]
  -- Apply the residue theorem for split denominators
  exact RiemannRochV2.residueSumTotal_splits f hsplit

end GlobalResidueTheorem

/-! ## Higher-Degree Residues at Arbitrary Places

For places of degree d > 1, we need:
1. Local residue in κ(v) = k[X]/(p) where p is the irreducible generator
2. Trace map Tr_{κ(v)/k} to get values back in the base field k

The key insight: for f = num/denom with p | denom (p = generator of v),
the local residue at v is computed via partial fractions.

For simple poles (p | denom, p² ∤ denom), writing denom = p · q with gcd(p,q) = 1:
  res_v(f) = (num · q⁻¹) mod p ∈ κ(v)

where q⁻¹ exists in κ(v) since q ∉ (p).
-/

section HigherDegreeResidues

variable (Fq : Type*) [Field Fq] [DecidableEq Fq]

open RiemannRochV2.PlaceDegree Polynomial
open scoped Classical

/-! ### Finiteness of Residue Fields -/

/-- The residue field κ(v) = Fq[X]/(p) is finite-dimensional over Fq.
This follows from the fact that p is monic irreducible. -/
instance residueField_finiteDimensional (v : HeightOneSpectrum (Polynomial Fq)) :
    FiniteDimensional Fq (Polynomial Fq ⧸ v.asIdeal) := by
  haveI : Module.Finite Fq (Polynomial Fq ⧸ v.asIdeal) := RiemannRochV2.residueField_finite Fq v
  infer_instance

/-- The finrank of κ(v) equals the degree of the place. -/
lemma finrank_residueField_eq_placeDegree (v : HeightOneSpectrum (Polynomial Fq)) :
    Module.finrank Fq (Polynomial Fq ⧸ v.asIdeal) = degree Fq v :=
  finrank_residueField_eq_degree Fq v

/-! ### Local Residue at Arbitrary Places -/

/-- Check if the denominator of f is divisible by the generator of v.
This determines whether f has a pole at v. -/
def hasPoleAt (v : HeightOneSpectrum (Polynomial Fq)) (f : RatFunc Fq) : Prop :=
  generator Fq v ∣ f.denom

/-- Check if f has a simple pole at v (p | denom, p² ∤ denom). -/
def hasSimplePoleAt (v : HeightOneSpectrum (Polynomial Fq)) (f : RatFunc Fq) : Prop :=
  generator Fq v ∣ f.denom ∧ ¬(generator Fq v ^ 2 ∣ f.denom)

/-- The "coprime cofactor" q where denom = gen * q and gcd(gen, q) = 1.
For a simple pole, this is the part of the denominator coprime to the generator.

This is only well-defined when gen | denom; otherwise returns 0. -/
noncomputable def denomCofactor (v : HeightOneSpectrum (Polynomial Fq)) (f : RatFunc Fq) :
    Polynomial Fq :=
  if _h : generator Fq v ∣ f.denom then
    f.denom /ₘ generator Fq v
  else 0

/-- The cofactor is nonzero when f has a pole at v. -/
lemma denomCofactor_ne_zero (v : HeightOneSpectrum (Polynomial Fq)) (f : RatFunc Fq)
    (hpole : hasPoleAt Fq v f) (_hf_ne : f ≠ 0) : denomCofactor Fq v f ≠ 0 := by
  unfold denomCofactor hasPoleAt at *
  simp only [dif_pos hpole]
  intro hq
  have hmonic := generator_monic Fq v
  have hdiv := Polynomial.modByMonic_add_div f.denom hmonic
  have hmod_zero : f.denom %ₘ generator Fq v = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hpole
  simp only [hmod_zero, zero_add] at hdiv
  rw [hq, mul_zero] at hdiv
  exact RatFunc.denom_ne_zero f hdiv.symm

/-- The cofactor is coprime to the generator for a simple pole.
(When p | denom and p² ∤ denom, the cofactor q = denom/p satisfies gcd(p, q) = 1.) -/
lemma denomCofactor_coprime (v : HeightOneSpectrum (Polynomial Fq)) (f : RatFunc Fq)
    (hsimple : hasSimplePoleAt Fq v f) :
    IsCoprime (generator Fq v) (denomCofactor Fq v f) := by
  -- Proof: If gcd(gen, q) ≠ 1 where q = denom/gen, then gen | q (since gen is irreducible).
  -- But gen | q means gen² | denom, contradicting gen² ∤ denom.
  unfold hasSimplePoleAt at hsimple
  obtain ⟨hpole, hnotsq⟩ := hsimple
  unfold denomCofactor
  simp only [dif_pos hpole]
  -- Show gen ∤ (denom /ₘ gen), which implies gcd = 1 for irreducibles
  have hirr := generator_irreducible Fq v
  rw [Irreducible.coprime_iff_not_dvd hirr]
  intro hgen_dvd_q
  -- gen | q and denom = gen * q implies gen² | denom
  have hmonic := generator_monic Fq v
  have hdenom_eq : f.denom = generator Fq v * (f.denom /ₘ generator Fq v) := by
    have h := Polynomial.modByMonic_add_div f.denom hmonic
    have hmod_zero : f.denom %ₘ generator Fq v = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hpole
    simp only [hmod_zero, zero_add] at h
    exact h.symm
  obtain ⟨r, hr⟩ := hgen_dvd_q
  rw [hdenom_eq, hr, ← mul_assoc, pow_two] at hnotsq
  exact hnotsq (dvd_mul_right _ _)

/-- The cofactor is not in v.asIdeal (its residue is nonzero in κ(v)). -/
lemma denomCofactor_not_mem_asIdeal (v : HeightOneSpectrum (Polynomial Fq)) (f : RatFunc Fq)
    (hsimple : hasSimplePoleAt Fq v f) :
    denomCofactor Fq v f ∉ v.asIdeal := by
  intro hmem
  rw [asIdeal_eq_span_generator Fq v, Ideal.mem_span_singleton] at hmem
  have hcop := denomCofactor_coprime Fq v f hsimple
  -- gen | q contradicts gcd(gen, q) = 1 since gen is irreducible (not a unit)
  have hunit := IsCoprime.isUnit_of_dvd' hcop (dvd_refl _) hmem
  exact not_isUnit_of_not_isUnit_dvd (generator_irreducible Fq v).1 (dvd_refl _) hunit

/-- The residue of the cofactor in κ(v) is invertible. -/
lemma denomCofactor_residue_isUnit (v : HeightOneSpectrum (Polynomial Fq)) (f : RatFunc Fq)
    (hsimple : hasSimplePoleAt Fq v f) :
    IsUnit (Ideal.Quotient.mk v.asIdeal (denomCofactor Fq v f)) := by
  -- κ(v) is a field since v.asIdeal is maximal
  haveI hmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : Field (Polynomial Fq ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  -- In a field, nonzero elements are units
  apply isUnit_iff_ne_zero.mpr
  rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact denomCofactor_not_mem_asIdeal Fq v f hsimple

/-- The local residue of f at place v (for simple poles).

For f = num/(gen · q) where gen = generator of v and gcd(gen, q) = 1:
  res_v(f) = (num · q⁻¹) mod gen ∈ κ(v)

Returns 0 if f does not have a simple pole at v.
-/
noncomputable def localResidueAtPlace (v : HeightOneSpectrum (Polynomial Fq)) (f : RatFunc Fq) :
    Polynomial Fq ⧸ v.asIdeal :=
  if hsimple : hasSimplePoleAt Fq v f then
    let num_res := Ideal.Quotient.mk v.asIdeal f.num
    -- The cofactor residue is a unit by denomCofactor_residue_isUnit
    num_res * (denomCofactor_residue_isUnit Fq v f hsimple).unit⁻¹
  else 0

/-- For non-poles, the local residue is zero. -/
lemma localResidueAtPlace_eq_zero_of_no_pole (v : HeightOneSpectrum (Polynomial Fq)) (f : RatFunc Fq)
    (hnopole : ¬hasPoleAt Fq v f) : localResidueAtPlace Fq v f = 0 := by
  unfold localResidueAtPlace hasSimplePoleAt
  have hns : ¬(generator Fq v ∣ f.denom ∧ ¬generator Fq v ^ 2 ∣ f.denom) := by
    push_neg
    intro hpole
    exact absurd hpole hnopole
  simp only [dif_neg hns]

/-! ### Traced Residue at Arbitrary Places -/

/-- The traced residue at an arbitrary place v.

Computes Tr_{κ(v)/Fq}(localResidueAtPlace v f) ∈ Fq.

For degree-1 places (linear places), this equals the standard residue
since trace from a 1-dimensional extension is the identity.
-/
noncomputable def tracedResidueAtPlace (v : HeightOneSpectrum (Polynomial Fq)) (f : RatFunc Fq) :
    Fq :=
  Algebra.trace Fq (Polynomial Fq ⧸ v.asIdeal) (localResidueAtPlace Fq v f)

/-- Traced residue is zero at non-poles. -/
lemma tracedResidueAtPlace_eq_zero_of_no_pole (v : HeightOneSpectrum (Polynomial Fq)) (f : RatFunc Fq)
    (hnopole : ¬hasPoleAt Fq v f) : tracedResidueAtPlace Fq v f = 0 := by
  unfold tracedResidueAtPlace
  rw [localResidueAtPlace_eq_zero_of_no_pole Fq v f hnopole, map_zero]

/-- For linear places, the traced residue equals the standard residue.

At a linear place (X - α), the residue field κ(v) ≅ Fq via evaluation at α.
The trace from Fq to Fq is the identity, so traced residue = local residue = standard residue.

**Mathematical fact**: Both approaches compute the same residue:
- `tracedResidueAtPlace`: (num · q⁻¹)(α) where denom = (X-α)·q
- `residueAt α`: coefficient of 1/(X-α) in partial fraction expansion

The proof requires showing these computational definitions agree, which follows from
the uniqueness of partial fraction decomposition.

**Proof sketch**:
1. For simple pole: f = num/((X-α)·q) = A/(X-α) + (regular part) for some A ∈ Fq
2. A = num(α)/q(α) by the residue formula (multiply by (X-α) and evaluate at α)
3. Our formula: (num · q⁻¹) mod (X-α) = num(α) · q(α)⁻¹ = A
4. Since κ(v) ≅ Fq via evaluation, and trace = identity for degree-1, we get tracedResidueAtPlace = A
-/
theorem tracedResidueAtPlace_eq_residueAt_linear (α : Fq) (f : RatFunc Fq) :
    tracedResidueAtPlace Fq (linearPlace Fq α) f =
    RiemannRochV2.Residue.residueAt α f := by
  -- The proof connects two computational approaches:
  -- 1. Our approach: (num · denomCofactor⁻¹) mod gen, then trace
  -- 2. Standard: Laurent coefficient via translation
  -- Both equal num(α)/cofactor(α) for simple poles at linear places
  sorry

end HigherDegreeResidues

end RiemannRochV2.ResidueTrace

end
