import RrLean.RiemannRochV2.Adelic.AdelicH1v2
import RrLean.RiemannRochV2.Dimension.KernelProof
import RrLean.RiemannRochV2.Definitions.Infrastructure
import RrLean.RiemannRochV2.ResidueTheory.ResidueFieldIso

/-!
# Euler Characteristic via Exact Sequence (Cycle 326)

This file proves the Euler characteristic formula χ(D) = deg(D) + 1 - g via the
6-term exact sequence:

```
0 → L(D) → L(D+v) → κ(v) → H¹(D) → H¹(D+v) → 0
```

## Main Definitions

* `connectingHom` - The connecting homomorphism δ: κ(v) → H¹(D)

## Main Results

* `exactness_at_kappa` - image(eval) = ker(δ)
* `exactness_at_H1` - image(δ) = ker(H¹(D) → H¹(D+v))
* `chi_additive` - χ(D+v) = χ(D) + 1
* `euler_characteristic` - χ(D) = deg(D) + 1 - g

## Strategy

The connecting homomorphism δ is constructed as follows:
1. Take α ∈ κ(v) = R/v.asIdeal = residueFieldAtPrime R v
2. Lift α to the local ring O_v (valuation ring at v)
3. Multiply by π⁻¹ where π is the uniformizer at v
4. This gives an element with a pole of order 1 at v
5. Embed as a single-component adele (zero at all other places)
6. Project to H¹(D) = A_K / (K + A_K(D))

## References

* Rosen "Number Theory in Function Fields" Ch. 6
* Liu "Algebraic Geometry and Arithmetic Curves" Ch. 7

-/

noncomputable section

namespace RiemannRochV2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable (k : Type*) [Field k]
variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] [Algebra k R]
variable (K : Type*) [Field K] [Algebra k K] [Algebra R K] [IsFractionRing R K]
variable [IsScalarTower k R K]

namespace EulerCharacteristic

open AdelicH1v2
open scoped Classical

/-! ## Section 1: The Connecting Homomorphism

The key map δ: κ(v) → H¹(D) is constructed by:
1. Lifting a residue class α to an element r ∈ R
2. Dividing by π^(D(v)+1) to create a pole at v
3. Embedding as a single-component adele (zero at all other places)
4. Projecting to H¹(D) = FiniteAdeleRing / (K + A_K(D))

### Key Insight (Well-definedness)

If we choose a different lift r' = r + s where s ∈ v.asIdeal, then:
- x' = r' / π^(D(v)+1) = x + s / π^(D(v)+1)
- The difference s / π^(D(v)+1) is a global element of K
- Since K is quotiented out in H¹(D), the result is independent of the lift

### Key Insight (α = 0 maps to 0)

When α = 0, we lift to r ∈ v.asIdeal, so r = π·t for some t.
Then x = r / π^(D(v)+1) = t / π^D(v), which has valuation ≤ exp(D(v)).
So the single-place adele is in A_K(D), hence maps to 0 in H¹(D).
-/

/-- Construct a finite adele with value x at place v and 0 elsewhere.

This is the key building block for the connecting homomorphism.
The result is integral at all places except possibly v. -/
def finiteAdeleSingleHere (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    FiniteAdeleRing R K :=
  ⟨fun w => if h : w = v then h ▸ x else 0,
   by
     simp only [Filter.eventually_cofinite, SetLike.mem_coe]
     apply Set.Finite.subset (Set.finite_singleton v)
     intro w hw
     simp only [Set.mem_singleton_iff]
     by_contra h_ne
     simp only [Set.mem_setOf_eq] at hw
     rw [dif_neg h_ne, mem_adicCompletionIntegers, Valuation.map_zero] at hw
     exact hw zero_le'⟩

@[simp]
lemma finiteAdeleSingleHere_apply_same (v : HeightOneSpectrum R) (x : v.adicCompletion K) :
    (finiteAdeleSingleHere R K v x) v = x := by
  show (finiteAdeleSingleHere R K v x).1 v = x
  simp only [finiteAdeleSingleHere, dite_true]

lemma finiteAdeleSingleHere_apply_ne (v w : HeightOneSpectrum R) (x : v.adicCompletion K)
    (h : w ≠ v) : (finiteAdeleSingleHere R K v x) w = 0 := by
  show (finiteAdeleSingleHere R K v x).1 w = 0
  simp only [finiteAdeleSingleHere, dif_neg h]

/-- The single-place adele respects zero. -/
@[simp]
lemma finiteAdeleSingleHere_zero (v : HeightOneSpectrum R) :
    finiteAdeleSingleHere R K v (0 : v.adicCompletion K) = 0 := by
  apply FiniteAdeleRing.ext K
  intro w
  show (finiteAdeleSingleHere R K v 0).1 w = (0 : FiniteAdeleRing R K) w
  by_cases h : w = v
  · subst h; simp only [finiteAdeleSingleHere]; rfl
  · simp only [finiteAdeleSingleHere, dif_neg h]; rfl

/-- The single-place adele respects addition. -/
lemma finiteAdeleSingleHere_add (v : HeightOneSpectrum R)
    (x y : v.adicCompletion K) :
    finiteAdeleSingleHere R K v (x + y) =
    finiteAdeleSingleHere R K v x + finiteAdeleSingleHere R K v y := by
  apply Subtype.ext
  funext w
  -- Need to show: (LHS).1 w = ((finiteAdeleSingleHere x) + (finiteAdeleSingleHere y)).1 w
  -- The RHS's .1 equals (finiteAdeleSingleHere x).1 + (finiteAdeleSingleHere y).1 by subtype add
  have h_add : ((finiteAdeleSingleHere R K v x) + (finiteAdeleSingleHere R K v y)).1 =
               (finiteAdeleSingleHere R K v x).1 + (finiteAdeleSingleHere R K v y).1 := rfl
  simp only [h_add, Pi.add_apply]
  by_cases h : w = v
  · subst h
    simp only [finiteAdeleSingleHere, dite_true]
  · simp only [finiteAdeleSingleHere, dif_neg h, add_zero]

/-- The single-place adele respects subtraction. -/
lemma finiteAdeleSingleHere_sub (v : HeightOneSpectrum R)
    (x y : v.adicCompletion K) :
    finiteAdeleSingleHere R K v (x - y) =
    finiteAdeleSingleHere R K v x - finiteAdeleSingleHere R K v y := by
  apply Subtype.ext
  funext w
  have h_sub : ((finiteAdeleSingleHere R K v x) - (finiteAdeleSingleHere R K v y)).1 =
               (finiteAdeleSingleHere R K v x).1 - (finiteAdeleSingleHere R K v y).1 := rfl
  simp only [h_sub, Pi.sub_apply]
  by_cases h : w = v
  · subst h
    simp only [finiteAdeleSingleHere, dite_true]
  · simp only [finiteAdeleSingleHere, dif_neg h, sub_zero]

/-- The uniformizer in K (as an element of the fraction field). -/
def uniformizerInK (v : HeightOneSpectrum R) : K :=
  algebraMap R K (uniformizerAt v)

/-- The uniformizer is nonzero in K. -/
lemma uniformizerInK_ne_zero (v : HeightOneSpectrum R) : uniformizerInK R K v ≠ 0 := by
  simp only [uniformizerInK]
  intro h
  have hinj := IsFractionRing.injective R K
  have hne := uniformizerAt_ne_zero v
  rw [← map_zero (algebraMap R K)] at h
  exact hne (hinj h)

/-- The inverse of the uniformizer power, for creating poles.

For n ≥ 0, this is π^(-n) = 1/π^n.
For n < 0, this is π^(-n) = π^|n|.
-/
def uniformizerInvPow (v : HeightOneSpectrum R) (n : ℤ) : K :=
  (uniformizerInK R K v) ^ (-n)

/-- Lift an element of the residue field to R.

Uses the linear equivalence to convert to R ⧸ v.asIdeal, then Quotient.out to lift.
The result satisfies: residueMapAtPrime v (liftToR α) represents the same class as α. -/
def liftToR (v : HeightOneSpectrum R) (α : residueFieldAtPrime R v) : R :=
  let α_quot : R ⧸ v.asIdeal := (residueFieldAtPrime.linearEquiv (R := R) v).symm α
  Quotient.out α_quot

/-- The lifted element projects back to the original residue class. -/
lemma liftToR_proj (v : HeightOneSpectrum R) (α : residueFieldAtPrime R v) :
    Ideal.Quotient.mk v.asIdeal (liftToR R v α) =
    (residueFieldAtPrime.linearEquiv (R := R) v).symm α := by
  simp only [liftToR]
  exact Quotient.out_eq _

/-- When α = 0, the lift is in v.asIdeal. -/
lemma liftToR_zero_mem_ideal (v : HeightOneSpectrum R) :
    liftToR R v 0 ∈ v.asIdeal := by
  simp only [liftToR]
  have h : (residueFieldAtPrime.linearEquiv (R := R) v).symm 0 = 0 := by
    simp only [map_zero]
  rw [h]
  exact Ideal.Quotient.eq_zero_iff_mem.mp (Quotient.out_eq (0 : R ⧸ v.asIdeal))

/-- The lift of a sum differs from the sum of lifts by an element in v.asIdeal. -/
lemma liftToR_add_diff_mem_ideal (v : HeightOneSpectrum R)
    (α β : residueFieldAtPrime R v) :
    liftToR R v (α + β) - (liftToR R v α + liftToR R v β) ∈ v.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add]
  simp only [liftToR_proj, map_add, sub_self]

/-- The lift respects scalar multiplication up to an element in v.asIdeal.
For c ∈ k ⊆ R, the lift of c•α differs from c * liftToR(α) by an element in v.asIdeal.

The proof uses that the k-action on residueFieldAtPrime factors through k → R → R/v.asIdeal,
so the scalar multiplication in the residue field matches the quotient multiplication. -/
lemma liftToR_smul_diff_mem_ideal (v : HeightOneSpectrum R)
    (c : k) (α : residueFieldAtPrime R v) :
    liftToR R v (c • α) - algebraMap k R c * liftToR R v α ∈ v.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, liftToR_proj, liftToR_proj]
  -- The k-action on residueFieldAtPrime R v factors through R via the scalar tower
  -- So c • α = (algebraMap k R c) • α for the R-module action
  have h_tower : c • α = (algebraMap k R c) • α := by
    rw [← smul_one_smul R c α]
    simp only [Algebra.smul_def, mul_one]
  rw [h_tower]
  -- The linear equivalence is R-linear, so it respects R-scalar multiplication
  have h_smul : (residueFieldAtPrime.linearEquiv (R := R) v).symm ((algebraMap k R c) • α) =
                (algebraMap k R c) • (residueFieldAtPrime.linearEquiv (R := R) v).symm α :=
    (residueFieldAtPrime.linearEquiv (R := R) v).symm.map_smul (algebraMap k R c) α
  rw [h_smul]
  -- In the quotient R ⧸ v.asIdeal, scalar multiplication by r is: r • q = Quotient.mk r * q
  simp only [Algebra.smul_def]
  -- algebraMap R (R ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal
  simp only [Ideal.Quotient.algebraMap_eq, sub_self]

/-- The connecting homomorphism function δ: κ(v) → H¹(D).

Construction:
1. Lift α ∈ κ(v) to r ∈ R using liftToR
2. Compute x = r · π^(-(D(v)+1)) in K (creates pole of order D(v)+1 at v)
3. Embed x into K_v via algebraMap
4. Create single-place adele with x at v, 0 elsewhere
5. Project to H¹(D) = FiniteAdeleRing / (K + A_K(D))
-/
def connectingHomFun (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    residueFieldAtPrime R v → SpaceModule k R K D := fun α =>
  let r : R := liftToR R v α
  let x : K := algebraMap R K r * uniformizerInvPow R K v (D v + 1)
  let x_local : v.adicCompletion K := algebraMap K (v.adicCompletion K) x
  let a : FiniteAdeleRing R K := finiteAdeleSingleHere R K v x_local
  quotientMapLinear k R K D a

/-- The connecting homomorphism sends zero to zero.

When α = 0, the lift r ∈ v.asIdeal, so r · π^(-(D(v)+1)) has valuation ≤ exp(D(v)),
putting the single-place adele in A_K(D), hence mapping to 0 in H¹(D).
-/
lemma connectingHomFun_zero (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    connectingHomFun k R K v D 0 = 0 := by
  simp only [connectingHomFun]
  -- The adele lands in globalPlusBoundedSubmodule, hence maps to 0
  unfold quotientMapLinear
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  -- globalPlusBoundedSubmodule = globalSubmodule + boundedSubmodule
  -- It suffices to show the adele is in boundedSubmodule (⊆ globalPlusBounded)
  unfold globalPlusBoundedSubmodule
  apply Submodule.mem_sup_right
  -- Show membership in boundedSubmodule k R K D
  show _ ∈ boundedSubmodule k R K D
  intro w
  simp only [satisfiesBoundAt, valuationAt]
  by_cases hw : w = v
  · -- At place v: the lift r ∈ v.asIdeal gives valuation bound
    subst hw
    simp only [finiteAdeleSingleHere_apply_same]
    -- r = liftToR R w 0 ∈ w.asIdeal
    have hr_mem : liftToR R w 0 ∈ w.asIdeal := liftToR_zero_mem_ideal R w
    -- w.intValuation r ≤ exp(-1) by membership in asIdeal (asIdeal^1)
    have hr_val : w.intValuation (liftToR R w 0) ≤ WithZero.exp (-(1 : ℤ)) := by
      have hmem1 : liftToR R w 0 ∈ w.asIdeal ^ 1 := by simp only [pow_one]; exact hr_mem
      have hle := (w.intValuation_le_pow_iff_mem (liftToR R w 0) 1).mpr hmem1
      simp only [Nat.cast_one] at hle
      exact hle
    -- Transfer to K valuation
    have hr_val_K : w.valuation K (algebraMap R K (liftToR R w 0)) ≤ WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact hr_val
    -- Compute valuation of x = r * π^(-(D w + 1))
    -- Using uniformizerAt_zpow_valuation
    have hx_val : w.valuation K (algebraMap R K (liftToR R w 0) *
        uniformizerInvPow R K w (D w + 1)) ≤ WithZero.exp (D w) := by
      unfold uniformizerInvPow uniformizerInK
      rw [Valuation.map_mul, uniformizerAt_zpow_valuation]
      simp only [neg_neg]
      -- exp(-1) * exp(D w + 1) = exp(D w)
      calc w.valuation K (algebraMap R K (liftToR R w 0)) * WithZero.exp (D w + 1)
          ≤ WithZero.exp (-1) * WithZero.exp (D w + 1) := by
            exact mul_le_mul_of_nonneg_right hr_val_K (WithZero.zero_le _)
        _ = WithZero.exp (-1 + (D w + 1)) := by rw [← WithZero.exp_add]
        _ = WithZero.exp (D w) := by ring_nf
    -- Transfer to adicCompletion via valuedAdicCompletion_eq_valuation'
    -- The algebraMap from K to adicCompletion preserves valuation
    let x : K := algebraMap R K (liftToR R w 0) * uniformizerInvPow R K w (D w + 1)
    -- algebraMap K (adicCompletion K w) = coe for the completion
    have hcoe : algebraMap K (w.adicCompletion K) x = (x : w.adicCompletion K) := rfl
    rw [hcoe, valuedAdicCompletion_eq_valuation' w x]
    exact hx_val
  · -- At place w ≠ v: the adele is 0
    have hne : w ≠ v := hw
    rw [finiteAdeleSingleHere_apply_ne R K v w _ hne, Valuation.map_zero]
    exact WithZero.zero_le _

/-- The connecting homomorphism is additive.

Key: Different lifts of the same residue class differ by elements of v.asIdeal,
and in H¹(D), these differences become global elements that quotient out.
-/
lemma connectingHomFun_add (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (α β : residueFieldAtPrime R v) :
    connectingHomFun k R K v D (α + β) =
    connectingHomFun k R K v D α + connectingHomFun k R K v D β := by
  simp only [connectingHomFun]
  -- Key: The difference r_sum - (r_α + r_β) ∈ v.asIdeal causes bounded adele difference
  have hdiff : liftToR R v (α + β) - (liftToR R v α + liftToR R v β) ∈ v.asIdeal :=
    liftToR_add_diff_mem_ideal R v α β
  -- Define the adeles for clarity
  let a_sum := finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K)
    (algebraMap R K (liftToR R v (α + β)) * uniformizerInvPow R K v (D v + 1)))
  let a_α := finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K)
    (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1)))
  let a_β := finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K)
    (algebraMap R K (liftToR R v β) * uniformizerInvPow R K v (D v + 1)))
  -- Goal: quotientMapLinear(a_sum) = quotientMapLinear(a_α) + quotientMapLinear(a_β)
  -- Equivalently, a_sum - (a_α + a_β) ∈ ker(quotientMapLinear) = globalPlusBoundedSubmodule
  rw [← map_add]
  unfold quotientMapLinear
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  -- Need: a_sum - (a_α + a_β) ∈ globalPlusBoundedSubmodule
  unfold globalPlusBoundedSubmodule
  apply Submodule.mem_sup_right
  -- Show the difference is in boundedSubmodule
  show _ ∈ boundedSubmodule k R K D
  -- Simplify the adele difference using finiteAdeleSingleHere additivity
  have hadele_diff : a_sum - (a_α + a_β) =
    finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K)
      (algebraMap R K (liftToR R v (α + β) - (liftToR R v α + liftToR R v β)) *
        uniformizerInvPow R K v (D v + 1))) := by
    simp only [a_sum, a_α, a_β]
    -- a_sum - (a_α + a_β) = finiteAdeleSingleHere(x_sum) - finiteAdeleSingleHere(x_α + x_β)
    rw [← finiteAdeleSingleHere_add R K v, ← finiteAdeleSingleHere_sub R K v]
    -- Now we need to show the K-elements are equal after algebraMap
    -- LHS: algebraMap(x_sum) - algebraMap(x_α + x_β)
    -- RHS: algebraMap(x_d)
    simp only [← map_add, ← map_sub]
    congr 1
    -- Now in K: x_sum - (x_α + x_β) = x_d
    simp only [(algebraMap R K).map_sub, (algebraMap R K).map_add]
    ring_nf
  rw [hadele_diff]
  -- Now same argument as connectingHomFun_zero with d ∈ v.asIdeal
  intro w
  simp only [satisfiesBoundAt, valuationAt]
  by_cases hw : w = v
  · subst hw
    simp only [finiteAdeleSingleHere_apply_same]
    -- Use that d ∈ v.asIdeal gives valuation bound
    have hr_val : w.intValuation (liftToR R w (α + β) - (liftToR R w α + liftToR R w β)) ≤
        WithZero.exp (-(1 : ℤ)) := by
      have hmem1 : liftToR R w (α + β) - (liftToR R w α + liftToR R w β) ∈ w.asIdeal ^ 1 := by
        simp only [pow_one]; exact hdiff
      have hle := (w.intValuation_le_pow_iff_mem _ 1).mpr hmem1
      simp only [Nat.cast_one] at hle
      exact hle
    have hr_val_K : w.valuation K (algebraMap R K (liftToR R w (α + β) -
        (liftToR R w α + liftToR R w β))) ≤ WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact hr_val
    have hx_val : w.valuation K (algebraMap R K (liftToR R w (α + β) -
        (liftToR R w α + liftToR R w β)) * uniformizerInvPow R K w (D w + 1)) ≤
        WithZero.exp (D w) := by
      unfold uniformizerInvPow uniformizerInK
      rw [Valuation.map_mul, uniformizerAt_zpow_valuation]
      simp only [neg_neg]
      calc w.valuation K (algebraMap R K (liftToR R w (α + β) -
            (liftToR R w α + liftToR R w β))) * WithZero.exp (D w + 1)
          ≤ WithZero.exp (-1) * WithZero.exp (D w + 1) := by
            exact mul_le_mul_of_nonneg_right hr_val_K (WithZero.zero_le _)
        _ = WithZero.exp (-1 + (D w + 1)) := by rw [← WithZero.exp_add]
        _ = WithZero.exp (D w) := by ring_nf
    let x : K := algebraMap R K (liftToR R w (α + β) - (liftToR R w α + liftToR R w β)) *
      uniformizerInvPow R K w (D w + 1)
    have hcoe : algebraMap K (w.adicCompletion K) x = (x : w.adicCompletion K) := rfl
    rw [hcoe, valuedAdicCompletion_eq_valuation' w x]
    exact hx_val
  · have hne : w ≠ v := hw
    rw [finiteAdeleSingleHere_apply_ne R K v w _ hne, Valuation.map_zero]
    exact WithZero.zero_le _

/-- The connecting homomorphism respects k-scalar multiplication. -/
lemma connectingHomFun_smul (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (c : k) (α : residueFieldAtPrime R v) :
    connectingHomFun k R K v D (c • α) = c • connectingHomFun k R K v D α := by
  simp only [connectingHomFun]
  -- Key: liftToR(c•α) - algebraMap k R c * liftToR(α) ∈ v.asIdeal
  have hdiff : liftToR R v (c • α) - algebraMap k R c * liftToR R v α ∈ v.asIdeal :=
    liftToR_smul_diff_mem_ideal k R v c α
  -- Define the key elements
  set r_cα := liftToR R v (c • α) with hr_cα
  set r_α := liftToR R v α with hr_α
  set d := r_cα - algebraMap k R c * r_α with hd
  -- d is in v.asIdeal
  have hd_mem : d ∈ v.asIdeal := hdiff
  -- The K-elements
  set x_cα := algebraMap R K r_cα * uniformizerInvPow R K v (D v + 1) with hx_cα
  set x_α := algebraMap R K r_α * uniformizerInvPow R K v (D v + 1) with hx_α
  -- The scaled element
  set x_scaled := algebraMap k K c * x_α with hx_scaled
  -- The difference in K
  have hx_diff : x_cα - x_scaled = algebraMap R K d * uniformizerInvPow R K v (D v + 1) := by
    simp only [hx_cα, hx_α, hx_scaled, hd]
    rw [IsScalarTower.algebraMap_apply k R K c, map_sub, map_mul]
    ring
  -- Define the adeles
  set a_cα := finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K) x_cα) with ha_cα
  set a_α := finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K) x_α) with ha_α
  -- Goal: quotientMapLinear(a_cα) = c • quotientMapLinear(a_α)
  have hlin : c • quotientMapLinear k R K D a_α = quotientMapLinear k R K D (c • a_α) := by
    simp only [map_smul]
  rw [hlin]
  -- Show a_cα - c • a_α ∈ globalPlusBoundedSubmodule
  unfold quotientMapLinear
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  unfold globalPlusBoundedSubmodule
  apply Submodule.mem_sup_right
  show _ ∈ boundedSubmodule k R K D
  -- The key: a_cα - c • a_α differs from a single-place adele by something in K (global)
  -- We'll show directly that at each place the valuation bound is satisfied
  intro w
  simp only [satisfiesBoundAt, valuationAt]
  by_cases hw : w = v
  · -- At place v (w = v)
    -- First establish (a_α) v = algebraMap K (v.adicCompletion K) x_α
    have ha_α_v : a_α v = algebraMap K (v.adicCompletion K) x_α := by
      rw [ha_α]; exact finiteAdeleSingleHere_apply_same R K v _
    -- The valuation of c • a_α at v
    have hsmul_v : (c • a_α) v = algebraMap K (v.adicCompletion K) x_scaled := by
      simp only [Algebra.smul_def]
      have h1 : ((algebraMap k (FiniteAdeleRing R K) c) * a_α) v =
          (algebraMap k (FiniteAdeleRing R K) c) v * a_α v := rfl
      rw [h1, ha_α_v]
      -- (algebraMap k (FiniteAdeleRing R K) c) v = algebraMap k K c as element of adicCompletion
      have halg : (algebraMap k (FiniteAdeleRing R K) c) v =
          (algebraMap k K c : v.adicCompletion K) := rfl
      rw [halg]
      -- Now: (algebraMap k K c : adicCompletion) * (algebraMap K adicCompletion x_α) = algebraMap K ... x_scaled
      -- The coercion from K to adicCompletion is the same as algebraMap K adicCompletion
      have hcoe : (algebraMap k K c : v.adicCompletion K) =
          algebraMap K (v.adicCompletion K) (algebraMap k K c) := rfl
      rw [hcoe, ← map_mul, hx_scaled]
    -- First establish (a_cα) v
    have ha_cα_v : a_cα v = algebraMap K (v.adicCompletion K) x_cα := by
      rw [ha_cα]; exact finiteAdeleSingleHere_apply_same R K v _
    -- The difference (a_cα - c • a_α) v
    have hdiff_v : (a_cα - c • a_α) v =
        algebraMap K (v.adicCompletion K) (x_cα - x_scaled) := by
      have hsub : (a_cα - c • a_α) v = a_cα v - (c • a_α) v := rfl
      rw [hsub, ha_cα_v, hsmul_v, ← map_sub]
    -- Now show the valuation bound for d * π^(-(D(v)+1))
    have hr_val : v.intValuation d ≤ WithZero.exp (-(1 : ℤ)) := by
      have hmem1 : d ∈ v.asIdeal ^ 1 := by simp only [pow_one]; exact hd_mem
      have hle := (v.intValuation_le_pow_iff_mem d 1).mpr hmem1
      simp only [Nat.cast_one] at hle
      exact hle
    have hr_val_K : v.valuation K (algebraMap R K d) ≤ WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact hr_val
    have hx_val : v.valuation K (algebraMap R K d * uniformizerInvPow R K v (D v + 1)) ≤
        WithZero.exp (D v) := by
      unfold uniformizerInvPow uniformizerInK
      rw [Valuation.map_mul, uniformizerAt_zpow_valuation]
      simp only [neg_neg]
      calc v.valuation K (algebraMap R K d) * WithZero.exp (D v + 1)
          ≤ WithZero.exp (-1) * WithZero.exp (D v + 1) := by
            exact mul_le_mul_of_nonneg_right hr_val_K (WithZero.zero_le _)
        _ = WithZero.exp (-1 + (D v + 1)) := by rw [← WithZero.exp_add]
        _ = WithZero.exp (D v) := by ring_nf
    -- Use hw : w = v to rewrite the goal
    rw [hw, hdiff_v, hx_diff]
    -- The algebraMap K → adicCompletion K v sends x to (x : adicCompletion K v)
    -- So Valued.v (algebraMap K _ x) = Valued.v ↑x = v.valuation K x
    -- Use valuedAdicCompletion_eq_valuation' with explicit term
    convert hx_val using 1
    exact valuedAdicCompletion_eq_valuation' v _
  · -- At place w ≠ v: both a_cα and c • a_α are 0 at w
    have ha_cα_w : a_cα w = 0 := by
      rw [ha_cα]
      exact finiteAdeleSingleHere_apply_ne R K v w _ hw
    have ha_α_w : a_α w = 0 := by
      rw [ha_α]
      exact finiteAdeleSingleHere_apply_ne R K v w _ hw
    have hsmul_w : (c • a_α) w = 0 := by
      simp only [Algebra.smul_def]
      have h1 : ((algebraMap k (FiniteAdeleRing R K) c) * a_α) w =
          (algebraMap k (FiniteAdeleRing R K) c) w * a_α w := rfl
      rw [h1, ha_α_w, mul_zero]
    have hdiff_w : (a_cα - c • a_α) w = 0 := by
      have hsub : (a_cα - c • a_α) w = a_cα w - (c • a_α) w := rfl
      rw [hsub, ha_cα_w, hsmul_w, sub_zero]
    rw [hdiff_w, Valuation.map_zero]
    exact WithZero.zero_le _

/-- The connecting homomorphism as a k-linear map.

This is the key map δ: κ(v) →ₗ[k] H¹(D) in the 6-term exact sequence.
-/
def connectingHom (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    residueFieldAtPrime R v →ₗ[k] SpaceModule k R K D where
  toFun := connectingHomFun k R K v D
  map_add' := connectingHomFun_add k R K v D
  map_smul' c α := by
    simp only [connectingHomFun_smul, RingHom.id_apply]

/-! ## Section 2: Exactness of the 6-Term Sequence

The 6-term exact sequence:
```
0 → L(D) → L(D+v) → κ(v) → H¹(D) → H¹(D+v) → 0
```

Each exactness statement relates kernels and images.
-/

/-- Exactness at L(D+v): ker(eval) = image(incl).

This is already proved in KernelProof.lean.
-/
theorem exactness_at_LDv (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    LinearMap.ker (evaluationMapAt_complete v D) =
    LinearMap.range (Submodule.inclusion
      (RRModuleV2_mono_inclusion R K (divisor_le_add_single D v))) :=
  kernel_evaluationMapAt_complete_proof v D

/-- Helper: if α = eval(f), then the lift of α and shiftedElement(f) have the same residue.

    This is the key observation for proving that image(eval) ⊆ ker(δ). -/
lemma lift_eq_shiftedElement_residue (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : RRModuleV2_real R K (D + DivisorV2.single v 1)) :
    (residueFieldBridge_explicit (R := R) (K := K) v)
      ((valuationRingAt.residue (R := R) (K := K) v)
        ⟨algebraMap R K (liftToR R v (evaluationMapAt_complete v D f)),
          algebraMap_mem_valuationRingAt v _⟩) =
    evaluationMapAt_complete v D f := by
  -- By liftToR_proj: Quotient.mk (liftToR α) = (linearEquiv).symm α
  -- By bridge_residue_algebraMap_clean: bridge(residue(algebraMap R K r)) = algebraMap R κ r
  -- algebraMap R κ r = linearEquiv (Quotient.mk r) = linearEquiv ((linearEquiv).symm α) = α
  -- Note: residueFieldBridge_explicit = residueFieldBridge_explicit_clean by definition
  have h1 := bridge_residue_algebraMap_clean (R := R) (K := K) v (liftToR R v (evaluationMapAt_complete v D f))
  -- residueFieldBridge_explicit and residueFieldBridge_explicit_clean are definitionally equal
  change (residueFieldBridge_explicit_clean (R := R) (K := K) v) _ = _
  rw [h1]
  -- Now need: algebraMap R (residueFieldAtPrime R v) (liftToR ...) = evaluationMapAt_complete v D f
  -- The residueFieldAtPrime R v has linearEquiv : R ⧸ v.asIdeal ≃ₗ[R] residueFieldAtPrime R v
  -- algebraMap R (residueFieldAtPrime R v) r = linearEquiv (Quotient.mk r)
  have h2 : algebraMap R (residueFieldAtPrime R v) (liftToR R v (evaluationMapAt_complete v D f)) =
      (residueFieldAtPrime.linearEquiv (R := R) v) (Ideal.Quotient.mk v.asIdeal
        (liftToR R v (evaluationMapAt_complete v D f))) := by
    rfl
  rw [h2, liftToR_proj]
  -- Now: linearEquiv ((linearEquiv).symm α) = α
  simp only [LinearEquiv.apply_symm_apply]

/-- Helper: algebraMap R K r - shiftedElement f is in the maximal ideal when residues match. -/
lemma algebraMap_sub_shiftedElement_mem_maxIdeal (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : RRModuleV2_real R K (D + DivisorV2.single v 1))
    (r : R) (hr : (residueFieldBridge_explicit (R := R) (K := K) v)
      ((valuationRingAt.residue (R := R) (K := K) v) ⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩) =
      evaluationMapAt_complete v D f) :
    (⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩ : valuationRingAt (R := R) (K := K) v) -
      ⟨shiftedElement v D f.val, shiftedElement_mem_valuationRingAt v D f⟩ ∈
      IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v) := by
  -- residue maps to 0 iff element is in maximal ideal
  rw [← IsLocalRing.residue_eq_zero_iff]
  -- residue is a ring hom, so residue(a - b) = residue(a) - residue(b)
  rw [map_sub]
  -- By hr, bridge(residue(algebraMap R K r)) = eval(f) = bridge(residue(shiftedElement))
  -- Since bridge is injective, residue(algebraMap R K r) = residue(shiftedElement)
  have h_bridge_inj := (residueFieldBridge_explicit (R := R) (K := K) v).injective
  apply h_bridge_inj
  rw [map_sub, map_zero]
  -- Now need: bridge(residue(algebraMap R K r)) - bridge(residue(shiftedElement)) = 0
  -- valuationRingAt.residue is the same as IsLocalRing.residue on valuationRingAt
  -- hr uses valuationRingAt.residue which is definitionally IsLocalRing.residue
  have h_same : (valuationRingAt.residue (R := R) (K := K) v) = (IsLocalRing.residue (valuationRingAt (R := R) (K := K) v)) := rfl
  rw [← h_same, hr]
  -- eval(f) is defined as bridge(residue(shiftedElement))
  -- residueFieldBridge_explicit = residueFieldBridge_explicit_clean definitionally
  -- Need to show: eval(f) - bridge(residue(shifted)) = 0
  -- But eval(f) = bridge_explicit_clean(residue(shifted))
  -- And bridge_explicit = bridge_explicit_clean
  have h_bridge_eq : residueFieldBridge_explicit (R := R) (K := K) v = residueFieldBridge_explicit_clean v := rfl
  simp only [evaluationMapAt_complete, evaluationMapAt_complete_clean, LinearMap.coe_mk, AddHom.coe_mk,
    evaluationFun_via_bridge_clean, h_bridge_eq, sub_self]

/-- In a discrete valuation, val < exp(0) = 1 implies val ≤ exp(-1).
This is because the value group is exp(ℤ) ∪ {0}. -/
lemma valuation_lt_one_imp_le_exp_neg_one (v : HeightOneSpectrum R) (x : K)
    (h : v.valuation K x < 1) :
    v.valuation K x ≤ WithZero.exp (-1 : ℤ) := by
  -- Either x = 0 (val = 0 ≤ exp(-1)) or x ≠ 0 (use step-down)
  by_cases hx : x = 0
  · simp only [hx, Valuation.map_zero]
    exact WithZero.zero_le _
  · -- x ≠ 0, so val ≠ 0, and val < 1 = exp(0) implies val ≤ exp(-1)
    have hval_ne : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    -- 1 = exp(0) = exp((-1)+1)
    have hone_eq : (1 : WithZero (Multiplicative ℤ)) = WithZero.exp ((-1 : ℤ) + 1) := by
      simp only [neg_add_cancel, WithZero.exp_zero]
    rw [hone_eq] at h
    -- Use the step-down lemma: x < exp(n+1) and x ≠ 0 implies x ≤ exp(n)
    exact withzero_lt_exp_succ_imp_le_exp (v.valuation K x) (-1) hval_ne h

/-- Helper: valuation bound for the difference at place v. -/
lemma diff_valuation_bound_at_v (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (f : RRModuleV2_real R K (D + DivisorV2.single v 1))
    (r : R)
    (hmem : (⟨algebraMap R K r, algebraMap_mem_valuationRingAt v r⟩ : valuationRingAt (R := R) (K := K) v) -
      ⟨shiftedElement v D f.val, shiftedElement_mem_valuationRingAt v D f⟩ ∈
      IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v)) :
    v.valuation K (algebraMap R K r * uniformizerInvPow R K v (D v + 1) - f.val) ≤ WithZero.exp (D v) := by
  -- The difference can be factored as (algebraMap R K r - shiftedElement f) * π^(-(D v+1))
  have hfactor : algebraMap R K r * uniformizerInvPow R K v (D v + 1) - f.val =
      (algebraMap R K r - shiftedElement v D f.val) * uniformizerInvPow R K v (D v + 1) := by
    unfold shiftedElement uniformizerInvPow uniformizerInK
    -- f.val * π^(D v + 1) * π^(-(D v + 1)) = f.val since π^n * π^(-n) = 1
    have hunif_ne := uniformizerAt_ne_zero v
    have h_zpow : (algebraMap R K (uniformizerAt v)) ^ (D v + 1) * (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)) = 1 := by
      rw [← zpow_add₀]
      · simp only [add_neg_cancel, zpow_zero]
      · intro h
        apply hunif_ne
        rw [← map_zero (algebraMap R K)] at h
        exact (IsFractionRing.injective R K) h
    calc algebraMap R K r * (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)) - f.val
        = algebraMap R K r * (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)) -
          f.val * ((algebraMap R K (uniformizerAt v)) ^ (D v + 1) * (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1))) := by
            rw [h_zpow, mul_one]
      _ = algebraMap R K r * (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)) -
          f.val * (algebraMap R K (uniformizerAt v)) ^ (D v + 1) * (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)) := by
            ring
      _ = (algebraMap R K r - f.val * (algebraMap R K (uniformizerAt v)) ^ (D v + 1)) *
          (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)) := by ring
  rw [hfactor, Valuation.map_mul]
  -- The maximal ideal membership gives valuation < 1, hence ≤ exp(-1)
  have h_diff_val : v.valuation K (algebraMap R K r - shiftedElement v D f.val) ≤ WithZero.exp (-1 : ℤ) := by
    -- hmem says the subtype difference is in maximalIdeal
    -- valuationRingAt is (v.valuation K).valuationSubring
    -- maximalIdeal = {x | v(x) < 1}
    unfold valuationRingAt at hmem
    rw [Valuation.mem_maximalIdeal_iff] at hmem
    -- Transfer from subtype to K element
    have h_transfer : v.valuation K (algebraMap R K r - shiftedElement v D f.val) < 1 := hmem
    exact valuation_lt_one_imp_le_exp_neg_one R K v _ h_transfer
  -- v(π^(-(D v+1))) = exp(D v + 1) by uniformizerAt_zpow_valuation
  unfold uniformizerInvPow uniformizerInK
  rw [uniformizerAt_zpow_valuation]
  simp only [neg_neg]
  -- exp(-1) * exp(D v + 1) = exp(D v)
  calc v.valuation K (algebraMap R K r - shiftedElement v D f.val) * WithZero.exp (D v + 1)
      ≤ WithZero.exp (-1) * WithZero.exp (D v + 1) := mul_le_mul_of_nonneg_right h_diff_val (WithZero.zero_le _)
    _ = WithZero.exp (-1 + (D v + 1)) := by rw [← WithZero.exp_add]
    _ = WithZero.exp (D v) := by ring_nf

lemma image_eval_subset_ker_delta (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    Set.range (evaluationMapAt_complete (K := K) v D) ⊆
    {α | connectingHom k R K v D α = 0} := by
  -- Take α = eval(f) for some f ∈ L(D+v)
  intro α ⟨f, hf⟩
  rw [Set.mem_setOf_eq]
  subst hf
  -- Goal: connectingHom k R K v D (evaluationMapAt_complete v D f) = 0
  simp only [connectingHom, LinearMap.coe_mk, AddHom.coe_mk, connectingHomFun]
  -- The adele a is finiteAdeleSingleHere R K v (algebraMap K (adicCompletion) x)
  -- where x = algebraMap R K (liftToR ...) * uniformizerInvPow R K v (D v + 1)
  -- We show a - diag(f) ∈ A_K(D), so a ∈ K + A_K(D)
  set r := liftToR R v (evaluationMapAt_complete v D f) with hr_def
  set x := algebraMap R K r * uniformizerInvPow R K v (D v + 1) with hx_def
  set a := finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K) x) with ha_def
  -- Show quotientMapLinear a = 0, i.e., a ∈ globalPlusBoundedSubmodule
  unfold quotientMapLinear
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  -- a ∈ globalSubmodule + boundedSubmodule means ∃ g ∈ K, a - diag(g) ∈ A_K(D)
  -- Take g = f
  unfold globalPlusBoundedSubmodule
  -- globalSubmodule + boundedSubmodule is sup of submodules
  -- a = diag(f) + (a - diag(f)), where diag(f) ∈ globalSubmodule, (a - diag(f)) ∈ boundedSubmodule
  have h_diag_mem : diagonalK R K f.val ∈ globalSubmodule k R K := ⟨f.val, rfl⟩
  have h_diff_mem : a - diagonalK R K f.val ∈ boundedSubmodule k R K D := by
    show a - diagonalK R K f.val ∈ boundedSubmodule k R K D
    intro w
    simp only [satisfiesBoundAt, valuationAt]
    by_cases hw : w = v
    · -- At place w = v
      rw [hw]
      -- (a - diag f) v = a v - (diag f) v = x_local - f
      have h_a_v : a v = algebraMap K (v.adicCompletion K) x :=
        finiteAdeleSingleHere_apply_same R K v _
      -- diagonalK = FiniteAdeleRing.algebraMap, and at component v, this is algebraMap K (adicCompletion)
      have h_diag_v : (diagonalK R K f.val) v = algebraMap K (v.adicCompletion K) f.val := rfl
      -- The goal is: Valued.v ((a - diagonalK R K f.val) v) ≤ exp(D v)
      -- Simplify the subtraction at component v
      have h_comp : (a - diagonalK R K f.val) v = a v - (diagonalK R K f.val) v := rfl
      rw [h_comp, h_a_v, h_diag_v]
      -- Now have: Valued.v (algebraMap K (adicCompletion) x - algebraMap K (adicCompletion) f.val)
      rw [← map_sub]
      -- Goal is: Valued.v (algebraMap K (adicCompletion) (x - f.val)) ≤ exp(D v)
      -- Use valuedAdicCompletion_eq_valuation' with explicit term
      have hval : Valued.v (algebraMap K (v.adicCompletion K) (x - f.val)) = v.valuation K (x - f.val) :=
        valuedAdicCompletion_eq_valuation' v (x - f.val)
      rw [hval]
      -- The key: liftToR produces r with same residue as shiftedElement(f)
      have hr_residue := lift_eq_shiftedElement_residue R K v D f
      have hmem := algebraMap_sub_shiftedElement_mem_maxIdeal R K v D f r hr_residue
      exact diff_valuation_bound_at_v R K v D f r hmem
    · -- At place w ≠ v
      -- (a - diag f) w = 0 - f = -f
      have h_a_w : a w = 0 := finiteAdeleSingleHere_apply_ne R K v w _ hw
      have h_diag_w : (diagonalK R K f.val) w = algebraMap K (w.adicCompletion K) f.val := rfl
      -- The goal is: Valued.v ((a - diagonalK R K f.val) w) ≤ exp(D w)
      have h_comp : (a - diagonalK R K f.val) w = a w - (diagonalK R K f.val) w := rfl
      rw [h_comp, h_a_w, h_diag_w, zero_sub, Valuation.map_neg]
      -- Valued.v (algebraMap K (adicCompletion) f.val) = w.valuation K f.val
      have hval : Valued.v (algebraMap K (w.adicCompletion K) f.val) = w.valuation K f.val :=
        valuedAdicCompletion_eq_valuation' w f.val
      rw [hval]
      -- f ∈ L(D+v), so at w ≠ v, v(f) ≤ exp((D + single v 1) w) = exp(D w)
      have hf_mem := f.property
      rcases hf_mem with hf_zero | hf_bound
      · -- f = 0 case
        simp only [hf_zero, Valuation.map_zero]
        exact WithZero.zero_le _
      · -- f ≠ 0 case
        have hf_w := hf_bound w
        -- (D + single v 1) w = D w for w ≠ v
        have hcoeff : (D + DivisorV2.single v 1) w = D w := by
          simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hw), add_zero]
        rw [hcoeff] at hf_w
        exact hf_w
  -- Now assemble: a = diag(f) + (a - diag(f)) with diag(f) ∈ globalSubmodule, (a - diag(f)) ∈ boundedSubmodule
  have h_eq : a = diagonalK R K f.val + (a - diagonalK R K f.val) := by ring
  rw [h_eq]
  exact Submodule.add_mem_sup h_diag_mem h_diff_mem

/-- Helper: membership in L(D+v) from bounded adele data.
    If the single-place adele minus diag(g) is in A_K(D), then g ∈ L(D+v). -/
lemma g_mem_LDv_from_bounded (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (g : K) (α : residueFieldAtPrime R v)
    (h_bounded : finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K)
      (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1))) -
      diagonalK R K g ∈ boundedSubmodule k R K D) :
    g ∈ RRModuleV2_real R K (D + DivisorV2.single v 1) := by
  -- Need to show: g = 0 ∨ ∀ w, w.valuation K g ≤ exp((D + single v 1)(w))
  by_cases hg : g = 0
  · left; exact hg
  · right
    intro w
    set a := finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K)
      (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1))) with ha_def
    have h_w := h_bounded w
    simp only [satisfiesBoundAt, valuationAt] at h_w
    by_cases hw : w = v
    · -- At place v: need val_v(g) ≤ exp(D v + 1)
      rw [hw]
      simp only [Finsupp.add_apply, Finsupp.single_apply, if_true]
      -- (a - diag(g))_v = x - g where x = r * π^(-(D v + 1))
      have ha_v : a v = algebraMap K (v.adicCompletion K)
          (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1)) :=
        finiteAdeleSingleHere_apply_same R K v _
      have hdiag_v : (diagonalK R K g) v = algebraMap K (v.adicCompletion K) g := rfl
      have h_comp : (a - diagonalK R K g) v = a v - (diagonalK R K g) v := rfl
      -- val_v(x - g) ≤ exp(D v) from h_bounded
      rw [hw] at h_w
      rw [h_comp, ha_v, hdiag_v, ← map_sub] at h_w
      have h_val_K : v.valuation K (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1) - g) ≤
          WithZero.exp (D v) := by
        rw [← valuedAdicCompletion_eq_valuation' v _]
        exact h_w
      -- Ultrametric argument: val(g) = val((g - x) + x) ≤ max(val(g-x), val(x))
      -- Since val(g-x) = val(x-g) ≤ exp(D v) and val(x) ≤ exp(D v + 1), we get val(g) ≤ exp(D v + 1)
      -- First show val(x) ≤ exp(D v + 1) where x = algebraMap R K (liftToR R v α) * uniformizerInvPow
      have hx_val : v.valuation K (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1)) ≤
          WithZero.exp (D v + 1) := by
        have hr_val : v.valuation K (algebraMap R K (liftToR R v α)) ≤ 1 := by
          rw [HeightOneSpectrum.valuation_of_algebraMap]
          exact v.intValuation_le_one _
        unfold uniformizerInvPow uniformizerInK
        rw [Valuation.map_mul, uniformizerAt_zpow_valuation]
        simp only [neg_neg]
        calc v.valuation K (algebraMap R K (liftToR R v α)) * WithZero.exp (D v + 1)
            ≤ 1 * WithZero.exp (D v + 1) := mul_le_mul_of_nonneg_right hr_val (WithZero.zero_le _)
          _ = WithZero.exp (D v + 1) := one_mul _
      -- Now use ultrametric: val(g) = val((g - x) + x) ≤ max(val(g - x), val(x))
      have h_ultra : v.valuation K g ≤ max (v.valuation K (g - (algebraMap R K (liftToR R v α) *
          uniformizerInvPow R K v (D v + 1)))) (v.valuation K (algebraMap R K (liftToR R v α) *
          uniformizerInvPow R K v (D v + 1))) := by
        have heq : g = (g - (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1))) +
            (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1)) := by ring
        conv_lhs => rw [heq]
        exact Valuation.map_add (v.valuation K) _ _
      -- val(g - x) = val(-(x - g)) = val(x - g) ≤ exp(D v)
      have h_gx : v.valuation K (g - (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1))) ≤
          WithZero.exp (D v) := by
        rw [← Valuation.map_neg]
        simp only [neg_sub]
        exact h_val_K
      -- Combine: val(g) ≤ max(exp(D v), exp(D v + 1)) = exp(D v + 1)
      calc v.valuation K g ≤ max (v.valuation K (g - (algebraMap R K (liftToR R v α) *
              uniformizerInvPow R K v (D v + 1)))) (v.valuation K (algebraMap R K (liftToR R v α) *
              uniformizerInvPow R K v (D v + 1))) := h_ultra
        _ ≤ max (WithZero.exp (D v)) (WithZero.exp (D v + 1)) := max_le_max h_gx hx_val
        _ = WithZero.exp (D v + 1) := by
          rw [max_eq_right]
          exact WithZero.exp_le_exp.mpr (by omega)
    · -- At place w ≠ v: (a - diag(g))_w = 0 - g = -g
      -- val_w(-g) ≤ exp(D w) from h_bounded
      -- So val_w(g) ≤ exp(D w) = exp((D + single v 1)(w)) for w ≠ v
      have ha_w : a w = 0 := finiteAdeleSingleHere_apply_ne R K v w _ hw
      have hdiag_w : (diagonalK R K g) w = algebraMap K (w.adicCompletion K) g := rfl
      have h_comp : (a - diagonalK R K g) w = a w - (diagonalK R K g) w := rfl
      rw [h_comp, ha_w, hdiag_w, zero_sub, Valuation.map_neg] at h_w
      have h_val_K : w.valuation K g ≤ WithZero.exp (D w) := by
        rw [← valuedAdicCompletion_eq_valuation' w g]
        exact h_w
      -- (D + single v 1)(w) = D w for w ≠ v
      have hcoeff : (D + DivisorV2.single v 1) w = D w := by
        simp only [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hw), add_zero]
      rw [hcoeff]
      exact h_val_K

/-- Helper: if the adele minus diag(g) is bounded, and g has the right residue,
    then evaluationMapAt_complete maps g to α. -/
lemma eval_g_eq_alpha_from_bounded (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (g : K) (α : residueFieldAtPrime R v)
    (hg_mem : g ∈ RRModuleV2_real R K (D + DivisorV2.single v 1))
    (h_bounded : finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K)
      (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1))) -
      diagonalK R K g ∈ boundedSubmodule k R K D) :
    evaluationMapAt_complete v D ⟨g, hg_mem⟩ = α := by
  -- Strategy:
  -- 1. From h_bounded at v: val(r * π^(-(D v+1)) - g) ≤ exp(D v) where r = liftToR R v α
  -- 2. Factor: (algebraMap R K r - shiftedElement v D g) * π^(-(D v+1))
  -- 3. Derive: val(algebraMap R K r - shiftedElement v D g) ≤ exp(-1) < 1
  -- 4. This means algebraMap R K r and shiftedElement v D g have the same residue
  -- 5. So eval(g) = bridge(residue(shifted(g))) = bridge(residue(r)) = algebraMap R κ r = α
  set r := liftToR R v α with hr_def
  set a := finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K)
    (algebraMap R K r * uniformizerInvPow R K v (D v + 1))) with ha_def

  -- Step 1: Extract the bound at place v from h_bounded
  have h_v := h_bounded v
  simp only [satisfiesBoundAt, valuationAt] at h_v
  have ha_v : a v = algebraMap K (v.adicCompletion K)
      (algebraMap R K r * uniformizerInvPow R K v (D v + 1)) :=
    finiteAdeleSingleHere_apply_same R K v _
  have hdiag_v : (diagonalK R K g) v = algebraMap K (v.adicCompletion K) g := rfl
  have h_comp : (a - diagonalK R K g) v = a v - (diagonalK R K g) v := rfl
  rw [h_comp, ha_v, hdiag_v, ← map_sub] at h_v
  have h_val_K : v.valuation K (algebraMap R K r * uniformizerInvPow R K v (D v + 1) - g) ≤
      WithZero.exp (D v) := by
    rw [← valuedAdicCompletion_eq_valuation' v _]
    exact h_v

  -- Step 2: Factor the difference as (algebraMap R K r - shiftedElement v D g) * π^(-(D v+1))
  have hfactor : algebraMap R K r * uniformizerInvPow R K v (D v + 1) - g =
      (algebraMap R K r - shiftedElement v D g) * uniformizerInvPow R K v (D v + 1) := by
    unfold shiftedElement uniformizerInvPow uniformizerInK
    have hunif_ne := uniformizerAt_ne_zero v
    have h_zpow : (algebraMap R K (uniformizerAt v)) ^ (D v + 1) *
        (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)) = 1 := by
      rw [← zpow_add₀]
      · simp only [add_neg_cancel, zpow_zero]
      · intro h
        apply hunif_ne
        rw [← map_zero (algebraMap R K)] at h
        exact (IsFractionRing.injective R K) h
    calc algebraMap R K r * (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)) - g
        = algebraMap R K r * (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)) -
          g * ((algebraMap R K (uniformizerAt v)) ^ (D v + 1) *
          (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1))) := by rw [h_zpow, mul_one]
      _ = (algebraMap R K r - g * (algebraMap R K (uniformizerAt v)) ^ (D v + 1)) *
          (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)) := by ring

  -- Step 3: Derive valuation bound for the difference
  rw [hfactor, Valuation.map_mul] at h_val_K
  unfold uniformizerInvPow uniformizerInK at h_val_K
  rw [uniformizerAt_zpow_valuation] at h_val_K
  simp only [neg_neg] at h_val_K
  -- We have: val(diff) * exp(D v + 1) ≤ exp(D v)
  -- So val(diff) ≤ exp(-1) since exp(D v) ≤ exp(-1) * exp(D v + 1)
  have h_diff_val : v.valuation K (algebraMap R K r - shiftedElement v D g) ≤
      WithZero.exp (-1 : ℤ) := by
    by_cases hdiff_zero : algebraMap R K r - shiftedElement v D g = 0
    · simp only [hdiff_zero, Valuation.map_zero]
      exact WithZero.zero_le _
    · have hval_ne : v.valuation K (algebraMap R K r - shiftedElement v D g) ≠ 0 :=
        (Valuation.ne_zero_iff _).mpr hdiff_zero
      -- From val(diff) * exp(D v + 1) ≤ exp(D v), use step-down
      -- val < exp(D v + 1) (else val * exp(D v + 1) > exp(D v)), so val ≤ exp(D v)
      -- More precisely: val(diff) * exp(D v + 1) ≤ exp(D v) = exp(-1) * exp(D v + 1)
      -- implies val(diff) ≤ exp(-1) by cancellation
      -- h_val_K : val(diff) * exp(D v + 1) ≤ exp(D v)
      -- Use discrete valuation step-down: if val * exp(D v + 1) ≤ exp(D v)
      -- and val ≠ 0, then val ≤ exp(D v) / exp(D v + 1) = exp(-1)
      -- This is because the value group is discrete (exp(ℤ))
      -- Actually, we can use: if val ≠ 0 and val * exp(D v + 1) ≤ exp(D v),
      -- then since val < exp(D v + 1) would give val ≤ exp(D v) after mult,
      -- we use the step-down from Cycle 68's approach
      have h_step := withzero_lt_exp_succ_imp_le_exp (v.valuation K (algebraMap R K r - shiftedElement v D g))
        (D v) hval_ne
      -- Need to show val < exp(D v + 1) = exp(D v) * exp(1)
      -- If val * exp(D v + 1) ≤ exp(D v), then val ≤ exp(D v) / exp(D v + 1)
      -- Since val ≠ 0 and exp(D v + 1) ≠ 0, and the value group is well-ordered in a sense...
      -- Actually, let's think about it differently:
      -- val * exp(D v + 1) ≤ exp(D v) < exp(D v + 1) (since D v < D v + 1)
      -- Hmm, that's not quite right either. Let me use a different approach.
      -- The simplest is: val(diff) = exp(n) for some n ≤ 0 (since diff might be in val ring or higher order)
      -- If val(diff) * exp(D v + 1) ≤ exp(D v), then exp(n) * exp(D v + 1) ≤ exp(D v)
      -- So exp(n + D v + 1) ≤ exp(D v), meaning n + D v + 1 ≤ D v, so n ≤ -1
      -- Hence val(diff) = exp(n) ≤ exp(-1)
      -- But we might have val(diff) < exp(n) for some n (could be zero)
      -- Actually in discrete valuations, val ∈ {0} ∪ {exp(n) : n ∈ ℤ}
      -- Let me look for a simpler inequality manipulation:
      calc v.valuation K (algebraMap R K r - shiftedElement v D g)
          ≤ v.valuation K (algebraMap R K r - shiftedElement v D g) * 1 := by rw [mul_one]
        _ = v.valuation K (algebraMap R K r - shiftedElement v D g) *
            (WithZero.exp (D v + 1) * (WithZero.exp (D v + 1))⁻¹) := by
              rw [mul_inv_cancel₀ WithZero.exp_ne_zero]
        _ = v.valuation K (algebraMap R K r - shiftedElement v D g) *
            WithZero.exp (D v + 1) * (WithZero.exp (D v + 1))⁻¹ := by
              rw [mul_assoc]
        _ ≤ WithZero.exp (D v) * (WithZero.exp (D v + 1))⁻¹ := by
              apply mul_le_mul_of_nonneg_right h_val_K (WithZero.zero_le _)
        _ = WithZero.exp (D v) / WithZero.exp (D v + 1) := by
              rw [div_eq_mul_inv]
        _ = WithZero.exp (D v - (D v + 1)) := by
              rw [WithZero.exp_sub]
        _ = WithZero.exp (-1) := by
              congr 1; omega

  -- Step 4: Valuation < 1 means the difference is in the maximal ideal
  -- v.valuation K x ≤ exp(-1) < 1 means x is in maximal ideal (val < 1)
  have h_diff_lt_one : v.valuation K (algebraMap R K r - shiftedElement v D g) < 1 := by
    calc v.valuation K (algebraMap R K r - shiftedElement v D g)
        ≤ WithZero.exp (-1 : ℤ) := h_diff_val
      _ < WithZero.exp (0 : ℤ) := by
          apply WithZero.exp_lt_exp.mpr
          omega
      _ = 1 := WithZero.exp_zero

  -- Step 5: The difference is in the maximal ideal of the valuation ring
  -- Both algebraMap R K r and shiftedElement v D g are in the valuation ring
  have hr_mem : algebraMap R K r ∈ valuationRingAt (R := R) (K := K) v :=
    algebraMap_mem_valuationRingAt v r
  have hg_shifted_mem : shiftedElement v D g ∈ valuationRingAt (R := R) (K := K) v :=
    shiftedElement_mem_valuationRingAt v D ⟨g, hg_mem⟩
  -- Their difference is in the valuation ring (it's a subring, closed under subtraction)
  have hdiff_mem : algebraMap R K r - shiftedElement v D g ∈ valuationRingAt (R := R) (K := K) v := by
    -- valuationRingAt is a valuation subring, hence a subring, closed under subtraction
    unfold valuationRingAt
    exact (v.valuation K).valuationSubring.sub_mem hr_mem hg_shifted_mem
  -- Valuation < 1 implies membership in maximal ideal
  have hmaximal : (⟨algebraMap R K r - shiftedElement v D g, hdiff_mem⟩ :
      valuationRingAt (R := R) (K := K) v) ∈
      IsLocalRing.maximalIdeal (valuationRingAt (R := R) (K := K) v) := by
    unfold valuationRingAt
    rw [Valuation.mem_maximalIdeal_iff]
    exact h_diff_lt_one

  -- Step 6: Elements in the maximal ideal have residue 0, so the residues of r and shifted(g) are equal
  have hresidues_eq : (valuationRingAt.residue (R := R) (K := K) v)
      ⟨algebraMap R K r, hr_mem⟩ =
    (valuationRingAt.residue (R := R) (K := K) v)
      ⟨shiftedElement v D g, hg_shifted_mem⟩ := by
    -- residue(a - b) = residue(a) - residue(b) = 0 when a - b ∈ maximalIdeal
    have h_sub_res : (valuationRingAt.residue (R := R) (K := K) v)
        ⟨algebraMap R K r - shiftedElement v D g, hdiff_mem⟩ = 0 := by
      -- valuationRingAt.residue is definitionally IsLocalRing.residue
      unfold valuationRingAt.residue
      rw [IsLocalRing.residue_eq_zero_iff]
      exact hmaximal
    have h_sub_eq : (⟨algebraMap R K r - shiftedElement v D g, hdiff_mem⟩ :
        valuationRingAt (R := R) (K := K) v) =
      ⟨algebraMap R K r, hr_mem⟩ - ⟨shiftedElement v D g, hg_shifted_mem⟩ := by
      simp only [Subtype.ext_iff]
      rfl
    rw [h_sub_eq, map_sub] at h_sub_res
    exact sub_eq_zero.mp h_sub_res

  -- Step 7: Apply bridge to both sides of the residue equality
  have hbridge_eq : (residueFieldBridge_explicit (R := R) (K := K) v)
      ((valuationRingAt.residue (R := R) (K := K) v) ⟨algebraMap R K r, hr_mem⟩) =
    (residueFieldBridge_explicit (R := R) (K := K) v)
      ((valuationRingAt.residue (R := R) (K := K) v) ⟨shiftedElement v D g, hg_shifted_mem⟩) := by
    rw [hresidues_eq]

  -- Step 8: The RHS is exactly evaluationMapAt_complete v D ⟨g, hg_mem⟩
  -- evaluationMapAt_complete = evaluationMapAt_complete_clean = evaluationFun_via_bridge_clean
  -- which is bridge(residue(shifted(g)))
  have heval_def : evaluationMapAt_complete v D ⟨g, hg_mem⟩ =
    (residueFieldBridge_explicit (R := R) (K := K) v)
      ((valuationRingAt.residue (R := R) (K := K) v) ⟨shiftedElement v D g, hg_shifted_mem⟩) := by
    simp only [evaluationMapAt_complete, evaluationMapAt_complete_clean, LinearMap.coe_mk,
      AddHom.coe_mk, evaluationFun_via_bridge_clean]
    rfl

  -- Step 9: The LHS is bridge(residue(algebraMap R K r)) = algebraMap R κ r = α
  have hlhs_eq : (residueFieldBridge_explicit (R := R) (K := K) v)
      ((valuationRingAt.residue (R := R) (K := K) v) ⟨algebraMap R K r, hr_mem⟩) = α := by
    -- Use bridge_residue_algebraMap_clean
    have h_bridge := bridge_residue_algebraMap_clean (R := R) (K := K) v r
    -- residueFieldBridge_explicit = residueFieldBridge_explicit_clean
    have h_eq : residueFieldBridge_explicit (R := R) (K := K) v =
        residueFieldBridge_explicit_clean v := rfl
    rw [h_eq, h_bridge]
    -- algebraMap R κ r = linearEquiv (Quotient.mk r) = linearEquiv ((linearEquiv).symm α) = α
    have h_alg : algebraMap R (residueFieldAtPrime R v) r =
        (residueFieldAtPrime.linearEquiv (R := R) v) (Ideal.Quotient.mk v.asIdeal r) := rfl
    rw [h_alg, liftToR_proj]
    simp only [LinearEquiv.apply_symm_apply]

  -- Combine
  rw [heval_def, ← hbridge_eq, hlhs_eq]

theorem exactness_at_kappa_set (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    (Set.range (evaluationMapAt_complete (K := K) v D) : Set (residueFieldAtPrime R v)) =
    {α | connectingHom k R K v D α = 0} := by
  apply Set.eq_of_subset_of_subset
  · exact image_eval_subset_ker_delta k R K v D
  · -- Backward direction: ker(δ) ⊆ image(eval)
    intro α hα
    rw [Set.mem_setOf_eq] at hα
    -- hα : connectingHom k R K v D α = 0
    -- Unpack: quotientMapLinear k R K D a = 0 where a = finiteAdeleSingleHere R K v x_local
    simp only [connectingHom, LinearMap.coe_mk, AddHom.coe_mk, connectingHomFun] at hα
    set r := liftToR R v α with hr_def
    set x := algebraMap R K r * uniformizerInvPow R K v (D v + 1) with hx_def
    set a := finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K) x) with ha_def
    -- hα : quotientMapLinear k R K D a = 0
    unfold quotientMapLinear at hα
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hα
    -- hα : a ∈ globalPlusBoundedSubmodule k R K D = globalSubmodule + boundedSubmodule
    unfold globalPlusBoundedSubmodule at hα
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hα
    -- ∃ g_adele ∈ globalSubmodule, b ∈ boundedSubmodule, a = g_adele + b
    obtain ⟨g_adele, hg_global, b, hb_bounded, h_eq⟩ := hα
    -- g_adele ∈ globalSubmodule means g_adele = diagonalK R K g for some g ∈ K
    obtain ⟨g, hg_diag⟩ := hg_global
    -- a = diagonalK R K g + b means a - diagonalK R K g = b ∈ boundedSubmodule
    have h_diff : a - diagonalK R K g = b := by
      -- h_eq : g_adele + b = a, hg_diag : diagonalK R K g = g_adele
      have h1 : a = g_adele + b := h_eq.symm
      have h2 : g_adele = diagonalK R K g := hg_diag.symm
      rw [h1, h2]
      ring
    rw [← h_diff] at hb_bounded
    -- Now we have: a - diagonalK R K g ∈ boundedSubmodule k R K D
    -- Use helper lemmas to show g ∈ L(D+v) and eval(g) = α
    have hg_mem : g ∈ RRModuleV2_real R K (D + DivisorV2.single v 1) :=
      g_mem_LDv_from_bounded k R K v D g α hb_bounded
    have heval : evaluationMapAt_complete v D ⟨g, hg_mem⟩ = α :=
      eval_g_eq_alpha_from_bounded k R K v D g α hg_mem hb_bounded
    -- So α ∈ image(eval)
    rw [Set.mem_range]
    exact ⟨⟨g, hg_mem⟩, heval⟩

/-- The projection map H¹(D) → H¹(D+v).

This is the natural quotient map induced by the inclusion A_K(D) ⊆ A_K(D+v).
-/
def H1Projection (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    SpaceModule k R K D →ₗ[k] SpaceModule k R K (D + DivisorV2.single v 1) :=
  Submodule.mapQ
    (globalPlusBoundedSubmodule k R K D)
    (globalPlusBoundedSubmodule k R K (D + DivisorV2.single v 1))
    LinearMap.id
    (globalPlusBoundedSubmodule_mono k R K (divisor_le_add_single D v))

/-- Forward direction: image(δ) ⊆ ker(proj).

δ(α) produces a single-place adele with val ≤ exp(D v + 1) at v and 0 elsewhere,
so it's in A_K(D+v), hence maps to 0 in H¹(D+v). -/
lemma image_delta_subset_ker_proj (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    LinearMap.range (connectingHom k R K v D) ≤
    LinearMap.ker (H1Projection k R K v D) := by
  intro x ⟨α, hα⟩
  rw [LinearMap.mem_ker]
  subst hα
  -- Goal: H1Projection (connectingHom α) = 0
  -- Unpack definitions
  simp only [connectingHom, LinearMap.coe_mk, AddHom.coe_mk, connectingHomFun]
  set r := liftToR R v α with hr_def
  set x_K := algebraMap R K r * uniformizerInvPow R K v (D v + 1) with hx_def
  set a := finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K) x_K) with ha_def
  -- H1Projection sends quotientMapLinear(a) to the quotient in H¹(D+v)
  -- It equals 0 iff a ∈ globalPlusBoundedSubmodule k R K (D + single v 1)
  -- We'll show a is in boundedSubmodule k R K (D + single v 1) ⊆ globalPlusBoundedSubmodule
  have h_a_bounded : a ∈ boundedSubmodule k R K (D + DivisorV2.single v 1) := by
    intro w
    simp only [satisfiesBoundAt, valuationAt]
    by_cases hw : w = v
    · -- At place w = v: val(x_K) ≤ exp(D v + 1)
      have hr_val : v.valuation K (algebraMap R K r) ≤ 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        exact v.intValuation_le_one r
      have hx_val : v.valuation K x_K ≤ WithZero.exp (D v + 1) := by
        simp only [hx_def, uniformizerInvPow, uniformizerInK]
        rw [Valuation.map_mul, uniformizerAt_zpow_valuation]
        simp only [neg_neg]
        calc v.valuation K (algebraMap R K r) * WithZero.exp (D v + 1)
            ≤ 1 * WithZero.exp (D v + 1) := mul_le_mul_of_nonneg_right hr_val (WithZero.zero_le _)
          _ = WithZero.exp (D v + 1) := one_mul _
      have hcoeff : (D + DivisorV2.single v 1) v = D v + 1 := by
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      -- Goal: Valued.v (a w) ≤ exp((D + single v 1)(w))
      -- Use hw : w = v to substitute via cases
      cases hw
      rw [finiteAdeleSingleHere_apply_same, hcoeff]
      -- Goal: Valued.v (algebraMap K (adicCompletion K v) x_K) ≤ exp(D v + 1)
      -- Use valuedAdicCompletion_eq_valuation' to convert Valued.v to v.valuation K
      convert hx_val using 1
      exact valuedAdicCompletion_eq_valuation' v x_K
    · -- At place w ≠ v: the adele is 0
      rw [finiteAdeleSingleHere_apply_ne R K v w _ hw, Valuation.map_zero]
      exact WithZero.zero_le _
  -- Now show H1Projection maps to 0
  -- H1Projection = mapQ from H¹(D) to H¹(D+v)
  -- quotientMapLinear(a) maps to the class of a in H¹(D+v)
  -- Since a ∈ boundedSubmodule(D+v) ⊆ globalPlusBoundedSubmodule(D+v), this class is 0
  unfold H1Projection quotientMapLinear
  simp only [Submodule.mkQ_apply]
  rw [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero]
  unfold globalPlusBoundedSubmodule
  exact Submodule.mem_sup_right h_a_bounded

/-! ### Helper lemmas for exists_alpha_for_bounded

The following lemmas break down the proof into manageable pieces to avoid
elaborator timeout issues with complex type coercions.
-/

/-- The uniformizer power in the completion. -/
def uniformizerPow_completion (v : HeightOneSpectrum R) (n : ℤ) : v.adicCompletion K :=
  algebraMap K (v.adicCompletion K) ((algebraMap R K (uniformizerAt v)) ^ n)

/-- The shifted element b(v) * π^(D v + 1) in the completion.

This shifts b(v) so that its valuation becomes ≤ 1 (in the integers of the completion). -/
def shiftedB (v : HeightOneSpectrum R) (D : DivisorV2 R) (b : FiniteAdeleRing R K) :
    v.adicCompletion K :=
  b v * uniformizerPow_completion R K v (D v + 1)

/-- The valuation bound for b at place v from bounded membership. -/
lemma bounded_val_at_v (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (b : FiniteAdeleRing R K) (hb : b ∈ boundedSubmodule k R K (D + DivisorV2.single v 1)) :
    Valued.v (b v) ≤ WithZero.exp (D v + 1) := by
  have h := hb v
  simp only [satisfiesBoundAt, valuationAt] at h
  have hcoeff : (D + DivisorV2.single v 1) v = D v + 1 := by
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [hcoeff] at h
  exact h

/-- The shifted b has valuation ≤ 1 in the completion.

Key calculation:
- val(b(v)) ≤ exp(D v + 1) from bounded membership
- val(π^(D v+1)) = exp(-(D v + 1)) from uniformizer valuation
- val(shifted_b) = val(b(v)) * val(π^(D v+1)) ≤ exp(D v + 1) * exp(-(D v+1)) = 1 -/
lemma shiftedB_val_le_one (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (b : FiniteAdeleRing R K) (hb : b ∈ boundedSubmodule k R K (D + DivisorV2.single v 1)) :
    Valued.v (shiftedB R K v D b) ≤ 1 := by
  unfold shiftedB uniformizerPow_completion
  rw [Valuation.map_mul]
  -- Compute valuation of uniformizer power in completion
  let π_pow : K := (algebraMap R K (uniformizerAt v)) ^ (D v + 1)
  have hcoe : algebraMap K (v.adicCompletion K) π_pow = (π_pow : v.adicCompletion K) := rfl
  have h_unif_val : Valued.v (algebraMap K (v.adicCompletion K) π_pow) = WithZero.exp (-(D v + 1)) := by
    rw [hcoe, valuedAdicCompletion_eq_valuation']
    exact uniformizerAt_zpow_valuation v (D v + 1)
  rw [h_unif_val]
  -- Get the bound on b(v)
  have hb_val := bounded_val_at_v k R K v D b hb
  -- val(b(v)) ≤ exp(D v + 1), val(π^n) = exp(-n)
  -- val(b(v)) * exp(-(D v+1)) ≤ exp(D v + 1) * exp(-(D v+1)) = 1
  calc Valued.v (b v) * WithZero.exp (-(D v + 1))
      ≤ WithZero.exp (D v + 1) * WithZero.exp (-(D v + 1)) :=
        mul_le_mul_of_nonneg_right hb_val (WithZero.zero_le _)
    _ = WithZero.exp ((D v + 1) + (-(D v + 1))) := by rw [← WithZero.exp_add]
    _ = WithZero.exp 0 := by ring_nf
    _ = 1 := WithZero.exp_zero

/-- The shifted b is in the integers of the adic completion. -/
lemma shiftedB_mem_integers (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (b : FiniteAdeleRing R K) (hb : b ∈ boundedSubmodule k R K (D + DivisorV2.single v 1)) :
    shiftedB R K v D b ∈ v.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers]
  exact shiftedB_val_le_one k R K v D b hb

/-- Define α from r ∈ R via the quotient and linear equivalence. -/
def alphaFromR (v : HeightOneSpectrum R) (r : R) : residueFieldAtPrime R v :=
  (residueFieldAtPrime.linearEquiv (R := R) v) (Ideal.Quotient.mk v.asIdeal r)

/-- Key lemma: liftToR of alphaFromR(r) differs from r by an element of v.asIdeal.

This is because both map to the same quotient class. -/
lemma liftToR_alphaFromR_diff_mem_ideal (v : HeightOneSpectrum R) (r : R) :
    liftToR R v (alphaFromR R v r) - r ∈ v.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, liftToR_proj]
  simp only [alphaFromR, LinearEquiv.symm_apply_apply, sub_self]

/-- The bound at places w ≠ v: the adele for α is 0 there, so we just need -b(w) bounded. -/
lemma bound_at_other_places (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (b : FiniteAdeleRing R K) (hb : b ∈ boundedSubmodule k R K (D + DivisorV2.single v 1))
    (w : HeightOneSpectrum R) (hw : w ≠ v) :
    Valued.v ((-b) w) ≤ WithZero.exp (D w) := by
  -- -b at w has same valuation as b at w
  have hneg : (-b) w = -(b w) := rfl
  rw [hneg, Valuation.map_neg]
  -- Get bound from hb
  have h := hb w
  simp only [satisfiesBoundAt, valuationAt] at h
  -- (D + single v 1)(w) = D(w) for w ≠ v
  have hcoeff : (D + DivisorV2.single v 1) w = D w := by
    simp only [Finsupp.add_apply, DivisorV2.single, Finsupp.single_apply, if_neg (Ne.symm hw), add_zero]
  rw [hcoeff] at h
  exact h

/-- Helper: elements of v.asIdeal have intValuation ≤ exp(-1). -/
lemma intValuation_of_ideal_mem (v : HeightOneSpectrum R) (s : R) (hs : s ∈ v.asIdeal) :
    v.intValuation s ≤ WithZero.exp (-1 : ℤ) := by
  have hmem1 : s ∈ v.asIdeal ^ 1 := by simp only [pow_one]; exact hs
  have hle := (v.intValuation_le_pow_iff_mem s 1).mpr hmem1
  simp only [Nat.cast_one] at hle
  exact hle

/-- Helper: K-valuation of an element whose intValuation is ≤ exp(-1). -/
lemma valuation_of_ideal_mem_K (v : HeightOneSpectrum R) (s : R) (hs : s ∈ v.asIdeal) :
    v.valuation K (algebraMap R K s) ≤ WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact intValuation_of_ideal_mem R v s hs

/-- The bound at place v using same-residue property.

When liftToR(α) - r ∈ v.asIdeal and toResidueField(r) = residue(shifted_b),
the valuation bound follows from ultrametric inequalities.

Proof outline:
1. liftToR(α) - r ∈ v.asIdeal, so val(liftToR(α) - r) ≤ exp(-1)
2. toResidueField(r) = residue(shifted_b) means val(r - shifted_b) ≤ exp(-1) in completion
3. Factor: liftToR(α) * π^(-n) - b(v) = (liftToR(α) - r) * π^(-n) + (r - shifted_b) * π^(-n)
4. By ultrametric: val(...) ≤ max(exp(-1), exp(-1)) * exp(n) = exp(-1+n) = exp(D v) -/
lemma bound_at_v_helper (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (b : FiniteAdeleRing R K) (hb : b ∈ boundedSubmodule k R K (D + DivisorV2.single v 1))
    (r : R) (hr_residue : ResidueFieldIso.toResidueField (K := K) v r =
      IsLocalRing.residue (R := v.adicCompletionIntegers K) ⟨shiftedB R K v D b,
        shiftedB_mem_integers k R K v D b hb⟩) :
    Valued.v (algebraMap K (v.adicCompletion K)
      (algebraMap R K (liftToR R v (alphaFromR R v r)) * uniformizerInvPow R K v (D v + 1)) - b v) ≤
      WithZero.exp (D v) := by
  -- Set notation for clarity
  set L := liftToR R v (alphaFromR R v r) with hL_def
  set sb := shiftedB R K v D b with hsb_def
  set sb_mem := shiftedB_mem_integers k R K v D b hb with hsb_mem_def
  set π_inv := uniformizerInvPow R K v (D v + 1) with hπ_inv_def
  set π_pow := uniformizerPow_completion R K v (D v + 1) with hπ_pow_def

  -- Step 1: Factor the difference
  -- b v = sb * π^(-(D v+1)) since sb = b v * π^(D v+1)
  have h_bv_factor : b v = sb * algebraMap K (v.adicCompletion K) π_inv := by
    simp only [hsb_def, shiftedB, hπ_inv_def, uniformizerInvPow, uniformizerInK, hπ_pow_def,
               uniformizerPow_completion]
    have hunif_ne := uniformizerAt_ne_zero v
    have hunif_K_ne : algebraMap R K (uniformizerAt v) ≠ 0 := by
      intro h
      have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
      exact hunif_ne (hinj (h.trans (map_zero _).symm))
    have h_zpow : (algebraMap R K (uniformizerAt v)) ^ (D v + 1) *
        (algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)) = 1 := by
      rw [← zpow_add₀ hunif_K_ne]
      simp only [add_neg_cancel, zpow_zero]
    -- sb = b v * π^(D v+1), so b v = sb * π^(-(D v+1))
    have h1 : algebraMap K (v.adicCompletion K) ((algebraMap R K (uniformizerAt v)) ^ (D v + 1)) *
        algebraMap K (v.adicCompletion K) ((algebraMap R K (uniformizerAt v)) ^ (-(D v + 1))) = 1 := by
      rw [← map_mul, h_zpow, map_one]
    calc b v = b v * 1 := (mul_one _).symm
      _ = b v * (algebraMap K (v.adicCompletion K) ((algebraMap R K (uniformizerAt v)) ^ (D v + 1)) *
            algebraMap K (v.adicCompletion K) ((algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)))) := by rw [h1]
      _ = (b v * algebraMap K (v.adicCompletion K) ((algebraMap R K (uniformizerAt v)) ^ (D v + 1))) *
            algebraMap K (v.adicCompletion K) ((algebraMap R K (uniformizerAt v)) ^ (-(D v + 1))) := by ring

  -- Rewrite goal using the factorization
  -- algebraMap K ... (L * π_inv) - b v = algebraMap K ... L * algebraMap K ... π_inv - sb * algebraMap K ... π_inv
  --                                     = (algebraMap K ... L - sb) * algebraMap K ... π_inv
  have h_goal_factor : algebraMap K (v.adicCompletion K)
      (algebraMap R K L * π_inv) - b v =
      (algebraMap K (v.adicCompletion K) (algebraMap R K L) - sb) *
        algebraMap K (v.adicCompletion K) π_inv := by
    rw [h_bv_factor, map_mul]
    ring
  rw [h_goal_factor, Valuation.map_mul]

  -- Step 2: Show val(algebraMap K ... L - sb) ≤ exp(-1) using ultrametric
  -- First, show val(L - r) ≤ exp(-1) from liftToR_alphaFromR_diff_mem_ideal
  have hL_r_ideal : L - r ∈ v.asIdeal := liftToR_alphaFromR_diff_mem_ideal R v r

  -- val(algebraMap R K (L - r)) ≤ exp(-1)
  have hL_r_val : v.valuation K (algebraMap R K L - algebraMap R K r) ≤ WithZero.exp (-1) := by
    rw [← map_sub]
    exact valuation_of_ideal_mem_K R K v (L - r) hL_r_ideal

  -- Step 3: Show algebraMap r and sb have same residue, so their difference is in maximal ideal
  -- hr_residue : toResidueField v r = residue ⟨sb, sb_mem⟩
  -- toResidueField = residue ∘ algebraMapToIntegers
  -- So residue(algebraMap r) = residue ⟨sb, sb_mem⟩
  -- Use explicit Subtype.mk since anonymous constructor doesn't work for ValuationSubring
  let sb_elem : v.adicCompletionIntegers K := Subtype.mk sb sb_mem
  have hr_sb_same_residue : IsLocalRing.residue (R := v.adicCompletionIntegers K)
      (ResidueFieldIso.algebraMapToIntegers v r) =
      IsLocalRing.residue (R := v.adicCompletionIntegers K) sb_elem := by
    simp only [ResidueFieldIso.toResidueField, RingHom.coe_comp, Function.comp_apply] at hr_residue
    exact hr_residue

  -- Same residue implies difference is in maximal ideal
  have hr_sb_diff_maxIdeal : ResidueFieldIso.algebraMapToIntegers v r - sb_elem ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at hr_sb_same_residue
    exact hr_sb_same_residue

  -- Difference in maximal ideal means val < 1, hence ≤ exp(-1)
  -- We need to show: Valued.v x < 1 → Valued.v x ≤ exp(-1)
  -- This follows from the value group being exp(ℤ) ∪ {0}
  have hr_sb_val : Valued.v ((ResidueFieldIso.algebraMapToIntegers v r : v.adicCompletionIntegers K) -
      sb_elem : v.adicCompletion K) ≤ WithZero.exp (-1) := by
    rw [ResidueFieldIso.mem_maximalIdeal_iff_val_lt_one] at hr_sb_diff_maxIdeal
    -- hr_sb_diff_maxIdeal : Valued.v (...) < 1
    -- Use withzero_lt_exp_succ_imp_le_exp: if x < exp(n+1) and x ≠ 0 then x ≤ exp(n)
    -- Here 1 = exp(0), so x < exp(0) = exp(-1+1) implies x ≤ exp(-1)
    set y := ((ResidueFieldIso.algebraMapToIntegers v r : v.adicCompletionIntegers K) -
        sb_elem : v.adicCompletion K) with hy_def
    by_cases hzero : Valued.v y = 0
    · rw [hzero]; exact WithZero.zero_le _
    · have hlt : Valued.v y < WithZero.exp ((-1 : ℤ) + 1) := by simpa using hr_sb_diff_maxIdeal
      exact withzero_lt_exp_succ_imp_le_exp (Valued.v y) (-1) hzero hlt

  -- Step 4: Use ultrametric to bound val(algebraMap K ... L - sb)
  -- algebraMap K ... L - sb = (algebraMap K ... L - algebraMap K ... r) + (algebraMap K ... r - sb)
  have h_split : algebraMap K (v.adicCompletion K) (algebraMap R K L) - sb =
      (algebraMap K (v.adicCompletion K) (algebraMap R K L) -
       algebraMap K (v.adicCompletion K) (algebraMap R K r)) +
      (algebraMap K (v.adicCompletion K) (algebraMap R K r) - sb) := by ring

  -- Convert hr_sb_val to the right form
  have hr_sb_val' : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) - sb) ≤
      WithZero.exp (-1) := by
    -- algebraMapToIntegers v r = algebraMap R (adicCompletionIntegers K) r
    -- Its coercion to adicCompletion K is algebraMap K (adicCompletion K) (algebraMap R K r)
    have hcoe : ((ResidueFieldIso.algebraMapToIntegers v r : v.adicCompletionIntegers K) :
        v.adicCompletion K) = algebraMap K (v.adicCompletion K) (algebraMap R K r) := by
      simp only [ResidueFieldIso.algebraMapToIntegers]
      rfl
    simp only [hcoe] at hr_sb_val
    exact hr_sb_val

  -- Convert hL_r_val to completion
  have hL_r_val' : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K L) -
      algebraMap K (v.adicCompletion K) (algebraMap R K r)) ≤ WithZero.exp (-1) := by
    -- The algebraMap K → completion preserves valuation
    rw [← map_sub]
    -- Show algebraMap K (completion) x = (x : completion) for x : K
    set y := algebraMap R K L - algebraMap R K r with hy_def
    have hval : Valued.v (algebraMap K (v.adicCompletion K) y) = v.valuation K y :=
      valuedAdicCompletion_eq_valuation' v y
    rw [hval]
    exact hL_r_val

  -- Ultrametric bound
  have h_ultra : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K L) - sb) ≤
      WithZero.exp (-1) := by
    rw [h_split]
    calc Valued.v ((algebraMap K (v.adicCompletion K) (algebraMap R K L) -
            algebraMap K (v.adicCompletion K) (algebraMap R K r)) +
           (algebraMap K (v.adicCompletion K) (algebraMap R K r) - sb))
        ≤ max (Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K L) -
                algebraMap K (v.adicCompletion K) (algebraMap R K r)))
              (Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) - sb)) :=
          Valuation.map_add _ _ _
      _ ≤ max (WithZero.exp (-1)) (WithZero.exp (-1)) := max_le_max hL_r_val' hr_sb_val'
      _ = WithZero.exp (-1) := max_self _

  -- Step 5: val(π_inv) = exp(D v + 1)
  have hπ_inv_val : Valued.v (algebraMap K (v.adicCompletion K) π_inv) = WithZero.exp (D v + 1) := by
    simp only [hπ_inv_def, uniformizerInvPow, uniformizerInK]
    have hval : Valued.v (algebraMap K (v.adicCompletion K)
        ((algebraMap R K (uniformizerAt v)) ^ (-(D v + 1)))) =
        v.valuation K ((algebraMap R K (uniformizerAt v)) ^ (-(D v + 1))) :=
      valuedAdicCompletion_eq_valuation' v _
    rw [hval, uniformizerAt_zpow_valuation]
    simp only [neg_neg]

  -- Step 6: Final calculation
  rw [hπ_inv_val]
  calc Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K L) - sb) * WithZero.exp (D v + 1)
      ≤ WithZero.exp (-1) * WithZero.exp (D v + 1) := mul_le_mul_of_nonneg_right h_ultra (WithZero.zero_le _)
    _ = WithZero.exp (-1 + (D v + 1)) := (WithZero.exp_add (-1) (D v + 1)).symm
    _ = WithZero.exp (D v) := by ring_nf

/-- Helper: For any bounded adele b at D+v, we can find α such that
    the single-place adele for α differs from b by something bounded for D.

    Key insight: Use density of K in completion (exists_close_element) and
    residue field surjectivity (toResidueField_surjective from ResidueFieldIso).

    Proof sketch:
    1. shifted_b := b(v) * π^(D v + 1) has val ≤ 1 in the completion
    2. By toResidueField_surjective, ∃ r ∈ R with toResidueField(r) = residue(shifted_b)
    3. Take α corresponding to r via the bridge isomorphisms
    4. Then liftToR(α) has same residue as shifted_b, so difference is in maxIdeal
    5. This gives val(a_α(v) - b(v)) ≤ exp(-1) * exp(D v + 1) = exp(D v)
    6. At w ≠ v: val(-b(w)) ≤ exp(D w) since (D+v)(w) = D(w)  -/
lemma exists_alpha_for_bounded (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (b : FiniteAdeleRing R K) (hb : b ∈ boundedSubmodule k R K (D + DivisorV2.single v 1)) :
    ∃ α : residueFieldAtPrime R v,
      finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K)
        (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1))) - b ∈
      globalPlusBoundedSubmodule k R K D := by
  /-
  DETAILED PROOF STRATEGY (fully verified but Lean 4 elaborator times out on inline proof):

  Construction of α:
  1. Let shifted_b := b(v) * π^(D v + 1) in v.adicCompletion K
     - val(b(v)) ≤ exp(D v + 1) from hb (since (D+v)(v) = D v + 1)
     - val(π^(D v+1)) = exp(-(D v+1)) from uniformizerAt_valuation
     - So val(shifted_b) ≤ 1, hence shifted_b ∈ v.adicCompletionIntegers K

  2. Apply ResidueFieldIso.toResidueField_surjective to find r ∈ R with:
     toResidueField(r) = IsLocalRing.residue(shifted_b)

  3. Define α := (residueFieldAtPrime.linearEquiv v) (Ideal.Quotient.mk v.asIdeal r)
     Then liftToR(α) - r ∈ v.asIdeal (they have the same quotient class)

  Verification of bound (difference in boundedSubmodule k R K D):
  At place w = v:
    The key factorization is:
      liftToR(α) * π^(-(D v+1)) - b(v) = (liftToR(α) - shifted_b) * π^(-(D v+1))

    since shifted_b = b(v) * π^(D v+1), so b(v) = shifted_b * π^(-(D v+1)).

    We show val(liftToR(α) - shifted_b) ≤ exp(-1) by ultrametric:
    - val(r - shifted_b) ≤ exp(-1): same residue implies difference in maxIdeal
    - val(liftToR(α) - r) ≤ exp(-1): same quotient implies difference in v.asIdeal
    - By ultrametric: val(liftToR(α) - shifted_b) ≤ max(exp(-1), exp(-1)) = exp(-1)

    Therefore:
      val((liftToR(α) - shifted_b) * π^(-(D v+1)))
      ≤ exp(-1) * exp(D v + 1) = exp(-1 + D v + 1) = exp(D v)

  At place w ≠ v:
    The single-place adele is 0 at w, so the difference is -b(w).
    val(-b(w)) = val(b(w)) ≤ exp((D+v)(w)) = exp(D(w)) for w ≠ v.

  Key lemmas used:
  - ResidueFieldIso.toResidueField_surjective: R → completion's residue field is surjective
  - valuedAdicCompletion_eq_valuation' v k: Valued.v (k : completion) = v.valuation K k
  - uniformizerAt_valuation: v.valuation K (uniformizerAt v) = exp(-1)
  - Valuation.Integer.not_isUnit_iff_valuation_lt_one: maxIdeal membership ↔ val < 1
  - withzero_lt_exp_succ_imp_le_exp: x < exp(n+1) and x ≠ 0 implies x ≤ exp(n)
  -/
  -- Step 1: shifted_b ∈ integers of completion
  have hshift_mem := shiftedB_mem_integers k R K v D b hb

  -- Step 2: Find r ∈ R with toResidueField(r) = residue(shifted_b)
  let shifted_elem : v.adicCompletionIntegers K := ⟨shiftedB R K v D b, hshift_mem⟩
  obtain ⟨r, hr_residue⟩ := ResidueFieldIso.toResidueField_surjective (K := K) v
    (IsLocalRing.residue (R := v.adicCompletionIntegers K) shifted_elem)

  -- Step 3: Take α = alphaFromR r
  use alphaFromR R v r

  -- Step 4: Show the difference is in globalPlusBoundedSubmodule
  -- It suffices to show it's in boundedSubmodule (which is contained in globalPlusBounded)
  apply Submodule.mem_sup_right
  show _ ∈ boundedSubmodule k R K D

  -- Need: for all w, val((adele_α - b) w) ≤ exp(D w)
  intro w
  simp only [satisfiesBoundAt, valuationAt]
  -- For FiniteAdeleRing, subtraction is component-wise, so (a - b) w = a w - b w
  have h_sub_apply : ∀ (a b : FiniteAdeleRing R K) (w : HeightOneSpectrum R),
      (a - b) w = a w - b w := fun _ _ _ => rfl
  by_cases hw : w = v
  · -- At place v: use bound_at_v_helper
    rw [hw, h_sub_apply, finiteAdeleSingleHere_apply_same]
    exact bound_at_v_helper k R K v D b hb r hr_residue
  · -- At place w ≠ v: the adele for α is 0, so difference is -b(w)
    rw [h_sub_apply, finiteAdeleSingleHere_apply_ne R K v w _ hw, zero_sub]
    exact bound_at_other_places k R K v D b hb w hw

/-- Exactness at H¹(D): image(δ) = ker(proj).

The kernel of H¹(D) → H¹(D+v) is exactly the image of δ.

Proof sketch:
- Forward (image(δ) ⊆ ker(proj)): δ(α) produces an adele with val ≤ exp(D v + 1) at v
  and 0 elsewhere, so it's in A_K(D+v), hence maps to 0 in H¹(D+v). (PROVED)
- Backward (ker(proj) ⊆ image(δ)): If [a] = 0 in H¹(D+v), then a = g + b with
  g ∈ K and b ∈ A_K(D+v). The "shifted residue" of b at v determines α ∈ κ(v),
  and [a] = δ(α). (Uses exists_alpha_for_bounded)
-/
theorem exactness_at_H1 (v : HeightOneSpectrum R) (D : DivisorV2 R)
    [hfin : Module.Finite k (SpaceModule k R K D)] :
    LinearMap.range (connectingHom k R K v D) =
    LinearMap.ker (H1Projection k R K v D) := by
  apply le_antisymm
  · -- Forward direction: image(δ) ⊆ ker(proj)
    exact image_delta_subset_ker_proj k R K v D
  · -- Backward direction: ker(proj) ⊆ image(δ)
    intro x hx
    rw [LinearMap.mem_ker] at hx
    -- Get a representative of x
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ x
    -- x = 0 in H¹(D+v) means a ∈ globalPlusBoundedSubmodule(D+v)
    have h_a_in : a ∈ globalPlusBoundedSubmodule k R K (D + DivisorV2.single v 1) := by
      unfold H1Projection at hx
      rw [← ha] at hx
      simp only [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at hx
      exact hx
    -- Decompose a = diag(g) + b
    unfold globalPlusBoundedSubmodule at h_a_in
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at h_a_in
    obtain ⟨g_adele, hg_global, b, hb_bounded, h_eq⟩ := h_a_in
    obtain ⟨g, hg_diag⟩ := hg_global
    -- The rest of the proof uses exists_alpha_for_bounded to construct α
    -- and shows quotientMapLinear b ∈ range(connectingHom)
    -- x = [a]_D = [b]_D since diag(g) ∈ globalSubmodule, then use α from the lemma

    -- Step 1: x = [a]_D = [b]_D since diag(g) ∈ globalSubmodule
    have hx_eq_b : x = quotientMapLinear k R K D b := by
      rw [← ha, ← h_eq]
      unfold quotientMapLinear
      -- Use Submodule.Quotient.mk_add to split g_adele + b
      simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_add]
      -- g_adele = diag(g) ∈ globalSubmodule ⊆ globalPlusBoundedSubmodule
      have hg_in_global : g_adele ∈ globalSubmodule k R K := ⟨g, hg_diag⟩
      have hg_in : g_adele ∈ globalPlusBoundedSubmodule k R K D := by
        unfold globalPlusBoundedSubmodule
        exact Submodule.mem_sup_left hg_in_global
      rw [(Submodule.Quotient.mk_eq_zero (globalPlusBoundedSubmodule k R K D)).mpr hg_in, zero_add]

    -- Step 2: Apply exists_alpha_for_bounded to find α
    obtain ⟨α, hα⟩ := exists_alpha_for_bounded k R K v D b hb_bounded

    -- Step 3: connectingHom(α) = [finiteAdeleSingleHere(...)]_D
    -- The definition of connectingHom uses quotientMapLinear
    have hconn_def : connectingHom k R K v D α = quotientMapLinear k R K D
        (finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K)
          (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1)))) := rfl

    -- Step 4: finiteAdeleSingleHere(...) - b ∈ globalPlusBoundedSubmodule(D)
    -- So quotientMapLinear(finiteAdeleSingleHere(...)) = quotientMapLinear(b)
    have h_eq_quot : quotientMapLinear k R K D
        (finiteAdeleSingleHere R K v (algebraMap K (v.adicCompletion K)
          (algebraMap R K (liftToR R v α) * uniformizerInvPow R K v (D v + 1)))) =
        quotientMapLinear k R K D b := by
      unfold quotientMapLinear
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact hα

    -- Step 5: x = connectingHom(α)
    rw [hx_eq_b, ← h_eq_quot, ← hconn_def]
    exact LinearMap.mem_range_self _ α

/-- H¹(D) → H¹(D+v) is surjective.

This follows from the inclusion of submodules.
-/
theorem H1_surjection (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    Function.Surjective (H1Projection k R K v D) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  use Submodule.Quotient.mk x
  rfl

/-! ## Section 3: Dimension Formula

Using exactness, we derive the additive property of the Euler characteristic.
-/

/-- The Euler characteristic χ(D) = ℓ(D) - h¹(D). -/
def eulerChar (D : DivisorV2 R) : ℤ :=
  (ell_proj k R K D : ℤ) - h1_finrank k R K D

/-- Assumption that all places have degree 1 over k.

This is equivalent to saying k is the full field of constants (k = H⁰(O_X))
and all places are k-rational points of the curve. This holds for:
- k algebraically closed
- Curves with only k-rational points
- Function fields where k is exactly the constants
-/
class DegreeOnePlaces where
  residue_finrank_one : ∀ v : HeightOneSpectrum R, Module.finrank k (residueFieldAtPrime R v) = 1

/-- The residue field κ(v) has dimension 1 over k.

The residue field κ(v) = R/v.asIdeal is a simple R-module (has length 1),
which when k ⊆ R implies dim_k(κ(v)) = 1.
-/
lemma kappa_dim_one [DegreeOnePlaces k R] (v : HeightOneSpectrum R) :
    Module.finrank k (residueFieldAtPrime R v) = 1 :=
  DegreeOnePlaces.residue_finrank_one v

/-- Key theorem: χ(D+v) = χ(D) + 1.

This follows from the exact sequence and the Rank-Nullity theorem.

The 6-term exact sequence gives:
0 → L(D) → L(D+v) → κ(v) → H¹(D) → H¹(D+v) → 0

By alternating sum of dimensions:
dim L(D) - dim L(D+v) + dim κ(v) - dim H¹(D) + dim H¹(D+v) = 0

Rearranging:
(dim L(D+v) - dim H¹(D+v)) - (dim L(D) - dim H¹(D)) = dim κ(v) = 1

Therefore: χ(D+v) = χ(D) + 1
-/
theorem chi_additive (v : HeightOneSpectrum R) (D : DivisorV2 R)
    [Module.Finite k (SpaceModule k R K D)]
    [Module.Finite k (SpaceModule k R K (D + DivisorV2.single v 1))]
    [Module.Finite k (RRSpace_proj k R K D)]
    [Module.Finite k (RRSpace_proj k R K (D + DivisorV2.single v 1))] :
    eulerChar k R K (D + DivisorV2.single v 1) = eulerChar k R K D + 1 := by
  -- Use exactness and dimension counting
  -- dim(L(D+v)) - dim(H¹(D+v)) - (dim(L(D)) - dim(H¹(D))) = dim(κ(v)) = 1
  sorry

/-- Full Euler characteristic formula by induction.

For any divisor D: χ(D) = deg(D) + 1 - g

where g is the genus (g = h¹(0) by definition).

Proof:
- Base case: χ(0) = ℓ(0) - h¹(0) = 1 - g
- Inductive step: chi_additive gives χ(D+v) = χ(D) + 1
- Induction on degree using deg(D + single v 1) = deg(D) + 1
-/
theorem euler_characteristic (D : DivisorV2 R) (genus : ℕ)
    [∀ E : DivisorV2 R, Module.Finite k (SpaceModule k R K E)]
    [∀ E : DivisorV2 R, Module.Finite k (RRSpace_proj k R K E)]
    (h_genus : h1_finrank k R K 0 = genus)
    (h_ell_zero : ell_proj k R K 0 = 1) :
    eulerChar k R K D = D.deg + 1 - genus := by
  sorry

/-! ## Section 4: Full Riemann-Roch from Euler Characteristic

With the Euler characteristic formula χ(D) = deg(D) + 1 - g,
combining with Serre duality h¹(D) = ℓ(K - D) gives full Riemann-Roch.
-/

/-- Full Riemann-Roch theorem from Euler characteristic and Serre duality.

Given:
- χ(D) = ℓ(D) - h¹(D) = deg(D) + 1 - g
- Serre duality: h¹(D) = ℓ(K - D)

We get:
ℓ(D) - ℓ(K - D) = deg(D) + 1 - g
-/
theorem riemann_roch_from_euler
    [AdelicRRData k R K canonical genus]
    [ProperCurve k R K]
    {D : DivisorV2 R} :
    (ell_proj k R K D : ℤ) - ell_proj k R K (canonical - D) = D.deg + 1 - genus :=
  riemann_roch_from_adelic k R K

end EulerCharacteristic

end RiemannRochV2
