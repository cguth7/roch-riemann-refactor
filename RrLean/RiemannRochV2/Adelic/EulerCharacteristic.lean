import RrLean.RiemannRochV2.Adelic.AdelicH1v2
import RrLean.RiemannRochV2.Dimension.KernelProof
import RrLean.RiemannRochV2.Definitions.Infrastructure

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

/-- Exactness at κ(v): image(eval) = ker(δ).

Elements mapping to zero under δ are exactly those from L(D+v).

Note: The evaluation map is R-linear while δ is k-linear. The exactness holds
for the underlying sets, i.e., as sets we have image(eval) = ker(δ).
-/
theorem exactness_at_kappa_set (v : HeightOneSpectrum R) (D : DivisorV2 R) :
    (Set.range (evaluationMapAt_complete (K := K) v D) : Set (residueFieldAtPrime R v)) =
    {α | connectingHom k R K v D α = 0} := by
  -- This requires:
  -- 1. If α = eval(f) for f ∈ L(D+v), then δ(α) = 0 because f provides a global element
  -- 2. If δ(α) = 0, we can construct f ∈ L(D+v) with eval(f) = α
  sorry

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

/-- Exactness at H¹(D): image(δ) = ker(proj).

The kernel of H¹(D) → H¹(D+v) is exactly the image of δ.
-/
theorem exactness_at_H1 (v : HeightOneSpectrum R) (D : DivisorV2 R)
    [hfin : Module.Finite k (SpaceModule k R K D)] :
    LinearMap.range (connectingHom k R K v D) =
    LinearMap.ker (H1Projection k R K v D) := by
  -- The kernel of proj consists of [a] where a ∈ K + A_K(D+v) but a ∉ K + A_K(D)
  -- Such elements have a pole of order exactly 1 at v, which is the image of δ
  sorry

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
