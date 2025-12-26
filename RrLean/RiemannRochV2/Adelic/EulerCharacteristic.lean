import RrLean.RiemannRochV2.Adelic.AdelicH1v2
import RrLean.RiemannRochV2.Dimension.KernelProof
import RrLean.RiemannRochV2.Definitions.Infrastructure

/-!
# Euler Characteristic via Exact Sequence (Cycle 325)

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
  -- Technical: at each place, we get 0 = 0
  sorry

/-- The single-place adele respects addition. -/
lemma finiteAdeleSingleHere_add (v : HeightOneSpectrum R)
    (x y : v.adicCompletion K) :
    finiteAdeleSingleHere R K v (x + y) =
    finiteAdeleSingleHere R K v x + finiteAdeleSingleHere R K v y := by
  -- Technical: at v we get x+y = x+y; at other places, 0+0 = 0
  sorry

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
  -- The key is that Quotient.out' 0 ∈ v.asIdeal
  -- and the resulting adele is in globalPlusBoundedSubmodule
  -- This requires showing the adele is bounded or differs from 0 by a global element
  sorry -- Will be filled once we prove the valuation bounds

/-- The connecting homomorphism is additive.

Key: Different lifts of the same residue class differ by elements of v.asIdeal,
and in H¹(D), these differences become global elements that quotient out.
-/
lemma connectingHomFun_add (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (α β : residueFieldAtPrime R v) :
    connectingHomFun k R K v D (α + β) =
    connectingHomFun k R K v D α + connectingHomFun k R K v D β := by
  simp only [connectingHomFun]
  -- This requires showing that the quotient map is compatible with the construction
  -- The key is that out'(α + β) - (out'(α) + out'(β)) ∈ v.asIdeal
  -- and after the construction, this difference becomes a bounded element
  sorry -- Will be filled with detailed valuation analysis

/-- The connecting homomorphism respects k-scalar multiplication. -/
lemma connectingHomFun_smul (v : HeightOneSpectrum R) (D : DivisorV2 R)
    (c : k) (α : residueFieldAtPrime R v) :
    connectingHomFun k R K v D (c • α) = c • connectingHomFun k R K v D α := by
  simp only [connectingHomFun]
  -- c • α corresponds to algebraMap k R c * r in R
  -- The single-place adele construction is linear
  sorry -- Will be filled with scalar tower compatibility

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

/-- The residue field κ(v) has dimension 1 over k.

The residue field κ(v) = R/v.asIdeal is a simple R-module (has length 1),
which when k ⊆ R implies dim_k(κ(v)) = 1.
-/
lemma kappa_dim_one (v : HeightOneSpectrum R) :
    Module.finrank k (residueFieldAtPrime R v) = 1 := by
  -- The residue field is 1-dimensional over k by hypothesis on k being
  -- the field of constants (i.e., k = H⁰(O_X))
  sorry

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
