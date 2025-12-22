# Target theorem (informal but precise)

Let k be an algebraically closed field and X a smooth projective curve over k.
Let D be a divisor on X, and let K be a canonical divisor on X.

Assume: for any divisor Z, the cohomology groups H^i(X, O_X(Z)) are finite-dimensional over k.

Define:
- ℓ(D) = dim_k H^0(X, O_X(D)) as a natural number.
- g(X) = dim_k H^1(X, O_X) as a natural number.

Then, in ℤ:
(ℓ(D) : ℤ) - (ℓ(K - D) : ℤ) = deg(D) + 1 - g(X)

## Definitions
- O_X(D): the invertible sheaf associated to divisor D.
- K: a divisor such that O_X(K) ≅ Ω¹_{X/k}.
- deg(D): the degree of divisor D (integer-valued).
- (· : ℤ): coercion ℕ → ℤ.

## Allowed internal reformulations
- Line bundle / invertible sheaf formulation.
- Canonical divisor ↔ canonical sheaf.
- Use Serre duality to identify H¹ terms if necessary.

## Disallowed changes
- Changing hypotheses (smoothness, projectivity, algebraic closedness).
- Removing the divisor formulation from the final statement.
- Omitting the integer coercion logic.

## Priority
Correctness > formalizability > elegance
