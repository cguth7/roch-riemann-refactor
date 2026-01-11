# Blockers

Format:
- Blocker:
- File/lemma:
- Why hard:
- Sketch or known approach:
- Dependencies:
- Status:

----

- Blocker: Strong approximation (P1)
- File/lemma: RrLean/RiemannRochV2/Adelic/StrongApproximation.lean (instStrongApprox_P1)
- Why hard: restricted product topology glue
- Sketch or known approach: use density in each completion + CRT; need RestrictedProduct topology lemmas
- Dependencies: FullAdelesCompact infrastructure
- Status: todo

- Blocker: Strong approximation (elliptic)
- File/lemma: RrLean/RiemannRochV2/Adelic/StrongApproximation.lean (instStrongApprox_Elliptic)
- Why hard: non-PID adelic analysis
- Sketch or known approach: textbook strong approximation for function fields
- Dependencies: none in repo; external math
- Status: blocked

- Blocker: Serre duality (elliptic, non-vanishing)
- File/lemma: RrLean/RiemannRochV2/Elliptic/EllipticH1.lean (serre_duality)
- Why hard: residue pairing + perfectness
- Sketch or known approach: reuse SerreDuality infrastructure, prove nondegeneracy
- Dependencies: residue theory, pairing
- Status: blocked

- Blocker: H1 vanishing for deg>0 (elliptic)
- File/lemma: RrLean/RiemannRochV2/Elliptic/EllipticH1.lean (h1_vanishing_positive)
- Why hard: needs strong approximation
- Sketch or known approach: adelic density implies quotient zero for large D
- Dependencies: instStrongApprox_Elliptic
- Status: blocked

- Blocker: genus=1 (elliptic)
- File/lemma: RrLean/RiemannRochV2/Elliptic/EllipticH1.lean (h1_zero_eq_one)
- Why hard: invariant differential
- Sketch or known approach: show H1(O) spanned by invariant differential
- Dependencies: differential setup
- Status: blocked
