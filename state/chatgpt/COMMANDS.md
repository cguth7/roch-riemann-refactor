# Verification Commands

## Axioms (explicit)
rg -n "^axiom\\s" RrLean/RiemannRochV2 --glob "*.lean"

## Sorries (actual placeholders)
rg -n "(:=\\s*sorry|by\\s+sorry|\\bsorry\\b$)" RrLean/RiemannRochV2 --glob "*.lean"

## Euler characteristic sanity check
rg -n "\\bsorry\\b" RrLean/RiemannRochV2/Adelic/EulerCharacteristic.lean

## Axioms for a theorem (Lean)
# Example:
# lake env lean -K5000 -T5000 -q <<'EOF'
# import RrLean.RiemannRochV2
# #print axioms RiemannRochV2.Elliptic.riemann_roch_fullRRData
# EOF
