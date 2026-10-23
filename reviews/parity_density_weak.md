# Actual parity density weak Maxwell equations

Frozen source: lean/ParityDensityWeak.lean.
SHA256: CB79E44619EA72DDB33349F49BA08FCF3C2B6D240DA31F46D43FE72065C753FA.
Author final pinned Lean 4.19 compiler/object PASS: exit 0, no warnings,
one standard-foundation report. Log: lean/logs/ParityDensityWeak-final.log.
Independent audit pending.

Both actual density kernel weak-curl pairings are instantiated with the
proved sphere parity differential bounds, integrability and actual point
Maxwell identities. Component/test conversion yields genuine vacuum
MaterialMaxwell.TestMaxwell for the literal electric/magnetic density pair.
Only actual component integrability of the source is supplied. No weak
Maxwell conclusion, curl interchange or operator identity is assumed.

This supplies the reaction part of the modified incident weak Maxwell pair.
Complete material assembly and physical finite-stack identification retain
their separate scopes.
