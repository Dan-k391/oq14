# Quadratic moving-gap coherent flux stability

Frozen source: lean/PlaneQuadraticMoving.lean.
SHA256: B915E094CF41FE144D3A4EED3A8452656C287E575F8CFA5B09600B7263FD86B2.
Author final pinned compiler/object emission PASS: exit 0, no warnings,
all four reports standard-only. Log: lean/logs/PlaneQuadraticMoving-final.log.
Independent audit pending.

The explicit genuine quadratic whole-plane constant at gap gamma*a,
multiplied by a^5, is exactly a polynomial with a^2, a^3 and a^5 terms.
Its limit is proved. Actual compact sources with gap gamma*a, source masses
at most M*a^2 and actual L1 difference at most C*a^3 therefore have genuine
quadratic outgoing normal-flux difference bounded by 2*C*M times this
vanishing factor, and their whole-plane L1 error tends to zero.

Neither a whole-plane flux limit nor a field error estimate is assumed.
The source masses and their difference are explicit generic premises to be
discharged by the actual finite-ball inverse. This concerns the free outgoing
volume quadratic term; gain-weighted parity reactions and their coherent
assembly, physical finite-stack identification and channel normalization
remain separate.
