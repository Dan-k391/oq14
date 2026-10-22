# Independent audit of actual quarter-wave parity limits

Source: `lean/RadialParityLimit.lean`.
SHA256: `35DB70B972B82142170F6A26E1B6376412225B54F1740D37070E841B6258C8CF`.

Independent full-source mathematical review and pinned Lean 4.19 compiler:
PASS. Exit 0, no warnings, and all eight reports use only propext,
Classical.choice, and Quot.sound. Log:
`lean/logs/RadialParityLimit-independent-continuation.log`.

The actual backward constant-reference pair is evaluated from its literal
sine/cosine matrices at the negative quarter-wave widths. Repetition gives
the actual diagonal factors (-sigma/q)^n and (-q/sigma)^n in the inward
reference state. The actual vacuum phase is evaluated separately for even
and odd degree, and its actual limiting coefficient ratio is derived by
explicit algebra with q and sigma nonzero.

The previously proved actual gamma limit is then specialized to obtain
-i*(q/sigma)^(2n) in even degree and -i*(sigma/q)^(2n) in odd degree. No gamma
or Green coefficient limit is a premise in these specializations.

Scope: fixed degree and fixed pair count n on the actual common radius
sequence. Uniformity over all degrees, the physical TE/TM identification,
all-channel kernel summation, and finite-stack spatial Green identification
remain separate work.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 8 reports using only standard foundations. Final source SHA256 `35db70b972b82142170f6a26e1b6376412225b54f1740d37070e841b6258c8cf`. Independent log: `lean/logs/RadialParityLimit-independent-continuation.log`; log SHA256 `a702e1aeee80e92d34387ee881a5dd8d99310c7bcce8da81933eb73eab682f09`. This certifies the stated scope, not either complete OQ14 construction.
