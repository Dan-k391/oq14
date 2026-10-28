# Independent review: ComplexRegionalMaxwell

PASS. Fresh compiler log: `lean/logs/ComplexRegionalMaxwell-root-audit.log`. The compiler completed with exit 0 and no warnings or errors.

Source SHA-256: `4E5D7A32F3271E84CDD60FD14D70290F53F99EBC64FB0ADF1002B72368B8F92F`

Compiler log SHA-256: `D22FD43C7834A69E6379ED9B8F7190774D5D5B849DB7F45227B6C52474D62B95`

Both fully qualified OQ14 axiom reports match the source commands and contain only propext, Classical.choice and Quot.sound. Full-source scan found no forbidden declarations or placeholder tokens.

The explicitly assumed distributional Maxwell curl identities imply the electric Helmholtz pairing for nonzero k and permittivity; the factor simplifies to k² ε with the stated signs. With ε = n² and local integrability, this yields the weak Helmholtz equation with wave number k n and its annular harmonic moment equation. The results assume the Maxwell identities and integrability; they do not establish these for a particular physical field or classify its modes.
