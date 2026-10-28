# Independent review: ComplexExteriorResponse

PASS. Fresh compiler log: `lean/logs/ComplexExteriorResponse-root-audit.log`. The compiler completed with exit 0 and no warnings or errors.

Source SHA-256: `7065EDB350DD7CAF76FEAF0F6EC85346358C829EEC3FE6A270BCEA9700F9A887`

Compiler log SHA-256: `300DE3FE520F1E1E6D1D48657E5D35E6D4E423600B63A72B64A2484B2FA221D2`

Three fully qualified OQ14 axiom reports match source commands and contain only propext, Classical.choice and Quot.sound. Full-source scan found no forbidden declarations or placeholders.

The actual localized response uses the Newton operator and complex remainder cut off at observation radius T plus source radius S. For coefficient supported in the source ball, it matches the actual real-frequency scattered field almost everywhere in the observation ball. For tests supported there, the actual weak source residual is entire when T+S is nonnegative and vanishes on the real line, so the identity theorem gives zero at every complex frequency. The result does not identify global outgoing behavior or an exterior boundary trace.
