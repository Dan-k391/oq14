# Actual physical Green coefficient normalization

Source: `lean/ScalarGreenNormalization.lean`.
SHA256: `3051587F290AA3973E19253C16F626985E449F129329BAAC00A782CF63C9B9CE`.

Author target and importable object EXIT0, no warnings; 433424 object bytes. Three selected reports standard-only. Log `lean/logs/ScalarGreenNormalization-final.log`. Forbidden-token scan passed.

The quotient Wronskian is derived from the actual regular/outgoing Riccati Wronskian and actual quotient derivatives. Actual matching plus the negative source jump determines both amplitudes without dividing by either radial wave value, so zeros of the regular wave cause no gap. Applying this algebra to the actual Green moments yields the literal min/max formula with physical I/k normalization and source polynomial normalization s^(-l). Frequency is positive real; source is nonzero; observation radius is positive and differs from source norm. This matches the manuscript reduced radial jump +1 convention, whose physical scalar multiplier has a minus sign. No electric dyadic prefactor or spatial differentiated series identification is inferred here.

Status: author PASS; frozen pending root full-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 3 reports use only standard foundations. Final source SHA256 `3051587f290aa3973e19253c16f626985e449f129329baac00a782cf63c9b9ce`. Independent log `lean/logs/ScalarGreenNormalization-root-audit.log`, SHA256 `9dfb94c89a581672268d70d0380fe87821a94d6028ebd33421b6c7b6e14e7bb6`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
