# ElectricPotentialDecomposition — Independent full-source audit

Source SHA256: `9890DC125C12BAE853C7490606A9647AF3FB95A3A339B72E5E40618731FB5453`.
Pinned Lean 4.19 targeted compile EXIT0; no warnings; all 7 dependency reports use only the standard axioms. Log `lean/ElectricPotentialDecomposition-independent-sol.log`, SHA256 `61B4361A042545D01C26B353FBC7E9285EFFF4566D5D4D2E5ADC12AE76C87A01`.

PASS. The literal scalar potential is the sum of actual Green-gradient convolutions, and the correction is literal k^2 times actual scalar Green convolution. Genuine distributional Green-gradient integration by parts and the actual electric-response pairing give grad V=E-W with the correct sign and both test integrals integrable. Existing actual local L2 response estimates establish V and its weak gradient locally L2. The correction continuity and its explicit k^2 bound are specialized from the independently checked scalar-potential convolution theorem. No H2 regularity or assumed decomposition is used.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 7 reports use only standard foundations. Final source SHA256 `9890dc125c12bae853c7490606a9647af3fb95a3a339b72e5e40618731fb5453`. Independent log `lean/ElectricPotentialDecomposition-independent-sol.log`, SHA256 `61b4361a042545d01c26b353fbc7e9285efff4566d5d4d2e5adc12ae76c87a01`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
