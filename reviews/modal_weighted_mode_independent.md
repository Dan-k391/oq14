# ModalWeightedMode — independent audit

PASS, 2026-10-27. I audited the full frozen source and checked its relevant imported definitions and residue theorem. Source `lean/ModalWeightedMode.lean` SHA256 `E77232DAC540DFCCCF9E37CFCB634CD133225FC5DE4FFFDA264F24172135342B`.

Fresh pinned Lean 4.19.0 compilation: `lean/logs/ModalWeightedMode-terra-audit.log`, SHA256 `57F62E6A4D88C2D025ABF8C6928119FFB68E0A0F33129973DBBF0E59244B612E`; exit receipt `lean/logs/ModalWeightedMode-terra-audit.exit.log` records exit 0. The complete log contains exactly nine axiom reports, no errors or warnings, and only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Source scan found no forbidden declarations or placeholders (`sorry`, `admit`, `axiom`, `opaque`, or `unsafe`); the nine `#print axioms` commands are reports.

For real n > 1, the coefficient is χ = n² − 1 on the open unit ball and zero elsewhere, supported in the closed unit ball. The existing Maxwell sphere coefficient agrees with 1 + χ almost everywhere, including the interface qualification. For nonzero complex frequency k and amplitudes f, the constructed L2 vector is the actual physical coordinate √χ E of the global electric residue mode almost everywhere, with source χ E and the stated interior formula. These coordinate identities do not require a determinant root.

Nonzero interior residue amplitude implies a nonzero weighted vector: vanishing in L2 would make its continuous interior component vanish everywhere on the open ball, contradicting its explicitly nonzero center value. The final existence theorem additionally assumes tmDet 1 n k = 0 and its complex derivative at k is nonzero; it invokes the imported simple-pole residue theorem to obtain suitable amplitudes. It does not prove that such a frequency exists.

The result constructs a nonzero weighted residue field. It does not establish its membership in the complex-frequency volume kernel, nor sector isolation or a volume-resolvent residue; those remain separate representation obligations.
