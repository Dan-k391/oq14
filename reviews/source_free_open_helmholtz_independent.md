# SourceFreeOpenHelmholtz — independent root audit

PASS, 2026-10-28. Full source and mathematical scope reviewed independently. Source SHA256 `C19DA8D82BF0D87422B063CD41A4CC51474E63A8864CC7E69A93432D7F7788CE`.

Fresh pinned source check completed with exit 0. Audit log: `lean/logs/SourceFreeOpenHelmholtz-root-audit.log`, SHA256 `F0689A745CA3CCD4B5B3A9ED6668D78D2DB4BAA99AF4D76021774CEF90163DFE`. Exit receipt: `lean/logs/SourceFreeOpenHelmholtz-root-audit.exit.log` = 0. All 7 reports use only standard axioms; no errors, warnings or proof placeholders. The check uses existing dependency objects, not a clean dependency rebuild.

Global response Maxwell pairings restricted to source-free tests give the local weak Helmholtz equation. Almost-everywhere identification with the smooth integral representative then gives the classical equation. For a finite union of strictly separated closed balls, existing connectedness of the complement and unique continuation propagate the annihilator's known exterior zero throughout that complement. Actual compact-source reciprocity then makes its pairing with every compact L2 source vanishing on the balls zero. Sources may lie inside the common enclosing ball; this is the required distinction from centered-ball Runge.
