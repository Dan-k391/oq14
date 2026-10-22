# Independent complete-source and compiler audit

Source `lean/SourceDielectricMaxwell.lean`, SHA256 `50745FF3C632505C075B4857BB9EDD4739A3D19115DC7207AB8B28999FF962E4`.
Independent log `lean/logs/SourceDielectricMaxwell-independent-modal.log`, SHA256 `2298B5B7FDD6DF9FB7DAB12359B2DEB16B1B578528E0F1B26EB22ABB4FA314E9`.

Full-source mathematical review PASS. Fresh serial pinned compiler EXIT0/no warnings/all 4 reports standard-only. Frozen source unchanged.

Actual selected sigma is identically one under literal layer sigma=1; actual constitutive mu is one under q^2=sigma. The general actual punctured equations therefore instantiate both TM dielectric equations and dual TE dielectric equations, with actual electric coefficient sigma or mu respectively. Actual compact tests must avoid zero. No material matching, source singularity or radiation result is assumed as a premise.

Status: independent modal source and compiler PASS.
