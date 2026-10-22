# Actual origin regularity of Green harmonic moments

Source: `lean/ScalarGreenOrigin.lean`.
SHA256: `3DC2B18CCBA9F834E1D0BA043392D9DEB7FFDF6C3774A0AAEEA91B0B1A7CA30A`.

Author target plus importable object compiler exit 0, no warnings. Object 219888 bytes. Six selected reports standard-only. Log: `lean/logs/ScalarGreenOrigin-final.log`. Forbidden-token scan passed.

Actual compact sphere parametric integration proves global continuity of the literal moment for any actual continuous spatial function, and of its actual first-Frechet-derivative moment when the spatial Frechet derivative is genuinely continuous. For the literal point-source Green kernel with nonzero source point y, the radius norm(y)/2 closed ball is genuinely contained in the open source complement. The existing actual smooth localization theorem constructs a global smooth function whose germ equals the literal kernel at every point of that ball. No smooth extension is supplied as a premise.

For every radius sufficiently close to zero, the complete radius-scaled sphere lies in this actual ball. Thus both the literal moment and literal derivative moment agree with those of the actual global smooth localization near zero, using actual Frechet derivative equality of equal germs. The proved compact sphere integral continuity therefore gives actual Green coefficient and derivative continuity at zero. This avoids inferring regularity at the origin from radial expressions that divide by radius. The source point y=0 is excluded explicitly in this origin-localization result; its radial source formula remains covered by ScalarGreenMoment.

Status: author PASS; frozen pending root complete-source and independent pinned compiler audit.

## Independent integration verification, October 22, 2026

Complete source independently reviewed. Pinned compiler exit 0, no warnings; all 6 reports use only standard foundations. Final source SHA256 `3dc2b18ccba9f834e1d0ba043392d9deb7ffdf6c3774a0aaeea91b0b1a7ca30a`. Independent log `lean/logs/ScalarGreenOrigin-root-audit.log`, SHA256 `3a84d3749bd8e4c6b4dbd887d5d166bfb6d08ee37274afe0653528d77fb85945`. The audit verifies this stated scope; complete OQ14 formalization remains unfinished.
