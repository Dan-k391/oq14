# Independent complete-source and compiler audit

Source `lean/RadialToroidalCurl.lean`, SHA256 `0FB14B0465F831B59DDD2FCD596DC87743DAB7772113E7B656FB5CB0E7C6B35E`.
Independent log `lean/logs/RadialToroidalCurl-independent-modal.log`, SHA256 `B5C547923D8AAF1C9D99D4785F26ED1B384165E247897C26860E0E5BE1814842`.

Full-source mathematical review PASS. Fresh pinned compiler EXIT0/no warnings/all 1 reports standard-only. Frozen source unchanged.

The actual arbitrary radial toroidal multiplier curl is derived using an explicit affine radial function with the same value and actual first derivative at the chosen radius. Actual coordinate partial identity transports the first jet, then the genuine smooth toroidal curl formula applies. No higher derivative or homogeneous radial-germ hypothesis is supplied; harmonic homogeneous polynomial hypotheses are explicit.

Status: independent modal source and compiler PASS.
