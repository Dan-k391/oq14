# Actual free Green expansion in spatial polynomial coordinates

Source `lean/ScalarGreenSpatial.lean`, SHA256 `2AA8D3C9F591F4E47107AE7754295E6FA23ACF2244658A97ABCD37D0BCB18929`.

Author target+object EXIT0/no warnings, 242448 bytes. Three selected dependency reports standard-only. Forbidden-token scan passed. Log `lean/logs/ScalarGreenSpatial-final.log`.

Actual Phi symmetry and the proved pointwise expansion handle both radial orders. Genuine homogeneous representative scaling converts the angular expression into literal spatial polynomial factors P_a(x)P_a(y), with denominators norm(x)^(l+1)norm(y)^(l+1), genuine entire origin at k*min(norms), actual xi at k*max(norms), and actual I/k prefactor. Actual unit-radius representation of each nonzero point discharges the geometric parametrization. Thus actual HasSum to Phi_k(x-y) holds for every positive frequency and arbitrary nonzero x,y of unequal norms, without an assumed expansion. Zero-radius extension, equal-radius singular sphere, and spatial differentiated free series remain separate.

Status: author PASS; frozen pending root full-source and independent pinned compiler audit.
