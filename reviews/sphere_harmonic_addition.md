# Genuine normalized harmonic evaluation and addition bounds

Source: `lean/SphereHarmonicAddition.lean`.
SHA256: `7987B9E9770BC6952906334B6C0158706F430EC0EE8C1DCC5C9292E489E8475A`.

Author final target plus importable object compiler exit 0, no warnings. Object 436504 bytes. Nineteen selected reports use only propext, Classical.choice, Quot.sound. Log: `lean/logs/SphereHarmonicAddition-final.log`. Forbidden-token scan passed.

The literal finite basis expansion lifts each actual degree-l sphere L2 vector to its unique continuous polynomial restriction. Actual orthogonal polynomial substitution and genuine volume-induced sphere measure preservation give a norm-preserving real linear map of this actual degree space. Finite dimension proves its surjectivity, so the construction is an actual linear isometry equivalence. Its continuous lift is literal precomposition by the sphere isometry.

The finite evaluation Riesz vector has squared norm equal to diagonal_l(n)=sum_i Y_li(n)^2. The genuine rotation map transports this vector, proving diagonal invariance. Actual reflection_sub maps any unit vector to any other; no transitivity premise is assumed. Hence the diagonal is spatially constant. Integrating the actual normalized squared basis functions gives the actual degree-space rank, proving

    sum_i Y_li(n)^2 = actualRank_l / angularArea.

The area is proved strictly positive from full support and finite sphere measure. Each normalized angular basis function has norm at most sqrt(actualRank_l/angularArea). The actual off-diagonal kernel sum_i Y_li(n)Y_li(m) is the inner product of the two genuine evaluation vectors, so Cauchy-Schwarz gives its norm at most actualRank_l/angularArea.

The rank is the actual finite image dimension, with the separate genuine polynomial bound at most (l+1)^3. No sharp 2l+1 dimension, Legendre closed form, cross-degree orthogonality, or derivative estimate is asserted. Actual normalized polynomial coefficient/jet bounds are the successor interpolation task.

Status: author PASS and root full-source / independent pinned compiler PASS. Frozen unchanged.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 19 reports use only standard foundations. Final source SHA256 `7987b9e9770bc6952906334b6c0158706f430ec0ee8c1dcc5c9292e489e8475a`. Independent log `lean/logs/SphereHarmonicAddition-root-audit.log`, SHA256 `56f2ed14b2c83d523a6b2dc5b21e00dc2e414cebb53ee6c05604982a73d7428a`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
