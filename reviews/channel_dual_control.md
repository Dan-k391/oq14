# Paired TE/TM radial control and wall-sector isolation

Owned files: manuscript/sections/channel_dual_control.tex and this review. Existing mathematical sections remain frozen. No Git operations.

## Exact paired-loop calculation

The reference TM generator is the negative transpose of the TE generator, so the TM prefix is the inverse transpose of the TE prefix at every location. If the TE prefix has rows (a,b),(c,d), its TM angular interaction integrand is n^-2 * [[cd,-c²],[d²,-cd]]. Its operator norm is (c²+d²)/n².

Direct quarter-layer integration gives integral c²/n²=b_M, integral d²/n²=d_M, and integral cd/n²=0, with the exact b_M,d_M already derived in cc:loop-derivative. Thus B_TM=-B_TE^T and both integrated interaction norms equal b_M+d_M. The finite-radius and accumulated-loop error constants carry over unchanged. Each positive-time TE angular shear exp(t nu Y) is paired with TM exp(-t nu X).

The actual paired asymptotic realizability semigroup contains common graph elements (G,G^-T). The map G -> (G,G^-T) is a group homomorphism. The signed-time, Vandermonde, and open-subgroup construction therefore proves all finite paired targets, using the same physical layers. This is a reachable family, not a universal restriction on all radial media.

## Physical wall gains

The electric-wall reflection condition is E(R_z x)=-R_z E(x), H(R_z x)=R_z H(x), giving Et=0 and Hz=0 at the plane. TE is electric-wall for l+m even; TM for l+m odd. Restriction to C2-even inputs means m even, hence electric-wall means TE even l or TM odd l.

Choose transfer targets G_l=diag(A_l,A_l^-1), start at R=2*pi*n, and use the paired theorem. Core gains after one common phase removal are TE-even=A_l, TE-odd=A_l^-1, TM-even=A_l^-1, TM-odd=A_l. Thus each controlled electric-wall sector is amplified and its opposite is suppressed. Uniform A across the band gives limiting multiplier A*P_e+A^-1*P_m.

Both wall sectors individually have zero pointwise normal plane flux. Uniform reciprocal gains cancel in the cross-sector flux form. No passage is created by this unperturbed amplification. No estimate is supplied for unselected partial waves, a full Green operator, a driven inclusion, or the symmetry-broken device.

## Review status

Both root and hotspots independently reviewed the completed source. They checked the reference differential inverse-transpose identity, explicit second rows and weighted TM integrals, identical error constants, graph homomorphism and group argument, spherical reflection and C2 parity, and the common physical phase in the gain table. Neither identified a substantive defect. The source is frozen after those audits.
