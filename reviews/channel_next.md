# Fresh channel route: spherical degeneracy and absolute bypass

Owned files: `manuscript/sections/channel_next.tex` and this review. No Git operations.

## Outcome

A new exact obstruction rules out a natural radial construction: arbitrarily large azimuthal degeneracy at one high angular order, amplified by unrestricted external radial Bragg layers, does not produce counted passage through a fixed centered square when a fixed homogeneous core contains the square and one exterior annulus. This holds with both polarizations and arbitrary coherent coefficients, not only one-port standing-wave fields.

The result is restricted to one angular order. It is not unrestricted channel closure.

## Derivation audit

- `cn:odd-return`: any integrable odd plane flux about a point in the plane has outside absolute flux at least the magnitude of its flux through any section. A single Maxwell inversion-parity sector therefore requires delta >= eta*tau. No centering of D is needed for this statement.
- `cn:flux-split`: for all regular electric/magnetic multipoles of one order ell in a homogeneous core, normal equatorial flux is F(r) O(phi) + G(r) C(phi). O is odd under phi+pi, C is even. The radial factors are F=sqrt(nu)*u^2/(2Z*k*r^3), G=sqrt(nu)*u*u'/(2Z*k^2*r^3), with u=r*j_ell(kr).
- The spherical curl signs are explicitly derived with X=rhat cross Psi: curl(j X)/k = -sqrt(nu)*j/(kr) Y*rhat - (rj)'/(kr) Psi. With exp(-i omega t), H=-i/Z (N_A+M_B).
- On the centered square, the odd flux integrates to zero. On a whole annulus, pairing opposite points bounds the absolute flux below by the absolute even part. This controls every coherent combination, with no diagonal/basis-only argument.
- `cn:radial-growth`: below the centrifugal turning scale, w=ru'/u solves r*w'=nu-k^2r^2+w-w^2. The invariant interval [gamma,ell+1], gamma=(1+sqrt(1+4(nu-k^2 R2^2)))/2, proves a lower power-law growth estimate.
- `cn:radial-bypass`: with R=L/sqrt(2), an annulus sR<r<tR, 1<s<t, and nu>k^2t^2R^2, outside absolute flux >= B_ell |P_D|, where B_ell=gamma/(ell+1)*(t^(2gamma-2)-s^(2gamma-2)). B_ell grows exponentially in ell. Hence delta >= B_ell*eta*tau is necessary for any nonzero counted input with pure-ell core field.
- The lower integral is bounded using u'<= (ell+1)u/r and u(r)<=u(R)(r/R)^gamma; the annulus uses u'>=gamma*u/r and the corresponding lower growth estimate. Both integrals carry the same positive normalization, which cancels.

## Quantifier audit

No actual counterexample is obtained merely from delta >= eta*tau. That regime permits compensating return flux, but the physical normalization and every-coherent-vector passage condition remain. T chosen as the full lossless scattering map is allowed but supplies only throughput; it does not create an infinite-dimensional positive passage subspace.

The obstruction does not cover mixed angular orders, a structured core, moving spherical centers with ell, or non-equatorial sections. No uniform bound on these unrestricted alternatives has been assumed.

## Verification status

The result is derived directly from the Maxwell equations and elementary spherical-harmonic parity; no unproved device synthesis result or external theorem supplies the bridge. The hotspot agent independently checked the radial cross-product signs, angular parity, opposite-point inequality, Riccati comparison, both radial integrals, and exponential growth; it found no substantive error. The parent owns integrated LaTeX builds and any formalization.

## Actual local mixed-order inverse synthesis

Added `cn:local-synthesis`: for any finite set of TE angular orders, a finite ordinary dielectric sphere admits 2m smooth radial material controls, supported in any prescribed interior annulus, that independently vary the m complex incoming coefficients of origin-normalized regular fields locally. This controls both physical core gain and phase, with fixed exterior power normalization.

The exact variation is D log A_l[h] = k0/(2i A_l) integral h*u_l*z_l, where z_l is the inward continuation of the vacuum outgoing Hankel wave. Inside the base homogeneous sphere its coefficients in the regular/irregular real basis have Im(alpha*conj(beta))=-k0/kappa, by their Wronskian. Thus real/imaginary variations span the two kernels psi_l² and psi_l*zeta_l. For finitely many distinct orders all such kernels are independent: even/odd parity separates the families, distinct Taylor vanishing orders prove square independence, and exact finite Hankel polynomials prove product independence. Smooth narrow bump controls then yield an invertible real Jacobian.

A retained quantitative neighborhood is explicitly stated using its smallest singular value sigma and a material/control radius rho: derivative variation <=sigma/2 gives target ball sigma*rho/2 by contraction. These quantities are not asserted uniform in m. The theorem does not yet give arbitrary simultaneous amplification or global absolute bypass. It is a real inverse-synthesis step, not a postulated effective network.

The coordinator independently checked the Wronskian sign, outgoing basis coefficients, complete kernel independence, bump selection, and retained contraction radius; it found no substantive defect. The hotspot agent subsequently independently checked the entire TE theorem and both-polarization corollary, including the TM weighted-Wronskian sign and adjacent-order identities, and likewise found no substantive defect.

Added `cn:both-synthesis`: if the selected orders differ by at least 3, 4m controls give local independent gain/phase tuning of both TE and TM. The TM derivative is (2ik0*A*n_b^4)^(-1) integral h*(u'*z' + l(l+1)u*z/r²). The weighted Wronskian fixes Im(alpha*conj(beta))=-n_b. Its two derivative kernels equal positive weighted combinations of adjacent-order regular squares and regular-irregular products. Disjoint triples {l-1,l,l+1} then prove independence together with the TE kernels. This is still local control, with its own possibly small Jacobian radius.

## Focused global continuation attempt

The attempted next step was to iterate the local inverse map until all required incoming coefficients A_l become small, giving large physical core response. That cannot work within a fixed bounded radial control region: `cn:fixed-control-ceiling` now proves a positive lower bound on |A_l| by a two-component radial transfer estimate, for both polarizations and arbitrary radial layer count. The explicit exponent is k0*(R0-r_-)*max(eps_plus,1+l(l+1)/(k0²*r_-²)); the fixed nonzero initial state and vacuum Hankel evaluation matrix give the remaining constants. The proof preserves material bounds and includes all radial interfaces.

Increasing support is allowed by the unrestricted target and could remove this fixed-region obstruction. However it also introduces a growing portion of the measured plane. No endpoint gain/phase synthesis bound controls absolute bypass in that region. The exact missing quantities are therefore (1) global simultaneous amplitude reachability with growing support while keeping positive bounded index and (2) the resulting coherent full-plane absolute-flux estimate. Neither is asserted merely from the local inverse function theorem. The single-order exponential bypass theorem shows why the second condition can fail even when amplification succeeds.

A targeted primary-source search inspected the scope of Palmai and Apagyi, *Quantum mechanical inverse scattering problem at fixed energy: a constructive method*, arXiv:1111.6009 (2011), https://arxiv.org/abs/1111.6009 . That fixed-energy phase-recovery work does not supply bounded-positive-permittivity Maxwell gain and bypass synthesis, and it is not used as a premise. The local theorem above is derived directly.

## Independent modal spectral audit requested by coordinator

Read `modal_spectral.tex` completely and the coefficient-continuation/transfer dependencies in `modal_next.tex`. No substantive defect found after the already identified compact-pencil correction: the continuation proof now explicitly uses F, rather than L, for norm convergence under material rounding. I reread and confirmed that correction in the saved source.

- Static compressed longitudinal P is positive; the Woodbury inverse I-Ps(I+sPs)^(-1)s checks. The remainder's 1/r kernel is Hilbert--Schmidt in three dimensions and entire in k.
- The Mie electric determinant and rational exponential reduction check. Its rational asymptotic distinguishes every angular order. For algebraic n, a multiple root or shared root would force nonzero algebraic z and algebraic exp(2inz), contradicting Lindemann--Weierstrass. The two rational coefficients cannot vanish together by the interior Hankel Wronskian.
- The Rouché circles of radius C/m around the stated l=1 centers give actual lower-half-plane poles, and their simple matching determinants give simple poles in the axisymmetric electric sector.
- For the reciprocal Green residue, the left functional is chi*E, d=ell L' E, and G=L^(-1)G0 with G0=k^(-2)K. Thus Res G=E tensor E/(k²d)=-E tensor E/(2k*N), N=-kd/2. All signs and factors check.
- Under spatial dilation by s, K' acting on the rescaled source gains s, d gains s^4, and N gains s^3. Thus a normalized electric field scales s^(-3/2), as used in the final fixed-real-frequency adjustment.
- The coefficient holomorphy uses subtraction of the constant regular remainder, preventing the lambda=1 apparent denominator from contaminating the limit. Its c0=sqrt(4pi/3)*E0(0) dot e and finite simultaneous nonvanishing check.
- Strong electric convergence, curl-div improvement, and fixed-interface scalar regularity supply the rounded collar convergence at varying complex k. The proof does not replace a QNM norm by divergent all-space energy.
