# Renewed channel closure audit

Owned files: `manuscript/sections/channel_closure_audit.tex` and this review. No Git operations performed; original `channels.tex` left unchanged during this renewed assignment.

## New rigorous progress

`ca:powerbudget` proves a global necessary threshold: in the compact-scatterer vacuum radiation class, hemisphere Poynting balance gives -||a||² <= P_plane <= ||a||². Absolute bypass then gives |P_D| <= (1+delta)||a||². No nonzero counted subspace exists if eta*tau>1+delta. This closes only an empty/unphysical threshold regime, not the meaningful channel conjecture.

`ca:loewner` records the actual all-superposition inequalities eta*T*T <= Q_D <= (1+delta)I and tau*I <= T*T <= I. These inequalities alone hold in every dimension; they supply no rank estimate.

`ca:localpackets` proves a stronger local obstruction than the existing evanescent sine example: at fixed D, frequency, and slab height, every finite N has exact smooth full-vector vacuum Maxwell fields with integrable flux on the WHOLE plane, total flux Gram I_N, pointwise nonnegative plane flux, P_D >= (1-delta)I_N, and outside-D absolute bypass <=delta for EVERY coherent vector. Construction uses orthonormal disjoint-frequency sinc wave packets and exact bandlimited Maxwell Cauchy evolution. All wavevectors can lie arbitrarily far beyond the propagating light circle. This is local flux normalization, not external incoming-power normalization.

`ca:packetresource` quantifies the missing resource: slab field norm >= 4h*q_min²/(c0*k0²) times coefficient norm². It can diverge while all coherent plane-flux conditions remain fixed. No local proof can eliminate energy merely from those conditions.

`ca:outgoingfailure` proves these exact local data cannot be continued into a homogeneous outgoing vacuum upper half-space: pure evanescent decaying data have zero asymptotic normal flux, contradicting the conserved positive full-plane flux. An external dielectric matching structure is an additional, unproved global realization problem. The result does not exclude all such structures.

`ca:compactcompletion` tightens the preceding scope: exact reproduction of the entire slab data by a compact dielectric outside the slab is impossible under standard propagating-incoming/outgoing radiation conventions. The Cauchy fields have an entire homogeneous extension; vacuum unique continuation identifies any proposed scattering field with that extension outside a large ball. In the upper half-space the pure high-q spectrum would then have to decay, contradicting positive plane flux. A physical many-channel proposal must therefore construct quantitatively controlled approximate data or different accessible fields; arbitrary resonant matching is not ruled out.

## Mathematical checks

Fourier convention: unitary transform; hat(phi_b)=(2b)^(-1/2) on [-b,b], giving phi_b=sin(bx)/(sqrt(pi*b)*x) and L2 norm one. One-coordinate escape <=4/(pi*b*L), square escape <=8/(pi*b*L). With b>=8N/(pi*L*delta), pointwise Cauchy--Schwarz supplies the all-vectors outside-plane bound.

Modulations K_j=Q+3bj produce disjoint support rectangles, so packet Gram is exactly I, without an approximate orthogonalization argument. Q>k0 makes all supports evanescent. Cauchy data in normalized fields: e_t=(0,Cf), h_t=(-Cf,0), e_z=iC/k0*dy f, h_z=-iC/k0*dx f, C=sqrt(2/c0). They give S_z=|f|². Tangential first-order evolution reconstructs all six curl equations, with no impressed currents.

Finite Fourier support implies smoothness and finite field norm on every finite slab even though the Cauchy problem is not uniformly well posed as the frequency support grows. The lack of a uniform estimate is the point, not a neglected issue.

Resource lower bound uses the scalar Helmholtz equation satisfied by each magnetic component, cosh/sinh evolution, cancellation of the odd cross term on (-h,h), and Plancherel. At z=0, ||h_z||² >=2*q_min²/(c0*k0²)||a||².

## Primary-source extension checked

A. Douglas Stone, William R. Sweeney, Chia Wei Hsu, Kabish Wisal, Zeyu Wang, *Reflectionless excitation of arbitrary photonic structures: a general theory*, Nanophotonics 10, 343-360 (2021), DOI 10.1515/nanoph-2020-0403. Primary article: https://onlinelibrary.wiley.com/doi/10.1515/nanoph-2020-0403 ; arXiv author version: https://arxiv.org/abs/2010.02470 . Read the multichannel reflectionless-state formulation, structural tuning discussion, and TCMT comparison. It does not give the same-frequency N-dimensional fixed-D passage/bypass realization required here. New manuscript uses direct DOI link, so no new bibliography key is required.

Searches for arbitrary Maxwell scattering-matrix synthesis and dielectric evanescent resonant tunneling returned inverse-reconstruction work, single-state matching, or ENZ/metallic-channel results. None inspected discharges the frozen global bridge. No exhaustive absence claim is made.

## Full closure and Lean status

Original full vector channel question remains OPEN. The sharper local counteraudit does not change that status. Global radiative accessibility, matching, and all-channel error control remain decisive. No premise has been silently upgraded to a theorem.

Lean can check stable algebraic lemmas and certificates; it cannot turn the unresolved global synthesis/exclusion into a theorem without proving that continuum bridge. No full-OQ14 Lean result is claimed, and no axiom assuming the missing bridge is proposed.

## Independent review of finite-three-dimensional hotspot proof

Read `manuscript/sections/hotspot_closure_audit.tex` completely, with particular attention to the bridges requested by the coordinator. No substantive gap found in the stated driven finite-device theorem after the noted correction.

- `hs:three-angular`: the double-cap trial z has weighted mean zero and makes the Rayleigh numerator minus twice denominator strictly negative. The first positive weighted spherical eigenvalue therefore gives 0<lambda<1. The integrated electrostatic energy lambda*R^(2lambda+1) checks directly.
- `hs:three-decomposition`: electric curl Caccioppoli, constant-mu magnetic div-curl regularity, and a regularized curl lifting give a bounded H2 remainder. The primary Costabel–McIntosh paper was independently checked: Corollary 3.4 gives Hs→H^(s+1) for the Poincare operator on a ball, and the homotopy identity gives curl R f=f when div f=0. Primary PDF: https://costabel.perso.math.cnrs.fr/publis/PoiBogdeRhv2.pdf . The use requires no boundary condition on the lifted field.
- `hs:three-coefficient`: derived the projected radial equation and variation-of-constants formula. As an independent sign test, for constant W, the angular eigenidentity gives B=nu*A and the particular term becomes p=-r*A, exactly what the compensating potential v=-W dot x requires. Bounded W makes p=O(r), p'=O(1); the averaged annular coefficient is L2-continuous on Maxwell solutions through the regular decomposition. Lifting independence follows because a bounded gradient changes the potential only by a Lipschitz function, whose weighted projection is O(r).
- `hs:three-local-excitation`: the weighted Helmholtz decomposition preserves tangential-zero boundary condition; the weighted divergence correction has norm <=d times the solenoidal part. PEC curl coercivity for sufficiently small kappa gives w=O(kappa²). Applying div-curl to curl w produces H1 size O(kappa²), so the lifting and projected coefficient give c=1+O(kappa²), avoiding the possibly singular 1/kappa constant in the general Maxwell decomposition. The PEC boundary is a local mathematical construction and is not inserted into the final device.
- `hs:three-volume`: the singular dyadic part has Fourier multiplier -xi*xi^T/|xi|² of norm one; the remaining kernel is locally O(1/r), hence bounded on the fixed ball by its L1 norm. The fixed-small-contrast Neumann inverse is uniform over all rounded geometries and does not require a minimum feature size.
- `hs:three-illumination`: the sphere stationary-phase coefficient 2pi/(ikr), combined with the displayed prefactor, gives incoming electric amplitude of modulus sqrt(2Z0)|g(-xhat)|/r and incoming power ||g||².
- `hs:three-runge`: bilinear reciprocity is appropriate for the symmetric real coefficient; smooth-density annihilation recovers every plane-wave polarization by continuity. Zero far field gives zero exterior field. Across a smooth interface outside the local approximation region, zero tangential E and curl E allow extension by zero as a constant-coefficient Maxwell solution; finite conical/curve sets can be avoided by paths. Both boundary traces then vanish on Q, proving annihilation of every local source-free field. This is density of total fields in the actual material.
- `hs:three-rounding`: the uniform volume inverse and dominated convergence yield strong electric L2 convergence. In a fixed unchanged smooth-interface neighborhood, the regular decomposition converts the difference to a scalar transmission problem. H2 remainder supplies H1 volume forcing and H3/2 conormal data, giving local piecewise H3 potential and thus uniform one-sided electric convergence. No estimate uniform at the shrinking tips is needed. The fixed smooth collar avoids the vertex/joining curves.
- Final diagonal argument chooses one incoming density, normalizes once, chooses high ordinary points before rounding, and retains all points and collar bounds simultaneously. The fields are finite 3D, with finite total incoming power; the target patch is explicitly a projection constraint and peak locations need not lie on the original plane.

Correction sent and confirmed fixed: `hs:three-no-real-mode` must use the REAL part of the complex Poynting identity for zero outward radiated power; its imaginary part instead measures the electric/magnetic energy difference. The author also expanded the ball Maxwell-inequality regularity justification and clarified the restoration of physical units.

The modal normalization/continuation problem remains open, and none of this independently reviewed driven construction supplies an area-only channel theorem or a full Lean verification.

## Independent review received on this channel audit

The hotspot agent independently checked the entire new channel audit, including Cauchy signs, sinc tail constants, coherent control, resource bound, hemisphere flux budget, and exact compact-exterior no-completion. It found no substantive defects. The coordinator independently checked the same core signs and constants. A LaTeX environment mismatch in the multi-column Cauchy equation was corrected from `split` to `aligned`.
