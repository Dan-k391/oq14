# Explicit parity-kernel transducer limit

New source: `manuscript/sections/channel_transducer_limit.tex`, labels `cl:*`. This is a proved transfer lemma for the explicit limiting core kernel. Its physical radial realization is separately proved in `radial_green_limit.tex`, theorem `rg:physical-limit`, and the final combination is `uc:counterexample`.

## Exact normalization and kernel

Polarization is P=chi*E; the electric volume response is K0=(k^2 I+grad grad)Phi. It splits as minus the positive longitudinal projection plus an O(1/r) dynamic remainder. Its imaginary kernel J is the entire transverse Herglotz kernel k^3/(16*pi^2) times the sphere integral of (I-theta theta^T)exp(i*k*theta*x).

The electric wall projection acts by W E(x)=-Rz E(Rz*x). The reaction kernel is K_B=K0+(B^2-1)*i*Pi_e J+(B^(-2)-1)*i*Pi_m J. Actual radial gain is B=sqrt(lambda)*t/a, while the prescribed jet amplitude is A=t/a. Keeping these two scales distinct is necessary after the physical Gram balancing.

## Self-consistent sphere equation

The weighted static block I+sqrt(chi) P_long sqrt(chi) is at least I. On the finite union of radius-O(a) spheres, the dynamic remainder has norm O(a^2), and the smooth entire reaction has norm O(B^2*a^3)=O(a). Thus a Neumann series gives a uniformly bounded inverse, source L2 norm O(a^(1/2)), and source L1 norm O(a^2).

The comparison polarization is constant and normal on each sphere, equal to chi*3/(epsilon_p+2) times its prescribed plane electric jet. It solves each isolated static sphere exactly. The background variation on a sphere is O(1), giving L2 residual O(a^(3/2)); intersphere static interaction is O(a^3); dynamic and reaction residuals are O(a^(3/2)). The resulting polarization error has L2 norm O(a^(3/2)) and L1 norm O(a^3), uniformly over all unit coherent coefficient vectors.

## Whole-plane, not local-only, remainder

For sources at height at least c*a, the static plane L1 operator bound is C/a. Its plane L2 Hilbert-Schmidt bound is C*a^(-1/2). The magnetic plane L2 bound on a fixed disk is C*a^(1/2), using the exact planar integrals of r^(-4) and r^(-2). Hence the free electric plane L2 norm is O(1), the free magnetic norm is O(a), and their self-flux is O(a).

The dominant exact normal-dipole trace has L1 norm O(a) and first plane moment O(a^2). The fixed finite-band background has global Lipschitz constant O(1/a), so replacement by its point jet costs O(a), without needing a logarithm. The source error crossed with the background also costs O(a).

The wall reaction field has amplitude O(B^2*||P||1)=O(1), but its tangential E vanishes exactly. The opposite-wall reaction has amplitude O(||P||1)=O(a^2), while its tangential H vanishes. Consequently every remaining near-plane product is O(a) in L1.

All free and regular reaction fields have transverse incoming/outgoing leading spherical amplitudes. On z=0, the cross product of any two leading transverse vectors is radial and has zero normal component. Thus their normal cross-products are O(r^(-3)), with an integrable plane tail. The far-region coefficients are O(A), O(a^2), and O(1) as appropriate, giving O(a) or smaller remainder. This controls the actual absolute normal flux over the entire plane of the explicit-kernel solution.

## Scope and subsequent physical realization

The conclusion is an O(a) whole-plane flux approximation to the exact local profiles, uniform over the unit coefficient sphere. This section alone does not claim finite physical radial realization. The separate theorem `rg:physical-limit` identifies the complete source Green kernel at fixed B and controls the remote annulus/exterior absolute plane flux. Constants here may depend on fixed N, the interpolation geometry and Gram factor, but not on shrinking a. The final theorem `uc:counterexample` preserves the necessary order: choose a, let the remote radius tend to infinity, then select a diagonal sequence a -> 0.

## Independent audit of this section

The channel agent read both the local transducer section and this explicit-kernel section in full. The audit checked the Debye interpolation, exact Gram balancing, positive static block, O(a) reaction perturbation, source residual exponent, normal-dipole first moment, plane Hilbert-Schmidt exponents, wall flux decomposition, and all near/far cross-products. No substantive issue was found. The source-kernel normalization was independently confirmed to match the actual common-stack limit on C2-even sources.

The parent independently read the entire explicit-kernel proof and checked its bounded inverse, source residual, Hilbert-Schmidt exponents, first moment, cross-products and far-field cancellation. No defect was found. The later scope paragraphs now reference the independently audited physical-radius result `rg:physical-limit` and the final construction `uc:counterexample`; the mathematical estimates and constants were unchanged.

## Independent audit of the radial source limit

Read the channel agent's `reviews/radial_green_tail.md` before its global packaging. The exact real-transfer source coefficient gamma=(-c*d-a*b-i)/(a^2+c^2), the identity -Im(gamma)=|gain|^2, the low-order Hankel energy bound, the comparable-order finite-polynomial estimate, the high-order barrier load Re(h)<=0, the Riccati lower bound, and the resulting geometric source tail all check. No substantive local defect was found. On the C2-even source sector, componentwise inversion-even fields are exactly electric-wall fields, since the pi-rotation matrix is -Rz. Hence the radial reaction-kernel normalization agrees with the kernel used here.

For growing-core estimates, the low-order uniform coefficient bound produces angular Herglotz densities bounded in every fixed smooth norm after multiplication by compact-source moments. In the high-order estimates, replacing the fixed observation radius by the inner stack radius leaves one factorial source suppression; the comparable-order and barrier tails remain superexponentially small in that radius. The channel agent further derived the normalized barrier-source values w(R)=1/(h*psi-psi'), with |w(R)|<=1/psi' and |p(R)|<=1/psi. Both |w| and |p| decrease outward through the barrier stack because the same real product Re(p*conj(w)) is nonpositive in both derivative identities. These are concrete estimates for the separate whole-plane physical-radius proof.
