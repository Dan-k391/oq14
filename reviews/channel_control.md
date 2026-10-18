# Global finite-order TE transfer control

Owned files: manuscript/sections/channel_control.tex and this review. No Git operations. The earlier channel_global.tex is frozen.

## Concrete claim

For any finite set of distinct TE angular orders and any tuple of real determinant-one transfer matrices, finite radial scalar dielectrics with 1 <= epsilon <= q² < epsilon_plus approximate that tuple as their starting radius R tends to infinity. Their total thickness is o(R). No absolute thickness, support, layer-count, or accuracy bound uniform in the target is asserted. This is actual radial Maxwell transfer control, not a network-model assumption.

The identity loop is a high-low quarter-wave stack followed by its reverse-order inverse. Its reference endpoint is I. Its first angular derivative is exactly B_M = [[0,-d_M],[b_M,0]], with b_M = pi*(q²+1/q)*(q^(2M)-1)/(2*(q²-1)), d_M = pi*(1+1/q)*(1-q^(-2M))/(2*(q²-1)), and d_M/b_M = q^(-2M)/(q²-q+1). The integrated conjugated angular-generator norm is exactly b_M+d_M <= 2*b_M.

For an actual loop starting at r, the error beyond its linear angular term is <= 4*nu*ell_M*b_M/r³ + 2*nu²*b_M²*exp(2*nu*b_M/r²)/r^4. Taking M=floor(a*log_q R), 1/2<a<1, and K=floor(t*R²/b_M) loops gives exp(t*nu*Y) simultaneously. The manuscript supplies an explicit finite-R accumulated-error bound. Thickness is O(R^(2-2a)*log R)=o(R).

Common SL(2,R) matrices follow from positive-length vacuum rotations and quarter-wave diagonal squeezes at bounded index. Positive angular shears and their J-conjugates give a simultaneous rotation with integer frequencies nu=l(l+1). Its period provides signed rotation times; another product formula supplies inverse shears. Vandermonde commutators separate the finite orders. An open-subgroup/IFT argument gives the whole finite product group. Diagonal selection of actual radial structures justifies closure of asymptotic realizability.

## Verification and limitations

Independent adversarial review by the hotspots agent passed: loop integrals and exact diagonal cancellation; integrated interaction norm; one-loop, radius-freezing, and telescoping constants; the strict exponent range 1/2<a<1; semigroup closure and concatenation; positive-length inverse generation using integer frequencies; Vandermonde algebra and group openness; and physical gain/phase extraction were all checked. No substantive defect was identified. No physical bypass claim follows from endpoint control. Fields in the control layers can be large; their absolute normal flux outside D needs a separate estimate.

The root agent independently checked the same loop constants, errors, closure and signed-shear generation, Lie/open-group argument, target determinant, and exterior complex phase, also without identifying a substantive defect. The corollary now explicitly says that field and derivative convergence occurs after removing the common phase. The mathematical source is frozen after both audits.

The theorem concerns TE transfers only. It does not assert independent TE/TM control, fixed support, exact finite-device target attainment, or unrestricted OQ14 closure.

The physical corollary cc:core-gains selects starting radii 2*pi*n and target matrices taking the limiting regular state to any nonzero real vector. Exterior Hankel extraction yields any prescribed finite tuple of nonzero complex TE core multipliers up to one common phase. Thus the reciprocal electric-parity pattern of the common stack is genuinely overcome. All coherent fields converge on fixed compact core subsets, but whole-plane bypass is still a separate requirement.

## Independent audit of the new bandwidth obstruction

Read manuscript/sections/channel_bandlimited.tex in full. Its elementary outside-interval L1 observation estimate has correct node spacing, Lagrange sum, complex divided-difference remainder, and absorption constant. The planar slice argument, compact Fourier support of quadratic flux, pointwise Fourier bound, point-flux rank, finite positive-trace count, fixed-band O(r^-3) plane-flux tail, and finite-core absorption are valid as written. No field-energy bound is assumed. The finite-band radius threshold may depend on the band, while the resulting dimension count does not. This is a real obstruction to completing the far-away radial control construction in its asymptotic finite-band regime; it is not an obstruction to arbitrary nearby-material designs.
