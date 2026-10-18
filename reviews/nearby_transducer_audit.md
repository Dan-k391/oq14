# Nearby positive-dielectric transducer audit

Status: exact local results proved. The physical bridge initially isolated here was subsequently discharged in `channel_transducer_limit.tex` and `radial_green_limit.tex`; the final fixed-threshold counterexample is `uc:counterexample` in `channel_unrestricted.tex`. This review retains the chronological failure analysis below. Local manuscript source: `manuscript/sections/channel_transducers.tex`, labels `ct:*`.

## Exact edge mechanism

A radius rho*s positive-dielectric sphere at height h*s, h>rho, driven by a normal electric jet A*e has static dipole moment epsilon0*alpha*s^3*A*e, where alpha=4*pi*rho^3*(epsilon_p-1)/(epsilon_p+2). Its tangential electric trace crossed with a constant magnetic jet A*b in the edge-tangent direction gives

`f(s*xi,s*upsilon) = -3*alpha*h*A^2*Re(e*conj(b))*xi / [8*pi*(xi^2+upsilon^2+h^2)^(5/2)]`.

For positive Re(e*conj(b)), the interior half-plane has positive flux and the exterior has negative flux. Both half-plane absolute masses equal `s^2*A^2*alpha*Re(e*conj(b))/(4*pi*h)`. The total signed plane integral is exactly zero. The manuscript derives the static sphere polarizability and both integrals directly. This is an exact electrostatic cross-term, not a full nonzero-frequency Maxwell solution or an admissible impressed-dipole construction.

## Coherent finite-rank jets and physical power

Even-l, even-m regular TE fields have the electric-wall plane parity E_t=H_z=0. Their plane flux is identically zero for all coherent combinations. The Debye representation E=curl(x*u), H=curl(E)/(i*omega*mu0), with scalar u even in z and under planar inversion, gives independent E_z,H_x,H_y jets at every finite set of nonzero, non-antipodal plane points. A direct exponential-polynomial argument proves tangential scalar two-jet surjectivity; smooth angular approximation and a finite spherical-harmonic truncation retain exact finite-jet surjectivity. This needs no global Runge assertion.

The interpolation Gram matrix is balanced exactly: add zero-jet vectors from a sufficiently enlarged finite-band kernel, orthogonal to the original interpolants, with Gram matrix lambda*I-G. After division by sqrt(lambda), the incoming data are physically orthonormal. A common amplified core multiplier A*sqrt(lambda) then restores the desired jets. This removes condition-number losses from the passage/bypass ratio for every coherent vector, even though lambda may depend strongly on N.

Place N centers on the interior of the right square edge and their C2 partners on the left. E_z is unchanged and H_t reverses under the pi rotation, exactly matching the reversal of the local outward normal and tangent. Both sides therefore contribute positive interior flux. With s=a/k0 and A=t/a, the ideal model has passage and absolute bypass tending uniformly on the unit coefficient sphere to p0=alpha*t^2/(2*pi*h). Disjoint fixed disks and the O(R^-2) scaled L1 tail prove uniformity; this is not a basis-only calculation.

For any one fixed tuple 0<tau<1 and 0<eta<delta, choose eta<p0<delta. If exact perturbed physical fields converge to that profile in whole-plane L1 flux, the full unitary scattering output map gives throughput one, and the N-dimensional space is counted. The manuscript states this as a conditional proposition with the exact missing estimate displayed.

## Bridge originally left open, then discharged separately

Finite-band incident gains are not interior-source Green bounds. The background amplification grows as 1/a while particle volume is O(a^3); an isolated finite-dimensional estimate suggests the feedback parameter volume*gain^2=O(a), but this cannot hide the dependence of a device inverse on radius, gain, and unselected angular orders. The electrostatic sphere formula does not itself control the small-inclusion expansion in such a changing background. Full-plane absolute flux, including remote material layers, must also be bounded. Neither local field convergence nor signed far-field power conservation gives that estimate.

The C2-even sector prevents coupling to odd-m degeneracies at a fixed l. The paired TE/TM construction amplifies electric-wall responses and suppresses the opposite wall sector within any controlled finite band. Taking an individual finite-device inverse as a generic constant would leave a circular choice of particle radius and gain. The later common-stack source proof resolves the previously uncontrolled high orders by exact source-coefficient estimates, centrifugal-barrier monotonicity and factorial/geometric tails; the explicit-kernel proof resolves feedback by the positive static inverse and an O(a) perturbation.

Axisymmetric electric-wall TE alone is insufficient for this particular normal-dipole mechanism: its E_z vanishes. The off-plane tangential electric jet generated to first order by a constant H_t is reactive, and the leading real cross flux cancels for an isotropic sphere. Nonaxisymmetric even-m fields avoid this restriction. An axisymmetric torus alternative spreads its response around a whole circle; the square's interior angular fraction changes only by a vanishing amount across a shrinking radial lobe, giving a vanishing useful passage/bypass ratio. Neither route supplies the needed counterexample.

## Independent paired-control audit

Read `manuscript/sections/channel_dual_control.tex` in full. The TE/TM reference propagators satisfy U_TM=U_TE^(-T); the actual TM angular interaction includes the necessary n^(-2) factor. The quarter-wave integrals give B_TM=-B_TE^T with the same integrated norm b_M+d_M and the same finite-radius error constants. The map G -> (G,G^(-T)) is a homomorphism, so the finite-ensemble control closure argument applies on that graph. The common phase and even/odd physical gain pattern are correct. The C2 and electric-wall reflection classification is correct. No substantive defect found. This agrees with the parent's independent audit.

## Potential next estimate; not yet proved

The parent identified a useful exact triangular splitting of the long identity loops. In the TE interaction matrix, the lower entry accumulates O(nu), while the integrated upper and diagonal entries are O(nu*q^(-2M)) and O(nu*M*q^(-2M)). Solving the lower-only equation exactly before perturbation may yield a polynomial transfer bound for a growing low-order range, without exp(C*nu). A balanced diagonal conjugation controls an intermediate range; factorial small-core Bessel decay may dominate the remaining transfer constants. To be useful, this must bound the actual material Green coefficients and their plane traces, not merely finite-band incident transfers. No such uniform source estimate has yet been recorded as a theorem.

## Independent audit of the new local section

The parent read the complete `channel_transducers.tex` section and independently verified the electrostatic polarizability, edge orientation, half-plane mass, scalar-jet Fourier-dual argument, Debye jet formulas, finite-TE approximation, physical Gram balancing, and uniform L1 profile limit. No substantive issue was found. The conditional completion statement correctly retains the actual whole-plane Maxwell remainder as a hypothesis. The section is frozen at this local scope.

## Subsequent simplification and its completed proofs

Only a common wall gain is needed after Gram balancing. The parent therefore replaced the independently tunable angular control route by an ordinary finite high-low quarter-wave stack with reference transfer diag(A,A^(-1)), A=q^M. For each fixed A its thickness is O(log A), independent of its radius. The subsequent proved result `rg:physical-limit` identifies the explicit parity-modified core Green kernel, controls all source angular orders, and proves whole-plane physical flux convergence. The result `cl:remainder` proves the O(a) self-consistent inclusion and plane-flux error for that kernel. Their diagonal combination is `uc:counterexample`. The construction uses delta>eta and the full unitary scattering output; it does not settle a reformulated small-bypass or restricted-output claim.
