# Counterexample-track audit

Status: fixed-frequency ordinary-dielectric, fixed-section channel target OPEN.
Owner: counterexamples agent. Canonical mathematics is only in
`manuscript/sections/counterexamples.tex`.

## Frozen scope

- Scalar real `1 <= eps_r <= eps_plus`, common fixed `eps_plus > 1`, vacuum exterior.
- Same physical section D, fixed positive frequency and thresholds tau, eta, delta.
- Support and Q may grow; no imposed internal sources, conducting partitions, or hidden ideal impedances.
- Physical input/output modes require power normalization; all passage/bypass conditions apply to every coherent vector.

## Claims and status

| Label | Status | Result / limitation |
|---|---|---|
| cx:bragg | PROVED | Exact full vector Maxwell amplification in radial bounded dielectric, one reflected incoming spherical channel; support grows. Extends prior report from q=2 to every eps_plus>1. No throughput counterexample. |
| cx:evanescent | PROVED local Maxwell | Arbitrarily large positive local flux spaces in a fixed collar, including zero sidewall real flux. Global normalized excitation and outside-D bypass absent. |
| cx:mirror-network | PROVED scattering model | Exact reciprocal lossless feedback compensates arbitrary weak links. Physical fixed-section synthesis absent. |
| cx:pair-solution | PROVED ODE model | Exact t, r, energy, internal current, pole and FWHM expressions. |
| cx:pair-sensitivity | PROVED ODE model | Quantified detuning, rate mismatch and parasitic loss thresholds. |
| cx:n-model | PROVED matrix model | N perfectly transmitted modes and weighted perturbation certificate. |
| cx:compression | PROVED operator lemma | Physical compression near unitary yields N efficient inputs; requires actual physical maps and flux data. |
| cx:absolute-bypass | PROVED sufficient certificate | Integral of pointwise flux matrix operator norms controls absolute bypass for every vector. Requires legitimate integrable traces. |
| cx:coherent-failure | DISPROVED shortcuts | Basis fields and signed integrated flux alone cannot certify coherent passage/absolute bypass. |
| cx:angular-obstruction | PROVED restricted radial lemma | No real-core Dirichlet/Neumann endpoint resonance above centrifugal threshold; no general open resonance exclusion. |
| cx:missing-bridge | OPEN | Simultaneous Maxwell realization, common-frequency tuning, relative-error control and fixed-section absolute bypass. |

## Audit of the prior report

Read extracted prior report lines 738–1010. The radial exact solution checks:
TE equation, continuity of u and u', low/high quarter-wave matrix order,
Wronskian sign, incoming power, derivative magnitude and energy growth all
agree. Incoming normalization determines the large core amplitude; no free
trapped-mode amplitude is inserted. Complete spherical net flux is zero.

The local positive-flux construction is exact vector Maxwell inside its
collar. It does not realize external channels. Sidewall real-flux vanishing
does not impose physical material sidewalls or prove absolute plane bypass.

The exact mirror network is a valid counterexample to an isolated-link-only
proof, not a construction of admissible fixed-section Maxwell structures.

The ENZ/variable-aspect-ratio guide is explicitly outside the frozen target:
lower bound, shape, background, and infinite-support conventions change.
No strengthening to the present class is claimed.

## Reproducible algebra diagnostics proposed to the coordinator

For N = 2,4,8 choose J_j = 10^(-j), gamma_j=J_j, common omega0=1.
At zero detuning the exact outputs are T=-iI, R=0, sigma_min(T)=1;
energy Gram is diag(1/J_j), model exchange-current Gram is I, FWHM_j=2sqrt(2)J_j.
These are model diagnostics and must not be labeled Maxwell section/bypass data.

For an adversarial mixed perturbation choose any explicitly specified
Hermitian H with norm <=1, F=i*rho*H, A=G(B0+F)G. This is a lossless
Hamiltonian perturbation: A+A*=2G^2. Full scattering S=-I+2G A^-1 G
must be unitary; transmission must satisfy the certified error bound
rho/(1-rho/sqrt(2)). A real symmetric H preserves the displayed reciprocal
port convention. Check the full spectral norm, not random test vectors.

Physical minimal transmission, section-flux Gram and absolute-bypass bound
are not available for these models; record them as unavailable, never zero.

## Sources checked

- Prior report supplied in project, cited as `priorreport`.
- Fan, Suh, Joannopoulos, JOSA A 20,569–572 (2003), DOI
  10.1364/JOSAA.20.000569; author-hosted primary paper:
  https://web.stanford.edu/group/fan/publication/Fan_JOSAA_20_569_2003.pdf
  Used only for the normalization/conventional-model context; proofs are explicit.
- Suh, Wang, Fan, IEEE JQE 40,1511–1518 (2004), author-hosted primary paper:
  https://web.stanford.edu/group/fan/publication/Suh_IEEEJQE_40_1511_2004.pdf
  Energy-conservation constraint between decay and port couplings checked.

## Physical construction outcomes

Radial Bragg cavities establish unbounded amplification, not transmission
multiplicity. High-angular-order centrifugal compensation exceeds fixed
eps_plus at a fixed inner radius. Enlarging the radius is allowed but loses
the asserted link to the original section; no general impossibility follows.

Planar Bragg structures give exact one-dimensional resonant matching but
have infinite transverse support and plane-wave power per area. Finite
truncation requires a new relative leakage and diffraction estimate.

Large remote resonators with fine tips might evade a naive local cutoff.
No proof has established common-frequency tuning, independent matching,
relative error below the weakest link, and all-superposition bypass together.
Failure to build this family is not an impossibility theorem.

## Independent review of the hotspot track

Read `manuscript/sections/hotspots.tex` in full after the first complete
proof was written. Independently checked the TM sign convention,
Herglotz stationary-phase incoming power, checkerboard transfer trace and
exponent, inhomogeneous radial projection sign, coefficient continuity,
finite-frequency small-disk construction, outgoing-source Runge duality,
finite-union simultaneous excitation, varying-coefficient inverse stability,
and fixed-collar one-sided convergence under rounding.

No substantive mathematical gap found in the restricted 2D driven theorem.
The Dirichlet-to-Neumann Garding paragraph's phrase "finite lower bound"
must read "finite upper bound" for real multiplier parts; root and hotspot
agent were notified. An optional explicit derivative estimate for the
projection particular solution was sent as rigor polish. The claimed
finite-3D and modal extensions remain correctly OPEN. This review is a
human-readable mathematical audit, not formal verification.

The channel-track agent independently reviewed this counterexample section
and found no substantive errors. Its requested regular radial derivative
asymptotic was justified explicitly using the transformed radial equation.
