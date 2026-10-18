# Renewed finite-three-dimensional hotspot audit

Canonical mathematical source: `manuscript/sections/hotspot_closure_audit.tex`. This file records review and scope; it is not an alternative manuscript.

## New result

**PROVED, hs:three-packing:** A finite three-dimensional binary dielectric device, using one fixed small positive contrast permitted by the original upper material bound, has any prescribed finite number of arbitrarily high electric peaks under one unit-total-incoming-power illumination. Each peak has a separate arbitrarily small three-dimensional neighborhood with a low-field collar. The neighborhood centers lie in a prescribed plane patch, and their orthogonal projections lie in that patch. Rounded peak maxima are not asserted to lie exactly in the same mathematical plane.

This advances the earlier invariant construction: the new inclusions have genuine conical point tips in the sharp reference geometry, and the completed device is finite in every direction with smooth interfaces. No finite-height approximation of the invariant device is used.

**OPEN, hs:three-modal-gap:** Simultaneous packing by one normalized quasinormal resonance is not established. The external illumination chosen by Runge cannot be replaced by a homogeneous resonance eigenfield. Resonance continuation, nonzero coefficients at all selected tips, and a finite nonzero chosen QNM normalization remain to be proved.

**PROVED diagnostic, hs:three-no-real-mode:** A compact, positive, piecewise homogeneous dielectric has no nonzero real-positive-frequency source-free finite-all-space-energy Maxwell mode. This rules out an inappropriate literal normalization; it does not refute the tutorial's high-Q or open-resonator interpretation.

## Decisive analytic checks

1. **Point singularity at strict positive contrast.** The weighted angular operator on the sphere has a positive eigenvalue below two. The trial function is the axial coordinate, and the two polar caps have enhanced positive permittivity. The exact Rayleigh quotient is `[2+d(2-3t+t^3)]/[1+d(1-t^3)]`; subtracting two gives `-3dt(1-t^2)/[1+d(1-t^3)]`. The indicial exponent therefore lies strictly between zero and one. Static energy scales as `lambda R^(2lambda+1)`, so the point singularity is integrable.

2. **Exact finite-frequency coefficient.** A regularized curl lifting writes the electric field as a scalar gradient plus a bounded H2 remainder. The weighted divergence equation gives an exact forced radial equation for the spherical projection. Integration by parts yields hs:three-exact with only bounded forcing moments A and B. The particular solution and its derivative are O(r) and O(1), respectively. Finite H1 energy excludes the negative indicial power. Annular averaging proves coefficient continuity, and changing the lifting changes only a Lipschitz potential, hence cannot change the singular coefficient.

3. **Constant-lifting consistency check.** For W=a constant and v=-a dot x, the eigenproblem gives B=lambda(lambda+1) A. The particular formula then equals `-r A` and the coefficient is zero. This checks both signs and the cancellation required for independence of lifting.

4. **Local Maxwell completion.** The static conical gradient is completed at a small but positive scaled frequency by a coercive solve on the weighted-divergence-free tangential-zero space. A weighted Helmholtz decomposition reduces its Maxwell inequality to the ordinary ball estimate. The correction is O(kappa^2) in H(curl), and its curl is O(kappa^2) in interior H1 by the constant-permeability curl/div estimate. The lifted remainder is consequently O(kappa^2) in H2, proving the singular coefficient is `1+O(kappa^2)`. Bare L2 approximation to a singular static field is not used as a substitute for coefficient continuity. The local tangential boundary problem is only a mathematical construction; the physical device has no conducting wall.

5. **Outgoing finite-device problem.** The dyadic volume kernel is split into the distributional static Hessian, whose full-space Fourier multiplier has norm one, and a locally integrable Helmholtz remainder. This includes the singular distributional diagonal term. Small fixed contrast gives a geometry-independent Neumann inverse on a comparison ball of radius `1/k`. The material contrast can be kept fixed as N, rounding and patch size vary.

6. **Global illumination and normalization.** Total-field Maxwell Runge uses an outgoing electric source solution, Lorentz reciprocity against all transverse plane-wave polarizations, vanishing electric far field, and unique continuation across constant-material interfaces. Local coefficient continuity then gives one nonzero functional per tip; the finite-union-of-kernels argument selects one illumination. The spherical Herglotz prefactor is `k sqrt(Z0)/(sqrt(2) pi)`, yielding incoming electric amplitude `sqrt(2 Z0) g(-direction)/r` and total incoming power `||g||^2`.

7. **Rounding.** Coefficients converge almost everywhere with the same small contrast. The exact volume-inverse difference identity gives strong electric L2 convergence. In an unchanged collar, local Maxwell regular decomposition and the scalar positive transmission problem give a piecewise H3 potential estimate and hence uniform one-sided electric-field convergence. These estimates use only fixed smooth interfaces away from the moving tips. One common rounding scale preserves all large ordinary-point values and all low collar bounds. The same normalized input is retained.

## External analytic dependency

The only new named analytic tool is the regularized Poincare curl lifting of Costabel and McIntosh, *Mathematische Zeitschrift* 265 (2010), 297–320, DOI `10.1007/s00209-009-0517-8`. The author's primary PDF at `https://costabel.perso.math.cnrs.fr/publis/PoiBogdeRhv2.pdf` was read. Its homotopy identity and order-minus-one Sobolev mapping give the precise ball operator used here. This establishes the local lifting, not any of the newly derived scattering, conical excitation, simultaneous packing, or rounding claims.

Standard scalar elliptic regularity on a smooth ball/interface is used in the explicit local estimates. The manuscript explains the tangential-difference-quotient and normal-derivative steps. No unproved general Maxwell shape-convergence theorem is imported.

## Independent reviews and corrections

The root reviewer checked the conical projection formula, normalization and uniform inverse chain. The independent channel reviewer checked the angular Rayleigh argument, exact projected particular solution, coefficient continuity and independence, PEC correction, volume inverse, Herglotz normalization, bilinear total-field Runge, and fixed-interface H3 rounding. Both identified the same wording correction: zero outgoing radiation follows from the **real** part of the complex Poynting identity, not its imaginary part. That correction is incorporated. Physical units are explicitly restored before the global illumination formula.

The ordinary-ball Maxwell estimate was expanded to avoid assuming H1 membership: first use the lifting from L2 to H1, then scalar boundary regularity for the remaining potential, then the Gaffney identity and the tangential-trace Poincare estimate.

The independent counterexample reviewer also found no substantive gap after checking the conical Rayleigh quotient, exact forcing signs, weighted local correction, lifting mapping (including the primary source's Corollary 3.4), the volume kernel's distributional diagonal, fixed contrast, source Runge argument, physical input normalization, and fixed-interface rounding. It requested that the Runge approximation set Q be explicitly restricted to the comparison ball, so the source inverse is applied exactly within its established domain. That restriction is now in hs:three-runge; every set used in the packing proof already satisfied it.

## Independent renewed channel audit

Read-only review of `manuscript/sections/channel_closure_audit.tex` found no substantive defect. The six curl-equation signs in the Cauchy construction were checked directly. The bounded transverse Fourier supports give smooth finite-energy fields on every fixed slab. The sinc escape estimates, disjoint spectral shifts, coherent Cauchy–Schwarz factor, and local resource lower bound are correct. The global half-space power budget is valid with the stated integrable-plane-flux and radiation hypotheses. Exact compact-exterior noncompletion correctly uses equality on the entire open slab, vacuum unique continuation, and exclusion of growing evanescent fields; it does not exclude controlled approximate resonant realizations.

## Formalization boundary

The new continuum proof has not been formalized in Lean. Formal finite-dimensional lemmas do not constitute formal verification of its Maxwell lifting, weighted angular spectrum, local variational solve, volume integral, Runge, or interface regularity steps. No full-original-OQ14 formal closure is asserted.
