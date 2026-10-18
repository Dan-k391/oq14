# Modal spectral proof audit

The final written theorem is `ms:modal-packing` in
`manuscript/sections/modal_spectral.tex`. It closes the stated QNM version
of finite modal hotspot packing. It does not close the channel conjecture
or claim a positive all-space energy norm for a radiating resonance.

The root agent derived the spectral construction. The hotspot and channel
agents independently reviewed it. They found one substantive presentation
error in the rounding proof: almost-everywhere material convergence gives
operator-norm convergence of the compactly reduced pencil F, not of the
original pencil L. The Schur reduction was changed to use F throughout.
Multiplication by the invertible static factor preserves multiplicities.

Checks completed:

- The dyadic static split retains its distributional local term. The
  remaining O(1/r) kernel is Hilbert--Schmidt on a bounded 3D ball.
- The static inverse uses positivity of `I + sqrt(chi) P sqrt(chi)` for
  any bounded nonnegative contrast. The compact pencil is the identity
  at zero; no small-contrast or imaginary-frequency uniqueness gap remains.
- Strong multiplier convergence, uniformly bounded static inverses and
  compact composition give norm convergence of F under rounding.
- Both tangential transmission conditions give the TM determinant. Its
  two rational exponential coefficients cannot vanish together by the
  Wronskians. Division at a pole is legitimate.
- A repeated root or common root across angular orders would be algebraic
  for algebraic refractive index, contradicting Lindemann--Weierstrass.
  Leading and first inverse-frequency terms distinguish the rational functions.
- Rouché disks give lower-half-plane dipole poles of arbitrarily high Q.
  The regular interior dipole field is nonzero on an axial interval.
- Separated radial matching gives operator simplicity. The invariant
  axisymmetric electric sector removes azimuthal degeneracy. The whole
  unprojected Green residue is not incorrectly called rank one.
- The left functional pairs with chi E without conjugation. Its derivative
  pairing d is nonzero by simplicity. The physical residue is exactly
  `-E tensor E / (2 k N)`, with `N = -k d / 2`.
- This genuine reciprocal norm is finite, nonzero, holomorphic under
  insertion and continuous under rounding. Fixed-interface regularity
  supplies one-sided uniform field convergence away from the tips.
- The local coefficient proof subtracts the constant regular curl lifting
  before taking the exponent to one. Two independent agents checked the
  cancellation and exact nonzero limiting coefficient.
- Dilation scales N by s^3 and normalized E by s^-3/2. Strict margins
  preserve placement, size and peak inequalities at the fixed real frequency.
- Axisymmetry puts an actual maximum in the plane. Its orbit can be a
  small ring contained in the small ball; uniqueness is not asserted.

Reproducible diagnostics check the determinant algebra, inverse-frequency
expansion, nine sample poles and exponent-one cancellation. They corroborate
formulas, not the continuum limits or claims for arbitrary N.

This is independent checking within an AI-assisted investigation, not human
peer review. The continuum modal theorem is not yet a Lean theorem. No
project axiom conceals Fredholm, interface or resonance arguments.
