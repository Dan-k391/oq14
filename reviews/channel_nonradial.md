# Nonradial, unrestricted-support channel attempt

## Scope and current verdict

The frozen target permits real scalar `1 <= epsilon_r <= epsilon_plus`, constant permeability, arbitrary finite three-dimensional material support, fixed real frequency and fixed square section, physical incoming power, a positive throughput threshold, a signed section-passage threshold, and an absolute bypass constraint for every coherent input in a counted subspace. Total material volume, enclosing radius, quality factor, and feature scale are unrestricted.

**The unrestricted target remains open.** This attempt proves a new uniform physical response and channel theorem under an explicit small-total-volume restriction, with no diameter, separation, number-of-pieces, or feature restriction. The complete proof is in `manuscript/sections/channel_nonradial.tex`, labels `nr:kernel` through `nr:channelcount`. This is a genuine additional restricted result, not a reinterpretation of the original quantifiers.

## New exact estimate

Write `chi=epsilon_r-1`, `0<=chi<=C`, let the material volume be `V`, and let `a=(3V/(4 pi))^(1/3)`. At real wavenumber `k`, split the exact outgoing Maxwell volume operator as `K=-P+R`, where `P` is the whole-space longitudinal orthogonal projection. The dynamic kernel has the pointwise bound

    ||R(x)|| <= 3 k^2/(8 pi |x|).

This bound is valid at every distance, not only for a small-diameter object. To prove it, set `z=k|x|` and `Cz=e^(iz)(1-i z)-1`. Its tangential and radial eigenvalues are respectively `(z^2 e^(iz)-Cz)/(4 pi |x|^3)` and `2Cz/(4 pi |x|^3)`. The identity `Cz'=z e^(iz)` yields `|Cz|<=z^2/2`. The singular distributional static contribution is already in `-P`; no diagonal term has been omitted.

Decreasing-kernel rearrangement gives `sup_x int_Omega |x-y|^(-1)dy <= 2 pi a^2`. In the weighted polarization equation

    (I + sqrt(chi) P sqrt(chi) - sqrt(chi) R sqrt(chi)) j
        = sqrt(chi) e_inc,

the static factor is at least the identity and the dynamic factor has norm at most `t=(3/4) C (k a)^2`. For `t<1` a geometric-series inverse gives `||j|| <= ||sqrt(chi)e_inc||/(1-t)`. This uses neither a Born truncation nor a lower contrast bound.

## Physical normalization and complete field resource

The manuscript uses transverse Herglotz incoming amplitudes `g` with physical incoming power `||g||^2`, including the explicit prefactor `k/(pi sqrt(2 c0))` for normalized electric and magnetic fields. The incident pointwise bound is `k sqrt(2/(pi c0)) ||g||`. The weighted inverse therefore bounds the polarization norm by `P_V ||g||`, with `P_V=C k sqrt(2V/(pi c0))/(1-t)`.

For any fixed observation set `U`, with equal-volume radius `b`, cross-set Schur bounds give

    ||R: L2(Omega)->L2(U)|| <= (3/4) k^2 a b,
    ||curl Phi_k: L2(Omega)->L2(U)||
        <= sqrt((a+k a^2/2)(b+k b^2/2)).

Together with `||P||=1`, these bound both complete physical fields in `U`. Thus the uniform local resource needed by the prior full-vector channel theorem is actually discharged for this class. The resulting channel count retains the required `delta < eta tau` and plane-trace compatibility hypotheses. It applies to all coherent inputs, including their reflected and evanescent fields.

The same polarization estimate yields a power-normalized outgoing scattering difference from vacuum of at most `C k^3 V/(2 pi (1-t))` in operator norm. This is an optional additional conclusion, not a surrogate for the section/bypass proof.

## Attempted unrestricted nonradial constructions and exact failure points

1. **Many remote resonators weakly coupled to a common microscopic region.** Near-degenerate resonances and independently accessible radiation directions do not establish a well-conditioned power-normalized map into the same fixed section. Their remote radiative tails are not the large fields inside each resonator. A matching structure must convert those directions into the desired section profiles while controlling the whole-plane absolute bypass. The necessary simultaneous singular-value and coherent-bypass estimate has not been obtained. The new small-volume theorem now rigorously excludes one subclass of such attempts: keeping the total bounded-contrast material volume sufficiently small while spreading it over arbitrary distances.

2. **Tiny dielectric corner or gap terminals attached to large resonators.** Electric point peaks alone do not supply a finite integrated power channel. An electric conical singularity proportional to `r^(lambda-1)` multiplied by a bounded magnetic factor has disk-integrated flux of order `r^(lambda+1)`, which vanishes with the disk radius. Increasing resonant amplitude can offset this local factor only together with a proof that it does not spoil the bypass ratio or coherence conditions. The completed hotspot proof does not provide those estimates.

3. **Abstract passive feedback completion of local evanescent profiles.** Algebraic unitary or passive circuit synthesis does not constitute a scalar bounded-positive-permittivity Maxwell realization. The missing step is conversion of propagating power channels into a prescribed finite family of very large transverse-wavevector boundary profiles, with quantitative suppression of unwanted plane flux. Existing electromagnetic circuit universality relies on constitutive regimes outside this class, as documented in `reviews/channel_global_attempt.md`.

4. **Weak subwavelength gratings or remote Bragg matching.** Weak high-transverse-frequency conversion can be nonzero but arbitrarily inefficient. Suppressing the direct low-transverse-frequency bypass below the tiny conversion while retaining fixed positive material bounds requires a quantitative simultaneous construction. A Bragg barrier may suppress the desired evanescent field even faster; a propagating stop-band estimate alone does not prove the required matching result.

5. **A proof from magnetic ellipticity and measured flux alone.** The existing local packet constructions already allow arbitrary finite-dimensional local spaces with positive section flux, small bypass, and increasing local field resource. Consequently a proof must use global radiation accessibility, not only the local Maxwell system and measured quadratic flux. The new weighted static inverse provides this missing physical-input estimate only when its dynamic remainder is small in norm. For large unrestricted material volume it supplies no replacement bound.

## Interpretation and safeguards

- The result is for real measurement frequency. Extending the kernel estimate to outgoing complex resonances would incorrectly discard exponential growth with distance. No diameter-independent complex resolvent estimate or pole exclusion is claimed.
- Small total volume is distinct from small enclosing diameter. The bound genuinely allows many disconnected pieces arbitrarily far apart, but their volume sum must obey the stated cap.
- The field-resource estimate is in `L2`, and therefore does not contradict unbounded pointwise electric hotspots.
- The inverse bound degenerates as `t` approaches one. Failure of this sufficient estimate at larger volume is not failure of physical well-posedness.
- No arbitrary-network equivalence, nonzero-coupling threshold substitution, or all-superposition bypass omission occurs in the proved result.

## Independent audit

The counterexample reviewer independently checked the exact radial/tangential dynamic kernel, its constants, the rearrangement and Schur estimate, and the coercive weighted static inverse. No defect was found. The reviewer specifically required the real-frequency restriction, which is explicit in the theorem and final scope remark. The root reviewer independently checked the complete section, including physical incoming normalization, the cross-set magnetic bound, the full resource constant, and the far-field scattering constant; no substantive defect was found. The complete normalization and resource calculation were also sent back to the counterexample reviewer for a second check.

Read-only independent review of `manuscript/sections/channel_global.tex` checked its vacuum Hilbert--Schmidt and positive-trace constants, both TE/TM reference transfer products, electric inversion parity, the amplified Volterra error estimate, physical normalization of the exterior coefficient, and the exact opposite-parity cancellation. The lower energy prefactor `16 Z0/25` and pointwise zero plane flux for all coherent odd-TE axisymmetric combinations also check. Minor TeX/azimuth-label cleanup was reported; no substantive mathematical defect was identified. This radial result genuinely supplies arbitrary-rank physical field amplification but, as its author states, its simultaneous parity pattern cancels the gain in centered-section signed flux.

## A further route examined after the estimates

One possible way around the radial parity cancellation would be a finite-order scattering-phase synthesis theorem that simultaneously rotates the regular TE and TM states into the contracting directions of a common outer mirror. The existing local inverse-function theorem gives only a neighborhood of the current finite coefficient vector. It does not justify a path through a phase change of order one, much less a path retaining arbitrarily large simultaneous gain. The determinant constraint on a common large-radius radial transfer matrix is precisely why the current stack amplifies one electric parity and suppresses the other.

A targeted search of primary inverse-scattering work did not produce the needed bounded-positive-dielectric realization. [Ramm's fixed-energy phase-shift paper](https://arxiv.org/abs/math-ph/9911033) concerns uniqueness from a subset of phase shifts. [Daudé and Nicoleau](https://arxiv.org/abs/1502.02276) prove uniqueness and localization statements for radial Schrödinger potentials. [Pálmai and Apagyi's constructive study](https://arxiv.org/abs/1111.6009) analyzes a scalar inverse scheme, with a one-phase-shift result and numerical two-phase examples. None of these stated results supplies arbitrary simultaneous TE/TM Maxwell gain with scalar permittivity confined to the fixed positive interval, compact support, and the coherent absolute-bypass bound. This is a limited source check, not an impossibility claim.

## Formalization scope

The proof introduces analytic continuum estimates beyond the existing finite-algebra Lean checks. Its positivity and geometric-series algebra could be separated for formalization, but neither that algebra nor the already checked channel count would formalize the Fourier projection, Maxwell volume representation, kernel estimates, or scattering normalization. No complete Lean verification is asserted here.
