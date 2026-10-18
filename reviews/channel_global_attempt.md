# Focused global-channel attempt: finite-rank resonance subtraction

## Scope and verdict

This attempt uses the frozen target in `manuscript/sections/problem.tex`: one fixed square and frequency, bounded real scalar positive permittivity and constant permeability, physical incoming-power coordinates, selected outgoing power, positive signed passage through the square, and an absolute-flux bound on its entire planar complement, all for every coherent vector in a counted subspace. Exterior support, quality factor, and feature scales remain unrestricted.

**The unrestricted channel conjecture is still not proved or disproved by this attempt.** A new exact reduction is proved below. It explains why the completed arbitrarily-many-hotspots theorem cannot be converted into arbitrarily-many-channels merely by increasing the gain of its one resonance. It also isolates a stronger simultaneous-resonance construction that would actually be needed. This is an additional obstruction to a proposed route, not a claim that large quality factor is harmless in every geometry.

## PROVED: a finite number of resonant input directions adds only that many counted directions

Let H be the physical incoming Hilbert space. Let F map an input to its complete electric and magnetic fields needed for the section and bypass measurements, and let T be the selected outgoing map. Suppose there are linear maps F0, T0 and a finite-dimensional coefficient map C:H→C^r such that

    F = F0 + V C,
    T = T0 + U C.

These are exact equalities, not a small-error approximation. The component maps need not individually be realizable by a separate passive device. Assume each measurement used below exists on the input vectors under discussion. Define “counted for (F0,T0)” using the same three inequalities and the same physical input norm as for (F,T). If every such background counted subspace has dimension at most K, then every counted subspace W for (F,T) has

    dim W <= K + r.

**Proof.** Put W0=W∩ker C. Rank-nullity on any finite-dimensional subspace of W gives dim W0≥dim W−r. On W0 the fields and selected outgoing amplitudes agree exactly with their background values. Hence the transmission, signed passage, and entire absolute-bypass inequalities are inherited without any error estimate. Therefore W0 is counted for (F0,T0), and dim W0≤K. If W were infinite dimensional, apply the same argument to finite-dimensional subspaces of arbitrarily large dimension. This proves the claim.

The essential conclusion is codimension r, not 2r. A direct rank estimate on the difference of quadratic flux matrices would normally lose an extra factor because of background–resonance cross terms. Taking the common kernel of the *linear excitation map* avoids that loss and handles the nonlinear absolute-bypass measurement automatically.

The background count K must actually be proved. It is not supplied by this lemma. In particular, analytic dependence of a background resolvent for each device does not make K uniform over devices.

## Exact applicability to the ordinary-dielectric Maxwell resolvent

The already proved volume pencil gives, in a ball B containing the material,

    L_chi(k) = I - K(k) chi,
    chi = epsilon_r - 1,
    K(k) = -P + R(k).

The static factor is boundedly invertible for bounded nonnegative chi, and the dynamic remainder is compact analytic. Thus, on a complex frequency neighborhood containing finitely many simple poles and the real measurement frequency k0, the inverse can be written exactly as

    L_chi(k)^(-1) = B0(k) + sum_j R_j/(k-k_j),

where B0 is analytic and each residue R_j has finite rank. For a simple pole in a symmetry sector, its residue has rank one. Factor the total principal part at the fixed real frequency as V_B C_B; its rank is at most the sum of the residue ranks. The incident-field map I(k0):H→L2(B)^3 gives C=C_B I(k0). No physical incoming amplitude has been rescaled.

There is an important whole-plane subtlety. One must **not** subtract globally continued QNM eigenfields evaluated at their complex frequencies from the real-frequency total field. Those QNMs grow at spatial infinity and can spoil the very flux integrability being tested. Instead subtract the Laurent principal parts for the *interior* electric solution, then reconstruct the physical-frequency field by

    E_total = E_inc + K_global(k0) chi E_B.

The finite-rank global correction is consequently

    K_global(k0) chi V_B C,

and its magnetic correction is obtained by taking its curl and dividing by i omega mu0. The selected outgoing correction is obtained from the same polarization source by the real-frequency far-field map and the fixed output projection. Therefore the field map and T share the same finite coefficient map C exactly. Where individual component traces require care, the common-kernel argument still uses only inputs on which the background and physical total fields agree, so their legitimate traces and integrability agree as well.

This proves the preceding rank theorem for actual compact ordinary-dielectric scattering, whenever a bound K on the residual background counted subspaces is available. It does not use a circuit model or independently adjustable fictitious ports.

### Consequence for the new modal hotspot construction

In its selected axisymmetric sector the completed modal construction follows one simple pole, regardless of the number of conical tips. Its pole-enhanced field map has one excitation functional. All arbitrarily numerous hotspots in that pole term have amplitudes proportional to that same scalar. A subspace of dimension at least two contains a nonzero input annihilating it. Consequently one simple pole contributes at most one additional counted direction beyond its analytic background. Arbitrarily large normalized modal peaks, arbitrarily high Q, and arbitrarily many peaks of that mode do not change this rank.

This does not assert that the complete device has only one channel. Other symmetry sectors, other poles, and the background can all contribute; they have to be analyzed in their own right.

## A serious attempted continuation toward a counterexample

The next potential construction would require an unbounded number of independently accessible pole directions at the same real frequency, with their *combined* plane-flux operator concentrated in the square. Several concrete possibilities were tested conceptually against the exact Maxwell requirements:

1. **Many almost degenerate large cavities.** Widely separated identical resonators can have nearly degenerate weakly interacting modes and independent radiation patterns. But their unit-power fields at a remote common section are ordinary radiative tails, not arbitrarily amplified local cavity fields. Bringing many microscopic tips of those modes to the section requires an additional common-material design. A weak connection or nonzero tail is insufficient: the whole incoming-to-section matrix must have a positive minimum singular value after physical power normalization, and the absolute bypass must be bounded for all superpositions.

2. **One highly degenerate spherical pole.** Its residue rank can grow with angular order, so the rank lemma does not exclude it. However the newly proved radial bypass obstruction in `channel_next.tex` shows that a pure angular order in a fixed homogeneous core has an exterior annular absolute-flux cost growing exponentially with the order. Its arbitrary azimuthal coefficients and both polarizations already include every coherent vector in that degenerate space. Increasing radial Bragg gain does not remove the cost. Mixed angular orders remain a distinct problem.

3. **Small circulating peaks straddling the boundary of D.** For large bypass tolerance, return flow is permitted, so placing opposite signs on opposite sides of the boundary is a potentially relevant loophole. But a bounded-positive-contrast conical electric singularity is integrable: if E behaves like r^(lambda-1) and the regular magnetic part stays bounded, its flux integrated over a radius-r disk is O(r^(lambda+1)), tending to zero. Shrinking the corner therefore gives high pointwise intensity without an order-one integrated passage channel. Resonant amplitude could compensate that small factor, but it also multiplies the unmeasured return flux; a uniform ratio and a coherent many-mode construction are still required. The modal theorem supplies neither and cannot be silently repurposed for that purpose.

4. **Independent matching of mixed radial orders.** The new local synthesis theorem in `channel_next.tex` genuinely varies a finite list of complex TE core coefficients using ordinary radial dielectric controls, and its extension does the same for separated TE/TM orders. It is a local inverse-function theorem with a retained, possibly tiny image radius. Repeated application does not prove that arbitrarily large simultaneous gains are reachable: the control path may approach the material bounds, the Jacobian may become singular, and its certified radius may collapse. Even global gain synthesis would leave the full-plane coherent bypass measurement to be proved.

Thus this fresh route has advanced from “make one resonance arbitrarily strong” to an exact statement of how many input directions a resonance can affect. It has not furnished the required unbounded family of flux-localized, power-normalized resonant directions.

## Why published network realizability does not close the step

The primary paper [Milton and Seppecher, *Electromagnetic circuits*, Networks and Heterogeneous Media 5 (2010), 335–360](https://www.aimspress.com/article/doi/10.3934/nhm.2010.5.335) was inspected in its [publisher PDF](https://www.aimspress.com/aimspress-data/nhm/2010/2/PDF/1556-1801_2010_2_335.pdf). Pages 339–340 explicitly use limiting zero or infinite material moduli and a variable magnetic permeability, and leave approximation of the ideal circuits as a further problem. These hypotheses do not satisfy the fixed positive scalar-permittivity interval and fixed permeability here. The article therefore cannot supply the required arbitrary matching realization. Replacing its constituents by “resonant dielectric equivalents” would require a new Maxwell convergence proof at the shrinking section scale, including port-power and bypass errors.

Likewise the [hybrid electromagnetic circuit construction](https://arxiv.org/abs/0910.0798) uses connectors with both permittivity and permeability zero. Its response-matrix universality cannot be imported into this ordinary-dielectric class. These are precise scope failures, not evidence that the desired bounded-material realization is impossible.

## Why the parallel proof route still does not close

The static factor I+P chi is uniformly invertible under the material bounds, but the dynamic compact remainder and its inverse are not uniformly controlled as the allowed material support grows. The exact meromorphic decomposition is therefore a theorem for each device, not a uniform bound on its number of relevant poles or its regular background. Near-resonance large local magnetic norms remain possible. Conversely, the all-superposition flux inequalities do not control those norms: the existing entire-plane local packet construction has arbitrary dimension and arbitrarily large local resource with fixed positive flux and small bypass. A global radiation-accessibility estimate is still essential.

The finite-rank reduction suggests a more specific sufficient proof strategy: establish a device-uniform bound on the sum of (i) a counted-background dimension and (ii) the number of resonant excitation directions whose section-flux residues can satisfy the passage and bypass thresholds. Neither term has been bounded here for unrestricted exterior support. Simply bounding the number of all resonances by an enclosing volume would change the target.

## Independent check completed during this attempt

Read-only audit of `cn:local-synthesis` and `cn:both-synthesis` in `channel_next.tex` found no substantive defect. The TE Wronskian variation has the stated sign and prefactor; the outgoing Wronskian makes the real/imaginary coefficient-kernel change of basis invertible. Even/odd analyticity and highest finite-Hankel degree prove independence. The TM weighted variation gives the displayed positive integral divided by `2 i k0 A n_b^4`; its neighboring-order identities and separated triples prove the stated independence. The inverse-function certificate respects the material interval and correctly makes no global-gain claim. These findings were sent to the channel author.

## Formalization and handover

The common-kernel rank increment lemma is finite-dimensional algebra and can be formalized independently. Its applicability to a physical device uses the existing analytic Maxwell pencil and the real-frequency reconstruction just described. Formalizing the rank statement would not prove a uniform background count or the missing many-resonance realization. No unrestricted channel closure or complete Maxwell Lean verification is claimed.
