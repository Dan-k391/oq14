# Genuine modal continuation: local proof and remaining dependencies

Owned manuscript: `manuscript/sections/modal_next.tex`.

## New proved bridge

`hs:modal-coefficient-continuation` proves that an analytic family of local Maxwell electric fields in a newly introduced conical material has a singular coefficient holomorphic through zero insertion contrast. The limiting coefficient is exactly `sqrt(4*pi/3) E_background(p) dot axis`. Consequently one analytically continued eigenfield has nonzero coefficients at all finitely many chosen points whenever the background component is nonzero there.

The key repair is necessary: the unmodified radial integral has an apparent singularity as the angular exponent tends to one. Subtract the constant value of the H2 regular curl lifting. The constant angular forcing obeys `B0=lambda(lambda+1) A0`, and its particular solution is exactly `-r A0`. The remaining lifting is Hölder and produces an `O(r^(1+gamma))` particular solution, with integrals uniformly convergent for `Re lambda < 1+gamma`. Annulus averaging then proves holomorphic coefficient dependence. This avoids the invalid inference that small L2 error alone preserves singular coefficients.

## Checks completed

- The axisymmetric odd angular eigenvalue two is simple at zero contrast. A compact analytic form construction gives the branch and normalized eigenfunction. Its exact derivative is `nu'(0)=-3 t(1-t^2)` and `lambda'(0)=-t(1-t^2)`, so positive cap contrast gives an exponent below one.
- All angular pairings are bilinear for complex parameter dependence. The physical coefficients and exponents are real for real positive contrast.
- Local curl/div estimates, the fixed regularized Poincare lifting, and the mean-fixed potential give an analytic H1/H2 regular decomposition from a local L2-analytic Maxwell family. The argument uses constant permeability and remains valid at a nonzero complex frequency.
- The negative radial homogeneous term is excluded by finite H1 energy. The annular formula has the correct average factor `2/R` on `[R/2,R]`.
- At zero contrast, the potential Taylor term and the subtracted constant lifting cancel exactly, leaving the background electric field rather than the lifting-dependent potential gradient.
- A finite intersection of nonvanishing contrast intervals is enough; no countable genericity argument or contrast uniform in N is needed. One fixed upper material bound remains respected, while insertion contrast can depend on N.
- Peaks are in separate small three-dimensional balls. With the symmetry axis in the target plane and axisymmetric rounding, an actual maximum in each ball can be rotated into that plane because intensity and the ball are rotation invariant. An offaxis maximum may form a rotational ring, entirely inside its arbitrarily small ball; nondegeneracy and uniqueness are not claimed. The background resonator's projection is not required to fit the patch.

## Global dependencies discharged in the spectral section

The local theorem and general transfer implication are proved. The separate `modal_spectral.tex` now supplies the global hypotheses: a simple pole in a symmetry sector of a finite dielectric sphere; analytic pole/eigenfield continuation for bounded dielectric insertions; a finite nonzero genuine QNM normalization and its continuity; and resonance/eigenfield convergence under tip rounding. Their synthesis is `ms:modal-packing`, with any finite number of peaks of one normalized finite-device mode, fixed real part of the frequency, and any prescribed finite lower quality-factor bound.

The root agent completed the explicit algebraic-index Mie-pole argument and the static-projector/compact-remainder factorization. Both were then independently audited. No driven Herglotz normalization is used for a mode, and no positive all-space energy integral is asserted finite for a QNM.

## Independent coefficient review

The independent counterexample reviewer checked the constant-forcing cancellation, the Hölder-integral bounds near exponent one, and the exact homogeneous-limit normalization, and found no substantive defect. Its requested statement precision is incorporated: the weak Maxwell electric field explicitly belongs to local H(curl), as required for the initial cutoff estimate. The proof spells out why distributional holomorphy plus locally uniform interior estimates upgrades the analytic dependence into the stronger Sobolev spaces. At that review stage the global resonance and normalization arguments were still being written; their completed audit is recorded below. The independent channel reviewer subsequently checked the same local continuation and finite simultaneous nonvanishing arguments without finding another defect.

## External source boundary

The regularized curl lifting is the same verified Costabel--McIntosh operator used in `hotspot_closure_audit.tex`. The new coefficient cancellation and holomorphic continuation are derived explicitly rather than attributed to a perturbation paper. Primary literature consulted for context includes Aiello--Harris--Marquardt, *Physical Review A* 100, 023837 (2019), DOI `10.1103/PhysRevA.100.023837`, and Muljarov--Langbein, *Physical Review B* 94, 235438 (2016), DOI `10.1103/PhysRevB.94.235438`. Neither paper's abstract alone is used as a proof of the present global hypotheses.

The continuum argument is not Lean-formalized. A subsequent finite algebraic formalization cannot certify the Maxwell analytic regularity and resonance steps without an explicit corresponding library development.

## Independent channel-route review

Read-only audit of `manuscript/sections/channel_next.tex` found no substantive defect. The radial/tangential cross products, the two angular inversion parities, and the full coherent-field opposite-point triangle inequality were checked directly. The Riccati interval `[gamma,l+1]`, the upper inside and lower outside radial integrals, and their exponentially growing ratio are correct. The theorem excludes the specified pure-angular-order homogeneous-core radial Bragg route; its explicit exclusions of mixed angular orders, a structured core, offcenter spheres, and offset section planes correctly prevent its being mistaken for the all-device channel conjecture.

## Sphere-route adversarial check sent to root

The proposed Mie rational-exponential proof was independently checked before the global section was written. The large-z rational ratio has the stated `(-1)^l (n+1)/(n-1) [1-i l(l+1)/(n z)+O(z^-2)]` expansion. To avoid division gaps, define both exponential coefficients before division. Simultaneous zeros of these coefficients force both the outgoing exterior Riccati-Hankel function and its derivative to vanish, contradicted by the interior Hankel Wronskian. At a denominator root neither coefficient can vanish separately. Thus the rational ratio is finite and nonzero there. Its derivative minus `2 i n` times itself is a nonzero rational function, permitting the algebraic-index transcendence argument for simple zeros. Operator simplicity additionally needs the separated 2-by-2 matching inverse, exclusion of numerator cancellation by the Wronskian, and the invariant axisymmetric meridional-electric/azimuthal-magnetic sector. These requirements were sent to the root author explicitly and are incorporated in the finished proof.

## Completed spectral adversarial audit

The full `modal_spectral.tex` was read. The static compressed longitudinal projection is positive and contractive even though compression is not itself an orthogonal projection; the Woodbury inverse gives the claimed uniform bound. The dynamic kernel is an entire Hilbert--Schmidt family, vanishes at zero, and gives an invertible Fredholm base point. Almost-everywhere coefficient convergence gives strong convergence of the static inverses and norm convergence of the compact pencils, without falsely claiming norm convergence of the leading material operator.

One actual wording/proof defect was found and repaired with the root author's permission: the simple-pole Schur reduction initially chose blocks of L but then used the rounding norm convergence proved only for F. It now consistently uses F; the explanation explicitly states why L cannot be used for that convergence step. Multiplication by the static inverse does not change right kernels or characteristic multiplicity.

The Mie matching determinant, rational-coefficient expansion, Wronskian exclusion of zero divisions, algebraic-index transcendence arguments, separated-block algebraic multiplicity, and Rouché existence of high-radial-order poles all check. The fixed sector avoids assuming that the full rotationally degenerate sphere pole is simple.

The reciprocal left functional is nonzero on that sector. Its derivative pairing gives the residue denominator, and applying the vacuum resolvent changes the denominator to `k_*^2 d`. Thus `N=-(k_*/2)d` gives the stated `-E tensor E/(2 k_* N)` physical electric Green residue, with sign consistent with the chosen curlcurl-minus-k² operator. Strong convergence of the weighted eigenfields proves continuity of this finite nonzero norm. Under real dilation by s the raw norm scales as s³, so the normalized electric field scales as s^(-3/2). The exact real-frequency adjustment and high-Q inequalities therefore preserve the local packing construction with strict margins.

The independent channel reviewer separately checked the spectral and local proofs and found no substantive gap beyond the same L-versus-F correction. The final theorem's stated limits remain essential: finite smooth interfaces, common material bounds but contrast allowed to depend on N, no support-size or minimum-feature bound, genuine complex-frequency QNM normalization, and no requirement of unique or nondegenerate maxima. The unrestricted power-channel conjecture is not settled by this modal result.
