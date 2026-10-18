# Channel track audit

Owned files: `manuscript/sections/channels.tex`, this review. No Git operations performed.

## Results and scope

- `ch:ranklemma` PROVED. Rank-M approximation error must be strictly below sqrt(tau), including for noncompact operators and infinite-dimensional candidate subspaces.
- `ch:factorization` PROVED. Endpoint and error factors retained; operator examples in `ch:algebraaudit` disprove their removal by passivity or per-device compactness. These are not dielectric counterexamples.
- `ch:fluxlemma`, `ch:magneticHone`, `ch:caccioppoli`, `ch:resourcecount`, `ch:average` PROVED under their stated local hypotheses. Full proofs audit and reproduce supplied prior report Section 3, explicitly credited. No originality claim for that argument.
- `ch:outerwindow` PROVED. New useful bridge: choose a smooth window equal to one on D and extending outside D. Absolute bypass bounds the signed correction, giving q_psi >= eta*||Ta||^2 - delta*||a||^2. Thus p=eta*tau-delta>0 supplies coercivity without an inner-edge assumption or a conserved collar. Physical D never changes. Trace compatibility is explicit (`ch:tracecompatibility`), and delta<eta*tau is an additional restriction of this route.
- `ch:fulloutput` PROVED under the explicit resource bound: full-output finite-rank R=T P_(ker projected magnetic field)^perp. Its error squared <= (delta+K*C_H*B_*/lambda_next)/eta. This acts on the complete physical T, with all feedback included in the resource B_*.
- `ch:essential` PROVED under the same resource and passage hypotheses: essential norm at most sqrt(delta/eta); exact zero bypass gives compactness for the particular full device. This does not make counts uniform across devices with growing B_*.
- `ch:spectralcor`, `ch:arearesource` CONDITIONAL uniform family/area results. Explicit constants and the extra dimensionless local resource omega*B_* remain. A wavelength-size comparison collar must be available for the displayed area scaling.
- `ch:anisotropy` PROVED local extension to real symmetric positive-definite tensors with common ellipticity bounds, still constant scalar mu.
- `ch:missing` OPEN: eliminate B_* or prove a distinct uniform finite-rank approximation theorem using only frozen area-only resources. No full OQ14 channel closure.

## Mathematical audit notes

1. The cross-Poynting Hermitian form is c0/4*(e_a cross conjugate(h_b) + conjugate(e_b) cross h_a). Its second term is not e_b cross conjugate(h_a). Correct conjugation is essential to linearity in a and divergence cancellation.
2. Magnetic div-curl regularity uses constant permeability, not any derivative of epsilon. The exact constant C_H=k0^2*eps_plus+||grad rho||_infty^2 follows from Minkowski plus a two-dimensional Cauchy--Schwarz inequality.
3. Flux is a continuous weighted weak plane representative, not an assumed L2 tangential trace. The bridge to a sharp operational section is a stated compatibility requirement; smooth traces or L1 plane convergence suffice.
4. The comparison Dirichlet box is analytical only; no conducting walls or boundary conditions are imposed on the actual dielectric.
5. Counting uses an exact positive-octant lattice-cell argument and includes eigenvalues at the cutoff. The next eigenvalue is strictly larger, giving the strict output-error inequality.
6. The average-resource proof orthonormalizes internal magnetic fields through their Gram matrix. It does not assume orthogonality of physical internal fields.
7. Bypass need not be a quadratic form. Only its scalar inequality for every coherent vector is used. Basis-only certificates cannot be substituted.
8. The outer-window step leaves the material bounds, fixed D, frequency, and all thresholds untouched. Its larger analytical support is not a larger physical aperture.
9. Independent review by the hotspot track found no substantive defect in the local constants, full-output approximation, counting, area substitution, or anisotropic extension. It identified a wording issue in the domain of the flux density; corrected `ch:tracecompatibility` to define the density on the entire section plane before imposing global outside-D integrability.

## Primary literature checks

Miller 2023: David A. B. Miller, *Why optics needs thickness*, Science 379(6627), 41-45 (2023), DOI 10.1126/science.ade3395. Full author PDF includes supplements (41 pages): https://dabm.stanford.edu/wp-content/uploads/2023/01/J289.pdf . Read S2 (PDF pages 16-18) and S12 (pages 37-39). Nonuniform maximum-index replacement is expressly conjectural. S12 proposes homogeneous estimates and design-specific complete-Green-function diagnostics. Cite key `miller2023`.

Kuang 2025: Zeyu Kuang, David A. B. Miller, Owen D. Miller, *Bounds on the Coupling Strengths of Communication Channels and Their Information Capacities*, IEEE Transactions on Antennas and Propagation 73(6), 3959-3974 (2025), DOI 10.1109/TAP.2025.3533263. https://dabm.stanford.edu/wp-content/uploads/2025/06/J298.pdf . Read Section II (PDF pp.2-3), explicit domain setup (pp.4 onward), Appendix E (pp.12-13). Physical map includes resistance and endpoint response matrices; Eq.(1) retains their norms. Explicit bounds isolate G and use domain size/separation/spherical separation; relative thresholds use a sum rule. Appendix E diagnoses nonmonotonic normalized ratios. Cite key `kuang2025`.

Follow-up checked: D. A. B. Miller, Z. Kuang, O. D. Miller, *Tunnelling escape of waves*, Nature Photonics 19, 284-290 (2025), DOI 10.1038/s41566-024-01578-w, https://www.nature.com/articles/s41566-024-01578-w . Spherical tunnelling/channel-decay analysis is relevant context, not a proof of the unrestricted structured internal-section problem. Root may include compact prior-art table. No exhaustive novelty or completeness claim.

Prior report: supplied unpublished research report dated October 8, 2026, extracted at `sources/cache/prior-report.txt`, Section 3, source PDF `oq14_research_report.pdf`. Cite key `priorreport`. Resource theorem already there; outer-window bypass bridge and explicit full-output approximation are the incremental deductions here.

## Independent counterexample review

Read `manuscript/sections/counterexamples.tex` after its complete first draft was written. No substantive mathematical defect found in the reviewed statements:

- `cx:bragg`: TE radial ODE and u/u' matching are appropriate for constant mu. Low/high quarter-wave transfer is -diag(q^-1,q); the exterior Riccati-Hankel Wronskian is 2i; derivative modulus squared is 1-x^-2+x^-4, in [3/4,1] for x>=1. Unit incoming power fixes the core amplitude. Choosing q between 1 and sqrt(eps_plus) and a sufficiently large derivative root supplies the claimed obstruction for every eps_plus>1. This is one reflected partial wave, not growing transmitted dimension.
- `cx:evanescent`: both curl equations, signs of H, positive integrated flux, normalization, sine orthogonality, and sidewall conditions hold for every finite coherent vector. The absent global finite-power completion and absolute-bypass certificate are correctly stated.
- `cx:mirror-network`: reciprocal unitary mirror matrices, round-trip phase, total t=i and r=0, and inverse factor xi^-1 are consistent. It is explicitly network algebra, not a dielectric synthesis.
- `cx:pair-solution`: solved the 2x2 system independently; reflection numerator, t=-i at gamma=J, energy 1/J, exchange-current sign, quartic matched line shape, linewidth 2*sqrt(2)*J, and pole locations are correct. Rate, detuning and loss tolerances follow.
- `cx:n-model` and `cx:port-errors`: B0^*B0=2I; the Neumann/resolvent bound and rho threshold are correct, with weighted weak-link error normalization explicit. Arbitrary perturbations are correctly not declared automatically passive.
- `cx:compression` and `cx:absolute-bypass`: isometry compression gives a lower bound on the complete output norm; the stronger flux Q>=eta I test uses T contraction correctly. F_ij conjugations yield a Hermitian pointwise physical-flux matrix, and integrating its operator norm is a sufficient all-vectors absolute-bypass certificate.
- `cx:angular-obstruction`: convexity proof is sound once the regular radial derivative asymptotic is made explicit. Sent a minor polish request to state u'~(ell+1)c*r^ell near zero; u~c*r^(ell+1) alone would not establish the derivative sign for an arbitrary function. This is a wording/completeness issue, not an identified counterexample.

The section consistently distinguishes a disproved intermediate lemma from an OPEN physical fixed-section channel conjecture. It does not assert that model energy/current matrices are physical Maxwell matrices. No coupled-mode result was promoted to an OQ14 disproof.
