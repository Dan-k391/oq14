# Reading list for the OQ14 manuscript

Compiled 13 November 2026. These are candidates for the related-work and
methods discussions, organized by what they can actually support. The links
and summaries were checked against the papers or their abstracts; theorem
hypotheses and exact quotations should be checked in the full text before a
specific result is relied on. None of the new candidates below appeared in
`manuscript/references.bib` when this list was prepared.

## Priority reading: hotspot and modal constructions

1. Valdemar Bille-Lauridsen and Jesper Mørk, **“The Dielectric Bowtie Effect:
   Classical Electromagnetic Edge Singularities in Subwavelength Cavities”**
   (2026), [arXiv:2607.11613](https://arxiv.org/abs/2607.11613). A recent
   preprint directly relevant to dielectric field enhancement and rounding. It
   distinguishes the roles of tip radius, gap and outer length using
   electrostatic and three-dimensional quasinormal-mode simulations. Compare
   it with the local singularity and rounded-geometry discussion in
   `sections/hotspots.tex` and the modal sections. Its local scaling and
   simulations do not establish simultaneous global hotspot packing.

2. Bastian Harrach, Yi-Hsuan Lin and Hongyu Liu, **“On Localizing and
   Concentrating Electromagnetic Fields,”** *SIAM Journal on Applied
   Mathematics* 78, 2558–2574 (2018),
   [doi:10.1137/18M1173605](https://doi.org/10.1137/18M1173605),
   [author-hosted text](https://www.math.uni-frankfurt.de/~harrach/publications/localizingEM.pdf).
   Proves field localization and a partial-boundary-data Maxwell Runge
   approximation result in a bounded domain. Useful related work for the
   driven construction and approximation arguments; boundary inputs and
   energy localization are not by themselves a fixed-power far-field
   illumination or pointwise packing theorem.

3. Valter Pohjola, **“On quantitative Runge approximation for the time
   harmonic Maxwell equations”** (2021; revised 2022),
   [arXiv:2105.15058](https://arxiv.org/abs/2105.15058). Provides quantitative
   approximation and conditional stability results. Useful when discussing the
   cost of approximating local fields by accessible excitations; check its
   geometry, regularity and boundary-data hypotheses before applying an
   estimate to open scattering.

4. C. Sauvan, T. Wu, R. Zarouf, E. A. Muljarov and P. Lalanne,
   **“Normalization, orthogonality and completeness of quasinormal modes of
   open systems: the case of electromagnetism,”**
   [arXiv:2112.08103](https://arxiv.org/abs/2112.08103),
   [doi:10.1364/OE.443656](https://doi.org/10.1364/OE.443656). A review of
   normalization, excitation and completeness, complementing the Muljarov–
   Langbein paper already in the bibliography. Use for modal terminology and
   normalization comparisons; verify which normalization and hypotheses the
   manuscript actually uses before asserting equivalence.

5. Mikhail V. Rybin et al., **“High-Q Supercavity Modes in Subwavelength
   Dielectric Resonators,”** *Physical Review Letters* 119, 243901 (2017),
   [doi:10.1103/PhysRevLett.119.243901](https://doi.org/10.1103/PhysRevLett.119.243901),
   [preprint](https://arxiv.org/abs/1706.02099). Demonstrates a high-Q
   mechanism in finite high-index dielectric resonators. Appropriate physical
   context for the modal discussion; it does not prove this project's
   arbitrary packing construction or its fixed-parameter limits.

## Priority reading: channels and comparison of limits

6. Rafael Piestun and David A. B. Miller, **“Electromagnetic degrees of
   freedom of an optical system,”** *Journal of the Optical Society of America
   A* 17, 892–902 (2000), [author-hosted paper](https://ee.stanford.edu/~dabm/207.pdf).
   Develops vector electromagnetic communication modes and effective degrees
   of freedom. Use alongside the channel discussion in `sections/channels.tex`:
   its source and receiver spaces, coupling measures and noise assumptions
   must be compared with the manuscript's physical power, passage and bypass
   definitions before drawing conclusions.

7. David A. B. Miller, **“Spatial channels for communicating with waves
   between volumes,”** *Optics Letters* 23, 1645–1647 (1998),
   [author-hosted paper](https://ee.stanford.edu/~dabm/194.pdf). Gives exact
   scalar-wave communication modes and a coupling-strength sum rule between
   volumes. Good foundational context for singular-value channel language;
   it is not a general Maxwell theorem for the manuscript's internal section.

8. Hyungki Shim, Haejun Chung and Owen D. Miller, **“Maximal Free-Space
   Concentration of Electromagnetic Waves,”** *Physical Review Applied* 14,
   014007 (2020), [doi:10.1103/PhysRevApplied.14.014007](https://doi.org/10.1103/PhysRevApplied.14.014007),
   [preprint](https://arxiv.org/abs/1905.10500). Establishes bounds relating
   free-space intensity concentration and spot size. Useful for contrasting
   the problem's hotspot definition with conventional concentration metrics;
   the free-space setting does not automatically bound resonant dielectric
   interiors.

9. Stephen C. Creagh and Gabriele Gradoni, **“Slepian eigenvalues for
   near-field communication,”** *Physical Review Applied* 23, 024070 (2025),
   [doi:10.1103/PhysRevApplied.23.024070](https://doi.org/10.1103/PhysRevApplied.23.024070).
   A semiclassical approximation for eigenvalues relevant to near-field
   communications. Useful context for channel roll-off in modeled geometries;
   not a universal area-only bound for arbitrary structured dielectrics.

## References already in the manuscript

Start with Miller and Monticone (2026), the source of OQ14, then Miller
(2023), Kuang, D. A. B. Miller and O. D. Miller (2025) for channel context;
Costabel, Dauge and Nicaise (1999) for Maxwell interface singularities; Zhao,
Zhang and Miller (2020) for dielectric mode volumes; and Muljarov and Langbein
(2016) for open-system mode volume. Their existing entries are in
`manuscript/references.bib`. Consult the specific definitions and assumptions
in each paper when positioning the project's results.
