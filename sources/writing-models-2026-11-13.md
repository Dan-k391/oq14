# Writing models for the OQ14 manuscript

Prepared 13 November 2026. These papers are examples of explanation and
organization; they are not substitutes for the hypotheses or proofs of our
results. Read the indicated passages with the manuscript's introduction and
main theorem statements open beside them.

## 1. Result-first introduction

**Shim, Chung and Miller, “Maximal Free-Space Concentration of Electromagnetic
Waves” (2020)** — [full text](https://arxiv.org/html/1905.10500v3).

Read the opening paragraphs and Section I. The authors identify the physical
question, the quantities held fixed, their main bound and an intuitive
interpretation before developing the optimization. Their first figure gives
the reader a picture of the setup.

**Apply here:** introduce the two questions in ordinary physical terms, say
what is fixed and what the device may change, and state each principal result
with its most important qualifications. Then give the mechanism in a few
sentences before introducing formal definitions.

## 2. A rigorous channel paper with a readable map

**Piestun and Miller, “Electromagnetic degrees of freedom of an optical system”
(2000)** — [full text](https://ee.stanford.edu/~dabm/207.pdf).

Read the introduction, especially its final paragraph, and Section 3. The
introduction explains why degrees of freedom matter, identifies limitations of
the usual approximations, describes the new framework, and maps the argument
section by section. Mathematical background and details are also placed in
appendices.

**Apply here:** give a brief roadmap of the hotspot result, channel result and
their proofs. Keep precise definitions and proofs accessible, but relocate
supporting audits and lengthy technical developments to later sections or
appendices where practical. Our count and normalization differ from theirs,
so use this as a presentation model, not as support for an OQ14 conclusion.

## 3. Explain a mechanism with a geometry

**Bille-Lauridsen and Mørk, “The Dielectric Bowtie Effect” (2026 preprint)** —
[full text](https://arxiv.org/html/2607.11613v1).

Read the introduction and Figures 1–2. The paper shows the geometry early,
names the relevant length scales and explains their different roles in words
before presenting the scaling relation. It then connects an idealized local
model to a finite cavity.

**Apply here:** draw the local geometry used for the hotspot argument, then
show how multiple localized structures fit into a single finite device. Explain
what rounding changes and why a local singularity alone is not yet a globally
excited, simultaneous hotspot result.

## 4. Explain the logic behind a bound

**O. D. Miller and coauthors, “Fundamental limits to optical response in
absorptive systems” (2016)** —
[full text](https://millergroup.yale.edu/sites/default/files/files/MillerPol16.pdf).

Read the introduction, Figure 1 and Section 2. The authors use a labeled
geometry and power balance, then explain in words how the main inequality
arises and where subsequent results are derived. They identify absorption as
part of the setting.

**Apply here:** illustrate the incident field, the fixed section, selected
output, and flux outside the section before defining passage and bypass. Give
the reader a verbal explanation of the resource-dependent bound before its
operator estimates. The cited paper treats absorptive systems; its material
assumptions must not be imported into our lossless setting.

## Optional short model

**D. A. B. Miller, “Spatial channels for communicating with waves between
volumes” (1998)** — [full text](https://ee.stanford.edu/~dabm/194.pdf).
On its first page, the paper starts from a familiar diffraction picture,
identifies where it is inadequate, and states the scalar-wave problem before
introducing its Green operator. Useful for rewriting the opening of the channel
discussion and explaining each equation immediately after it appears.

## What this implies for the current manuscript

The abstract in `manuscript/main.tex` packs the two questions, mechanisms,
restrictions and formal verification into one paragraph. The first section of
`manuscript/sections/problem.tex` then opens with assumptions and formal
inequalities before the reader sees a physical picture. The main channel
construction occurs much later. The audit is useful, but it currently competes
with the explanation of the work.

A practical revision order:

1. Replace the dense opening with a narrative introduction: why the two
   questions matter, how they differ, and what is held fixed.
2. Add an informal results table, with links to precise theorems: driven and
   modal hotspot results, the channel counterexample for the stated
   parameter regime and complete-scattering output, and the remaining cases.
3. Add a section-and-bypass diagram and a schematic of hotspot construction.
4. Before each principal proof, explain the central idea and provide a short
   proof roadmap; define quantities in words beside their first equations.
5. Place formal verification, provenance, and subsidiary technical arguments
   later in the paper or in appendices, preserving precise scope and proofs.

An example of the intended explanatory register for the channel question:

> Imagine a fixed square cut through a dielectric device. We ask how many
> independent input patterns can carry substantial power through that same
> square while keeping the flux outside it under control. The device surrounding
> the square may grow and become more complicated. Our counterexample shows
> that, for the thresholds and complete-output convention stated below, the
> square's area alone does not give a uniform finite channel count. The case of
> a stricter bypass requirement remains a separate question.

This is a guide for the narrative, not a replacement for the quantified
statement in `sections/problem.tex` or the hypotheses of the counterexample.
