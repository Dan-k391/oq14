# OQ14 scope index

Source: Miller and Monticone, arXiv:2605.24738v1, Section 5.6.
This file is an index; the canonical mathematics belongs in manuscript/.

Freeze fixed positive frequency; real scalar reciprocal nonmagnetic ordinary dielectrics 1 <= eps_r <= eps_plus; identical physical planar section D for every channel construction; physical incident/output power normalization; fixed thresholds tau, eta, delta; every coherent vector in each counted subspace must meet passage and absolute-bypass constraints. No uniform feature size, surrounding support size, Q, matching complexity, or port-count constraint is assumed for the area-only target. A common positive eps_minus variant and fixed-support variant are separate.

Hotspots require one normalized global field exciting every neighborhood. Driven 2D, driven finite 3D, and modal claims must be distinguished. A local singularity alone does not settle global packing.

The user supplied a research manual as project material. Its mathematical routes are proposals, not evidence or established conclusions.

## Canonical scope and resource locations

| Item | LaTeX label |
|---|---|
| Ordinary dielectric class, fixed frequency and vacuum exterior | `pr:class`, `pr:maxwell` |
| Physical power normalization and outgoing admissibility | `pr:scattering` |
| Same square D, transmission, passage, absolute bypass | `pr:count`, `pr:transmission`, `pr:passage`, `pr:bypass` |
| Uniform channel target and separate area scaling | `pr:channel-target`, `pr:area-bound` |
| Driven versus modal hotspot targets | `pr:hotspot-target`, `hs:peak-definition` |
| 2D exact Maxwell reduction and incoming power per length | `hs:tm`, `hs:power` |
| Finite 3D driven theorem, projected patch and finite incident power | `hs:three-packing`, `hs:three-illumination` |
| Closed single-resonance modal packing with reciprocal norm | `ms:modal-packing`, `ms:normalization` |
| Local modal coefficient continuation and rounding | `hs:modal-coefficient-continuation`, `ms:rounding` |
| Internal field resource and trace compatibility | `ch:resource`, `ch:tracecompatibility` |
| Explicit collar, shape, lower-index and amplification costs | `ch:arearesource` |
| Growing support in Bragg example | `cx:bragg`, `cx:bragg-scope` |
| Mode-model errors versus physical section and bypass | `cx:n-model`, `cx:missing-bridge` |
| Whole-plane local bypass obstruction and exact noncompletion | `ca:localpackets`, `ca:compactcompletion` |
| Exact formal theorem coverage and logical foundations | `ver:lean` |
| Separate verdicts and undischarged bridges | `ver:verdicts`, `ver:gaps` |

Subsequent request: complete closure of the original statements and Lean
formalization. The project must not assert that either requirement is met
unless the complete substantive theorem and its physical bridges are proved.
