# Genuine plane annulus inverse-power integrals

Frozen source: lean/PlaneInverseAnnulus.lean.
SHA256: 7AECE5E79576C7F47320CEA686585B3DAC9586753D2515D422F9F57CDB638343.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all seven reports standard-only. Log: lean/logs/PlaneInverseAnnulus-final.log.
Independent review is pending.

Actual radial profiles restrict inverse radius and inverse radius squared
to d<r<=M. Their genuine plane integrability is derived through actual
Euclidean radial measure decomposition. The weighted radial integrands are
exactly one and inverse radius, respectively. Actual positive-interval
integration yields plane masses diskConstant*(M-d) and
diskConstant*log(M/d) for positive d<=M. Here diskConstant is the actual
surface factor twice the unit disk area.

No polar-coordinate formula, logarithmic bound or plane integrability is
assumed. These are actual scalar plane profiles; application to the genuine
Maxwell kernels and coherent flux remains separate.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 7 reports use only standard foundations. Final source SHA256 `7aece5e79576c7f47320cea686585b3dac9586753d2515d422f9f57cdb638343`. Independent log `lean/logs/PlaneInverseAnnulus-root-audit.log`, SHA256 `58d0537fdb4b9c1ba30a8d4a63efb9358d22675230f3813510859b754e094815`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
