# Actual scalar-to-TE planar jet map

Frozen source: lean/DebyePlanarJets.lean.
SHA256: 336D494669190601B9C28A41F26AA0C19AFFB04A0CB61524BA2ADC87AD3C6EA8.
Author final pinned compiler/object PASS: exit 0, no warnings, three reports
using standard foundations only. Log: lean/logs/DebyePlanarJets-final.log.
Independent audit pending.

For the literal Debye TE electric field curl(x*f), genuine Frechet derivative
product rules give grad(f) cross x and the exact curl components
2*partial_i f + sum_j x_j*partial_j partial_i f - x_i*laplacian f.
At (r,0,0), the actual scalar Helmholtz equation then derives the manuscript's
three jet formulas for E_z,H_x,H_y, including the actual magnetic factor -I/k.
No field-jet identity is a premise. This generic calculus theorem is intended
to be instantiated with the actual symmetric scalar waves and subsequently
with actual smooth angular/finite-band realizations. It does not assert scalar
jet surjectivity, finite incoming power, or a finite-band expansion.
