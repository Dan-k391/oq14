# Derived actual finite-sphere reaction-field asymptotics

Frozen source: lean/FiniteSphereReactionScale.lean.
SHA256: 760BBDDBC0F380D87D1B9BA41B0A897A390C812DAA051A4779B2F2D3D3BECD29.

Author final pinned compiler and object emission PASS: exit 0, no warnings,
all three reports use only propext, Classical.choice, and Quot.sound.
Log: lean/logs/FiniteSphereReactionScale-final.log. Root independent complete-source mathematical review and pinned compiler PASS: exit 0, no warnings, standard-only reports.

Actual ball volume scaling, the derived polarization factor, and actual
incident center bounds A/a yield a derived finite moment error O(a cubed)
for radius rho*a balls. The actual inverse-source family already proved in
FiniteSphereAsymptotics is inserted into the genuine reaction integral and
compared with explicit center-evaluated reaction kernels times the actual
volume-polarization moments. The resulting field error is O(a cubed), uniform
in the observation point and in electric/magnetic parity.

The final family theorem allows actual centers to move with a; it constructs
all support data and a positive small-radius range. Its premises are actual
uniform center separation, fixed enclosing geometry, actual incident local
derivative bounds M/a, actual center amplitude bounds A/a, and actual weighted
forcing representatives. No inverse response, source convergence, kernel
convergence, or dipole field conclusion is a premise. The intermediate
reaction_from_estimates theorem is explicitly a composition with the previously
proved source estimates; the final family theorem discharges that input.

The field here is the literal explicit parity reaction field, before gain
amplification. The gain b/a and its reciprocal enter the actual material
inverse and the displayed constants. Amplification estimates are separate.
Physical finite-stack spatial Green identification and shrinking-gap plane
integration remain open and are not claimed by this theorem.

## Independent integration verification, October 22, 2026

Complete source reviewed independently. Pinned compiler exit 0, no warnings; all 3 reports use only standard foundations. Final source SHA256 `760bbddbc0f380d87d1b9ba41b0a897a390c812daa051a4779b2f2d3d3becd29`. Independent log `lean/logs/FiniteSphereReactionScale-root-audit.log`, SHA256 `8b281bc922c944d69b24392eff15a12beced5d9ff14729e22d26944e11e2f603`. This verifies the stated scope; neither full OQ14 construction is yet formally closed.
