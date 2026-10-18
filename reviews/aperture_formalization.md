# Lipschitz plane aperture audit

Frozen source: `lean/WeakPoynting/Aperture.lean`, SHA256 `8d34849076123befee915ec2add25a5c2d4a2fdbdfbb583cc2247627756474e3`. The 11 selected exports compile cleanly; every axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`. Complete directly captured compiler output and source/dependency hashes are recorded in `aperture-verification.txt` and `aperture-provenance.json` beside the source.

An aperture is an actual compact globally Lipschitz scalar on the transverse plane. Its partial derivatives are the actual Frechet derivatives, with measurability and pointwise bounds independently proved. Rademacher supplies a.e. differentiability on the plane. The coordinate measure-preserving equivalence and quasi-measure-preserving projection transport this full-measure statement to physical three-space; no unjustified evaluation on a fixed line is used.

The tensor of that aperture and a compact C1 axial test is proved Lipschitz and compactly supported inside the stated open physical region. Its actual a.e. gradient is calculated by the product and chain rules. The previously proved Lipschitz weak-divergence theorem applies, and genuine coordinate Fubini identifies the two resulting L1 plane functions. The signs yield `integral(theta' * flux + theta * lateralFlux) = 0`, hence the weak derivative of flux is lateralFlux.

`maxwell_aperture_continuous_flux` specializes to actual regional weak Maxwell fields. It constructs a continuous representative on each compact interval in the axial collar, agrees a.e. with the actual plane integral, and proves exact integral increments. Raw plane integrals are not asserted to be representative values at every plane. Uniqueness at all interval points follows from the existing representative theorem when the interval is nondegenerate.

The frozen module does not contain the nonsmooth axial endpoint formula or its complex Hermitian specialization; these are developed separately. It introduces no boundary trace, scattering solvability, global field L2 requirement, or assumed density. The coordinator independently read the complete source and approved the derivative and Fubini scope.
