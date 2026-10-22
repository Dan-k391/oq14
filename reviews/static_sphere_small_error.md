# Derived small-radius source errors for the literal parity-kernel sphere

Source: `lean/StaticSphereSmallError.lean`.
SHA256: `91B5EB31CE949A12109F7F6DE7CB244237CAA885CBB1AE757495CC28E40A2288`.

Author final pinned compiler and object emission pass with exit 0, no warnings,
and both reports use only propext, Classical.choice, and Quot.sound.
Log: `lean/logs/StaticSphereSmallError-final.log`. Root independent full-source
mathematical and pinned compiler review PASS, no warnings and both reports
standard-only. Log: `lean/logs/StaticSphereSmallError-root-audit.log`.

For one actual sphere of radius rho*a, susceptibility chi>=0, and gain b/a,
the actual local incident derivative bound M/a and actual center component
amplitude bounds A/a imply the actual weighted forcing error and actual trial
norm estimates. The source-error constant is explicit and contains the fixed
enclosing radius and genuine dynamic/parity kernel norms. No source-response
or Green convergence estimate is a hypothesis.

The existing actual inverse residual estimate then gives weighted and physical
L2 errors bounded by constants times a*sqrt(a), and actual coordinatewise L1
source errors bounded by constants times a^3. The scalar perturbation smallness
condition K*a<=1/2 is explicit; the next family wrapper removes it using the
proved positive smallness radius and constructs actual geometric support data.

Scope: a single sphere and the literal explicit parity-kernel inverse, with
actual local incident derivative/amplitude hypotheses. Multiple-sphere
material interactions and identification of a specific finite-stack Green
background with these kernels are separate work. This does not label the
weaker dynamic support-volume bound as O(a^2).

## Independent integration verification, October 22, 2026

Complete source reviewed independently. The pinned compiler completed with exit 0, no warnings, and all 2 reports using only standard foundations. Final source SHA256 `91b5eb31ce949a12109f7f6de7cb244237caa885cbb1ae757495cc28e40a2288`. Independent log: `lean/logs/StaticSphereSmallError-root-audit.log`; log SHA256 `34d094cb28df90ec170db156d0294fd5ffbd715b3c4a56ca896b850ae5a20c9d`. This certifies the stated scope, not either complete OQ14 construction.
