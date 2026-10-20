# NewtonConvolution verification

Frozen source: `lean/NewtonConvolution.lean`.
SHA256: `E82E4529FEA00CA429D5B5F2B5CAAC93E11AB525F5CF3D0833A14D4AE29EE49A`.

On October 20, 2026, the pinned Lean 4.19 toolchain compiled the entire source
cleanly. The 11 exported theorem reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. No admissions or additional axioms occur.

The source constructs genuine translated Schwartz tests and proves the
translation derivative and inverse Fourier identities. The weak source response
is defined by the actual iterated spatial integral
`integral rho(y) integral N(x-y) partial_i partial_j f(x) dx dy`.
For every integrable source, the inner Newton integral and outer weak pairing
are integrable. A separate product-space absolute integrability proof justifies
the Fourier Fubini interchange, yielding the actual ordinary Fourier transform
of the source times the derived full Newton-Hessian symbol.

This module does not claim joint absolute integrability of the original spatial
double integrand, nor yet identify a bounded spatial operator on arbitrary L2
sources. The subsequent L2 identification is developed separately.

Independent read-only review by the hotspots agent passed on October 20:
translation signs, actual change of variables, absolute Fourier integrability,
Fubini, and the scope all checked without a substantive defect.

Exports: `translate_apply`, `translate_pderivative`,
`inverse_fourier_translate`, `weakHessian_translate_spatial`,
`weakHessian_translate_fourier`, `weakConvolution_spatial`,
`translated_newton_integrable`, `source_fourier_pairing_integrable`,
`source_weak_pairing_integrable`, `source_spatial_pairing_integrable`,
`weakConvolution_fourier`.
