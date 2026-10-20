# Hankel real basis independent audit

Independent whole-source mathematical review and pinned compiler recheck by `fredholm_sol`: PASS.

- Source: `lean/HankelRealBasis.lean`.
- Exact SHA256: `3862604AA0E2D40F4BE0903C4C12CCFC155AE67B535CF3D1E92A741D1A57DC5B`.
- Independent command: pinned Lean 4.19.0 `lake env lean HankelRealBasis.lean`, exit 0, no warnings.
- Independent log: `lean/HankelRealBasis.independent-fredholm.log`; SHA256 `997557D0921004A5E88FD726C24B7B3D576A9D7E9366A88BA6BE3047494D1D42`.
- All fifteen dependency reports use only `propext`, `Classical.choice`, `Quot.sound`.

Conjugation is proved through the actual factorial coefficients, finite inverse-power sums, and real-frequency phase/exponential factors. Thus the real part of the actual outgoing function is the literal regular `psi`, including the chosen phase convention. Taking the imaginary part of the already proved actual incoming/outgoing Wronskian gives determinant one for the displayed real basis. The real ODE and first derivatives are the real and imaginary parts of the actual complex equations.

The Frobenius square is exactly the sum of the outgoing function and derivative squared norms. The earlier genuine energy estimate controls it by `4/(1-c^2)` in the stated low range. The elementary real two-dimensional estimate applies to the basis matrix and its literal determinant-one adjugate; the same sum of squared entries controls both. Consequently both squared-state bounds are correct, with no matrix norm or inverse bound included as an input. This file establishes the radial vacuum basis/state estimates, not an interface matching or final scattering estimate.
