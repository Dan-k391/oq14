# NewtonHessian: full weak Hessian and projection symbol

`lean/NewtonHessian.lean` compiles ten exported theorems under pinned Lean 4.19.0. All ten axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

The weak Hessian is defined by the actual integral of `GreenKernel.phi 0` against two actual Schwartz coordinate derivatives. Consequently the source contribution is retained. The Fourier calculation derives, rather than assumes, the matrix `-xi_i*xi_j/|xi|^2` using the scalar Newton pairing and the correct negative sign in inverse-Fourier differentiation.

The matrix is proved equal to the negative of the already constructed longitudinal projection symbol, including the convention at zero. Entrywise norms are at most one. The exact weak trace is `sum_i weakHessian(i,i,f) = -f(0)`, proving the fundamental-solution identity with its source term. The final theorem identifies the Fourier multiplier of the actual physical projection with the negative Hessian matrix for arbitrary vector L2 fields.

The hotspots agent independently reviewed the complete source and passed the derivative signs, constants, finite-dimensional symbol calculation, integrability uses, Dirac-source trace identity, and final scope. No substantive defect was found.

Scope: these are actual weak test-pairing identities and actual L2 Fourier-multiplier agreement. A spatial convolution action on arbitrary L2 sources is not defined or assumed in this module. No claim equates the pointwise Hessian alone with the full distributional Hessian. No packaged continuous Schwartz-dual object is needed or asserted by these statements.

Related independent audit by channels: ModalInterface23 passed its actual radius cross-product traces, a/n interior normalization, both matching implications, nonzero-field conclusions, and high-Q assembly. Its explicit punctured-interior restriction remains necessary until the separately developed origin bridge is proved.
