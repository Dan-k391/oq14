# Independent read-only KernelEstimates audit

The complete frozen `lean/KernelEstimates.lean` was independently read, together with its local-integrability and dynamic-remainder prerequisites. No mathematical defect was found.

The actual Haar radial integral theorem specializes to Euclidean dimension three with the correct coefficient `3 * volume(unit ball)`. The closed-ball indicators become radial intervals `(0,R]`; the endpoint at zero is excluded in the radial calculation and causes no missing mass. Radius zero also gives the correct zero integral. The exact inverse-radius and squared-inverse-radius masses are `(3/2) * volume(unit ball) * R²` and `3 * volume(unit ball) * R`.

The final dynamic remainder bound uses the independently proved L1 integrability and the actual entrywise all-point estimate under `abs(k)*R ≤ 1`. Integral monotonicity is applied only after the relevant integrability is established. Its conclusion is for each matrix entry indexed by `i,j`; it does not assert that the same numerical constant is already a dyadic operator-norm bound. The source states this scope correctly.

No PDE or scattering conclusion is encoded as a premise, and no unproved radial integrability fact is assumed. This review made no source or configuration changes.
