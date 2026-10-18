# Actual lower-half-plane TM zeros and large decay ratios

Source: `lean/ModalAsymptotics.lean`; namespace `OQ14.ModalAsymptotics`.

This module sharpens the actual root construction from `ModalExistence`. It makes the displacement from each sufficiently distant constant-quotient exponential root smaller than any prescribed positive epsilon. The logarithmic correction is an actual C1 function near zero; continuity adds the small-correction neighborhood before choosing the closed ball for the already proved contraction. No root proximity is an assumption.

The exact exponential centers are `(log(q)+2*pi*i*m)/(i*b)` for positive real b. Actual complex arithmetic proves their exponential equation, their unbounded real parts, and the exact constant imaginary part `-log(norm(q))/b`. Thus actual inverse-polynomial quotient roots have arbitrarily large real part and lie within any prescribed vertical distance of that horizontal line.

For every natural angular degree and every real refractive index n>1, the actual TM constant matching quotient has norm `(n+1)/(n-1)>1`. The preceding exact factorization converts the quotient roots to zeros of the actual TM determinant. The finite multiple-zero set from `ModalRational` then gives simple determinant zeros with arbitrarily large real part and arbitrarily small vertical displacement from

`Im(z) = -log((n+1)/(n-1))/(2*n)`.

In particular, for every lower bound L and every nonnegative target Q, the last theorem constructs an actual nonzero simple determinant zero z with `Re(z)>L`, `Im(z)<0`, and `Q<Re(z)/(-2*Im(z))`. The proof takes the vertical error smaller than half the positive decay-line height and then makes the real part sufficiently large. No algebraicity or transcendence assumption is used for this fixed-degree conclusion.

The claims remain scalar determinant claims. The module does not identify an outgoing Maxwell operator eigenvalue, establish its full algebraic multiplicity, or exclude coincidence with every other angular degree. The countably infinite cross-degree isolation issue and operator identification remain separate formal obligations. The theorem names and comments explicitly preserve this distinction.

Self-audit checked the logarithm neighborhood, fixed-point nonvanishing, exact real/imaginary center formulas, real-index quotient norm, finite-exception argument, and sign of the quality ratio denominator. All 11 fully qualified exports compile with only standard axioms, without lints, `sorry`, `admit`, or new axioms. Evidence: `lean/logs/modal-asymptotics-check.log`.

An independent read-only audit of `HelmholtzProjection.lean` was also completed during this work. Its actual Fourier-coordinate annihilator, compact smooth test separation, a.e. symbol argument, and closed-gradient orthogonal projection characterization are sound and noncircular; its author and the parent were notified.
