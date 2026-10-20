# Complex-frequency physical dynamic remainder

Source: `lean/ComplexDynamicKernel.lean`.

SHA256: `29E38E19E51E46DC62A7F32408E33665DCFBDD03B78C237EED3F5607C7ACF661`.

Pinned Lean 4.19 source compilation with direct olean emission passed on 2026-10-20 (compiler exit 0). All fourteen theorem exports have matching axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent full conceptual audit passed at this exact hash. The source is frozen at the hash above.

The dyadic is k squared times the physical scalar kernel on the diagonal plus its actual spatial Hessian. Subtracting the zero-frequency Hessian gives the physical remainder. Exact identities restrict both objects to the existing real-frequency dyadic and remainder.

The existing transverse and radial cancellation polynomials retain a second-order zero at the origin. Taylor estimates for norm at most one and polynomial estimates outside this ball prove bounds 4 exp(norm z) norm(z)^2 and 10 exp(norm z) norm(z)^2. Normalized coordinate products have norm at most one. The exact remainder formula therefore gives the global pointwise bound 14 exp(norm(k) norm(x)) norm(k)^2/(4 pi norm(x)) away from zero. On a ball of radius R this yields the stated bound with exp(norm(k) R). The exact totalized value at zero is zero.

Actual measurability and the established three-dimensional inverse-radius L1/L2 estimates prove local L1 and L2 on every finite closed ball, plus local integrability on every compact set. There is no frequency smallness condition. These are physical complex-frequency kernel estimates; operator-valued analyticity and a meromorphic Fredholm inverse remain separate obligations.
