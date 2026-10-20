# Actual convolution regularization of weak Helmholtz fields

Source: `lean/WeakHelmholtzRegularity.lean`.

SHA256: `7ED5311FF11854BCD6343CEB47DA642703782864B63D84D1AD4E6404C4DA5D41`.

Pinned Lean 4.19 compilation and direct olean emission passed with exit 0 and no warnings on 2026-10-20. All seven exported theorem dependency reports contain only `propext`, `Classical.choice`, and `Quot.sound`. Root's independent complete-source mathematical audit and independent compiler check passed at this exact hash. The source is frozen.

The actual weak Helmholtz predicate is the literal bilateral compact smooth test integral on the given domain, at arbitrary complex frequency. For a globally locally integrable complex function and a genuine smooth compact kernel, Bochner convolution is globally smooth. Both first and second actual spatial coordinate derivatives of this convolution are proved to equal the integrals with the corresponding actual kernel derivatives. No derivative of the original weak function is assumed.

The weak equation is tested with the literal translated reflection of the kernel. The two reflected derivative signs cancel in its Laplacian. The first and second kernel derivative products are actually integrable; finite summation and integration then prove the actual classical Helmholtz equation for the smoothed field at every point whose reflected kernel support lies inside the weak-equation domain.

The actual reflected topological support is contained in the inverse image of the original kernel support. If that kernel support lies in the actual closed ball of radius epsilon, the triangle inequality places every shifted support inside the larger ball whenever the target point lies in the ball with radius reduced by epsilon. This yields a genuine smaller-ball classical PDE for the regularizations, with no assumed support separation or regularity of the weak field.

This source proves actual local regularization. Existence of a smooth representative of the original weak field, and passage from the smoothed representation through a convergence theorem, remain separate obligations.
