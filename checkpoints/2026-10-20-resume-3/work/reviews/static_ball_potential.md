# Actual C1 potential of a uniform ball

Source: `lean/StaticBallPotential.lean`.
SHA256: `47CCC48BF55DA2BF9DAFABB918D749F1B6CC5FF7F902A95C590948E66B1D507C`.

Author pinned Lean 4.19 compilation and object emission completed with exit 0,
without warnings. All 14 selected reports are standard-only. Importable
object: 570392 bytes. Independent review is pending.

The scalar radial function is explicitly R^2/2-r^2/6 inside and R^3/(3*r)
outside. For R>0 the boundary values and first radial derivatives match.
The actual derivative is proved on both regions and at the boundary by
joining the two within-set derivatives. Its derivative is globally
continuous. The spatial potential is therefore continuous, with the explicit
Frechet derivative force(R,norm(x))*inner(x,·). At the origin the quadratic
interior formula proves the derivative directly. The force coefficient is
continuous across the sphere, giving a genuine globally C1 potential.

These are actual calculus statements, with no assumed boundary matching,
PDE source or operator identity. The scalar function itself is not placed
in L2. Global weak Laplacian/Hessian, L2 gradient/Hessian construction, and
identification with the actual Newton/projection operator remain subsequent
obligations. In particular no exact -P/3 depolarization is claimed yet.
