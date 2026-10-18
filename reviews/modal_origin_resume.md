# Modal center extension: paused draft checkpoint

The user requested a checkpoint. No compiler session is pending. Last session
40024 completed with exit code 1. The draft is `lean/ModalOrigin.lean` and is
NOT a verified export or part of the frozen formal release.

## Frozen immediately preceding module

`lean/ModalInterface.lean` is frozen, with all 23 qualified exports checked
using only `propext`, `Classical.choice`, and `Quot.sound`.

- Source SHA256: `423E94CB77C3F612B8E882708D986B641D6311BA1605ADFDC34F78F8E268E195`.
- Review SHA256: `A876E8F2AFF69F2312C9DC2E417F0EF6FBD3E3D90F9943090EC62B4CF11A7BB4`.
- Evidence: `lean/logs/modal-interface-check.log`.
- Parent targeted build passed; parent and channels independently audited.
- Importable ModalInterface and ModalDipole oleans are ready.

It proves actual tangential transmission iff the degree-one determinant
vanishes, nonzero amplitudes and exterior traces, actual Maxwell equations
away from the center, and unconditional high-Q transmission-field existence.
It does not claim origin removability or a global weak assembled solution.

## Current draft route

Define E_m by m repeated divided differences of exp at zero. Then
E_m(0)=1/m!, every E_m is entire, and z E_(m+1)=E_m-1/m!.
Define the entire even function

F(z) = [E_2(iz)+E_2(-iz)-E_3(iz)-E_3(-iz)]/2.

Its value is F(0)=1/3 and F'(0)=0. Algebra gives psi_1(z)=z^2 F(z)
for nonzero z and hence psi_1'(z)=2zF(z)+z^2 F'(z).
These are actual definitions and derivations, not assumed expansions.

The following draft proofs elaborate without errors (but some depend on
currently failing predecessors, so they are NOT frozen verified results):
expTail_series, expTail_differentiable, expTail_step,
profile_differentiable, profile_zero, profile_hasDerivAt_zero,
expTail_three_identity, psiD_profile.

## Exact current compile errors (three)

1. `expTail_zero`, line 37: after `coeff_zero`, `coeff_iterate_fslope`, and
   unfolding coeff, target is
   `(NormedSpace.expSeries C C (0+m)) 1 = (m.factorial:C)^(-1)`.
   `change ... m (fun _ => 1)` fails to be definitionally equal. Resolve
   the dependent zero-add/index and constant tuple coercion explicitly;
   `NormedSpace.expSeries_apply_eq` or `expSeries_eq_ofScalars` should finish.
   The mathematical coefficient identity is exact.
2. `expTail_two_identity`, line 82: h0 was simplified using `[expTail]` but
   h1 retains `expTail 1 z`; `linear_combination` leaves their definitionally
   equal representations as separate atoms. Normalize both to the same form
   (or retain `expTail` in h0, simplifying only its zero iterate).
3. `psi_profile`, line 101: current `field_simp` plus chosen linear combination
   overclears denominators and fails. Better first solve the two exact tail
   identities for E_2(plus/minus iz), E_3(plus/minus iz), substitute, and
   normalize I^2=-1 and `-I*z=-(I*z)` before clearing denominators. Alternatively
   establish the polynomial numerator identity and cancel one nonzero z.

No missing theorem or mathematical counterexample was discovered. These are
local algebra/elaboration errors. No `sorry`, `admit`, or extra axioms were added.

## Next proof steps after these errors

1. Entire F implies entire F'. Define J(z)=dslope F' 0 z, so z J(z)=F'(z)
   because F'(0)=0. J is continuous, including zero; its exact value at zero
   is unnecessary for first derivatives of the vector field.
2. Rewrite the actual regular radial fields, with z=kappa r, as
   A(r)=kappa^2 [2F(z)+zF'(z)], B(r)=-kappa^4 J(z),
   C(r)=i kappa^4/k F(z). Define extended E=axisField A B and H=swirlField C.
   These agree with regularE/H for x != 0.
3. A(0)=2 kappa^2/3 and A'(0)=0. Prove the general radial zero-derivative
   lemma: if HasDerivAt A 0 0 then x -> A(norm x) has Frechet derivative zero
   at zero. Use `hasDerivAt_iff_isLittleO`, composition with continuous norm,
   then `isLittleO_norm_right` and `hasFDerivAt_iff_isLittleO_nhds_zero`.
4. Continuous B times quadratic coordinate products has derivative zero at
   zero. Continuous C times linear coordinates has its expected linear
   derivative. Thus E(0)=(2 kappa^2/3)e_z, DE(0)=0,
   H(0)=0, DH(0) is i kappa^4/(3k) times x cross e_z.
5. Compute actual coordinate curls at zero: curl E=0=ikH and
   curl H=-2i kappa^4/(3k)e_z=-ik epsilon E if kappa^2=k^2 epsilon.
6. Transfer away-from-zero Maxwell using eventual equality and existing
   regular_dipole_maxwell, then extend ModalInterface existence to an interior
   field satisfying actual pointwise Maxwell at the center too.
7. A global weak assembled interface solution and cross-degree operator
   isolation remain separate. Do not claim full continuum Lean completion.

## Environment and commands

PowerShell cwd `D:/oq14/lean`:

    & '../.tools/lean/lean-4.19.0-windows/bin/lake.exe' env lean ModalOrigin.lean

Parent fetched pinned `Mathlib.Analysis.Complex.RemovableSingularity` and
dependencies; IsolatedZeros and SpecialFunctions.Exponential are also available.
Do not modify frozen modules, shared Lake config, or Git. Parent registers
new modules and builds their importable oleans after review. Qualify all
eventual `#print axioms` outside the namespace.

## Independent audit completed during this turn

Read all of channels' `lean/NewtonHessian.lean`: inverse Fourier signs,
distributional Hessian, retained source term Delta N=-delta, bounded symbol,
and actual physicalProjection multiplier all pass. Sent parent and channels
the audit. No spatial L2 convolution theorem is claimed by that module.
