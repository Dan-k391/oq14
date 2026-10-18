# Actual spherical Maxwell interface matching

Source: `lean/ModalInterface.lean`; namespace `OQ14.ModalInterface`.

This module identifies the actual tangential traces of the constructed degree-one Maxwell dipole fields with the frozen two-amplitude matching map. The trace is the actual cross product with the real radius vector; on a positive-radius sphere this has the same equality condition as the unit-normal trace.

The interior electric and magnetic fields are the regular fields with internal wavenumber n*k, multiplied by a/n. The exterior fields are the outgoing fields at wavenumber k, multiplied by b. Actual cross-product calculation gives electric trace coefficients a*k*psiD(n*k*r)/r and b*k*xiD(k*r)/r, and magnetic coefficients i*k*n*psi(n*k*r)*a/r² and i*k*xi(k*r)*b/r². Thus the normalization agrees exactly with the previously defined matching rows, rather than assuming that agreement.

The proof establishes both directions. Matching coefficients imply equality of both actual tangential traces at every point of the sphere. Conversely, equality of the sphere traces, evaluated at an actual nonzero equatorial point, recovers both scalar matching rows. The determinant-zero/nonzero-kernel result then gives determinant zero if and only if there is a nonzero amplitude pair satisfying the actual interface traces.

The nontriviality is also checked at field level. The regular/outgoing Wronskian is derived from the already proved Hankel Wronskian. Both matching amplitudes must be nonzero, and a nonzero outgoing amplitude has a nonzero electric or magnetic trace at an explicit equatorial point. The equivalence cannot be satisfied merely by nonzero labels attached to zero fields.

Actual component differentiability of the electric and magnetic fields is proved from their radial formulas. Complex-frequency Maxwell scaling follows from the actual curl product rules. The interior scaled fields satisfy Maxwell with permittivity n² and the exterior fields with permittivity 1, at every nonzero point. The final theorem uses the already constructed high-quality simple determinant zeros to produce actual nonzero transmission fields on the unit sphere for every real n>1 and every prescribed frequency-to-decay ratio. It has no determinant-zero, field-existence, Maxwell-equation, or matching-equivalence premise.

The interior field is still only asserted to satisfy Maxwell away from the origin. Origin removability, a globally assembled weak interface solution, outgoing resolvent identification, and full angular-degree isolation remain separate formal obligations. No such global conclusion is claimed here.

Self-audit checked the a/n normalization, all four tangential coefficients, determinant sign, both implication directions, the equatorial nontriviality argument, the actual complex Maxwell scaling, and the final unconditional high-quality construction. All 23 fully qualified exports compile with only standard axioms and no proof placeholders. Evidence: `lean/logs/modal-interface-check.log`.
