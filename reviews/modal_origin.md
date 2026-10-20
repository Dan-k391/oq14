# Actual regular dipole center extension

Source: `lean/ModalOrigin.lean`. This replaces the unfinished mathematical
obligation recorded in `modal_origin_resume.md`; that file remains a historical
checkpoint and does not describe the current source status.

The module has 44 explicitly qualified exports. The full source compiled
before the final axiom-report run. Evidence is `lean/logs/modal-origin-check.log`.

## What is proved

Repeated divided differences of the actual complex exponential have their
actual power series, factorial values at zero, and global complex
differentiability. The exact finite remainder identities prove

    psi_1(z) = z^2 F(z),  F(0)=1/3,  F'(0)=0,

where F is the explicitly defined entire even combination of the second and
third exponential divided differences. No asymptotic expansion is a premise.
The derivative identity for psi_1 is obtained from actual derivatives and
eventual equality.

The extended field coefficients are

    A(r)=kappa^2 [2F(kappa r)+(kappa r)F'(kappa r)],
    B(r)=-kappa^4 dslope(F',0)(kappa r),
    C(r)=i kappa^4 F(kappa r)/k.

They agree exactly with the earlier Riccati-defined fields for nonzero radius.
The derivative of F is entire, so its divided difference is entire as well.

Three proved real Frechet calculus lemmas handle the center: composing a
zero-derivative complex scalar with the radius has derivative zero; a
continuous coefficient times a coordinate has the expected linear derivative;
and a continuous coefficient times two coordinates has derivative zero.
These follow from actual little-o estimates, continuity, and bounded
coordinate linear maps.

Consequently E(0)=(2 kappa^2/3)e_z, DE(0)=0, H(0)=0, and the actual curl of H
is -2i kappa^4/(3k)e_z. The identity kappa^2=k^2 epsilon proves both Maxwell
curl equations at zero. Away from zero, exact field agreement transfers the
previous actual equations via equality of actual Frechet derivatives.
Every component is globally continuous and real differentiable.

The final existence theorem combines the proved scalar determinant roots and
actual interface matching with the explicit center extension. It constructs
nonzero transmitted dipole amplitudes with arbitrarily large frequency-to-decay
ratio; actual interior Maxwell equations hold at **every** point. Actual
exterior equations and tangential interface matching are retained, together
with a certified nonzero exterior trace.

## Self-audit

- Checked the normalization of psi_1/z^2 and the signs of both exponential
  arguments; the profile value 1/3 is the actual factorial coefficient.
- Differentiating psi_1=z^2 F gives the actual radial coefficient A; cancellation
  in B uses z dslope(F',0)=F'(z), with F'(0)=0 proved.
- The magnetic factor is i kappa^4/k, consistent with the earlier field
  definition and its kappa^2=k^2 epsilon relation.
- Center derivative proofs do not differentiate the norm at zero.
- Equality away from zero is used on an actual open punctured neighborhood,
  so its transfer to curls is valid.
- The final theorem does not take a determinant root, a regular-center
  extension, a Maxwell equation, or a matching condition as a premise.

## Remaining scope

This module does not yet assemble the piecewise interior/exterior field into a
global distributional transmission solution. It does not identify the scalar
matching residue with the full Maxwell operator residue, prove full
cross-degree isolation, or finish the continuum hotspot/channel formalization.
Those are separate obligations. There are no added axioms or unfinished proof
placeholders.
