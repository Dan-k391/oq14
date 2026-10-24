import RestrictedTEMaterial
import RestrictedTEPartnerBalls

/-! Half-turn covariance of the finite restricted TE incident fields and half-turn-fixed weighted datum.

The finite TE potentials are built from the half-turn projected harmonic polynomials
(`RestrictedTEIncoming.polynomial q = EvenHarmonicProjection.project ...`), so the incident fields of every
coefficient vector `A : Index →₀ ℂ` (in particular of every output of `PhysicalTEBandInterpolation.interpolate`)
are automatically in the even half-turn sector; no further sector hypothesis on `A` is needed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEEvenDatum
open MeasureTheory Complex Maxwell RestrictedTEPlaneLocal SymmetricHarmonicJets
abbrev Space := FourierL2.Space

theorem halfTurn_eq_rot (x : Space) :
    HalfTurnMaxwellParity.halfTurn x=HalfTurnVectorAction.rot x := by
  rw [HalfTurnMaxwellParity.halfTurn_apply]
  exact (HarmonicHalfTurn.rotation_apply x).symm

/-- The incident electric field of every finite restricted TE coefficient vector is half-turn invariant. -/
theorem electric_invariant (A : Index →₀ ℂ) : HalfTurnMaxwellParity.Invariant (electric A) :=
  RestrictedTEFields.electric_half_turn 1 A

/-- The incident magnetic field of every finite restricted TE coefficient vector is half-turn invariant. -/
theorem magnetic_invariant (A : Index →₀ ℂ) : HalfTurnMaxwellParity.Invariant (magnetic A) := by
  have hf : ∀ j, Differentiable ℝ (fun x : Space =>
      DebyeCalculus.toroidal (RestrictedTEFields.potential 1 A) x j) := fun j x =>
    (DebyeCalculus.toroidal_smooth _ x (RestrictedTEFields.potential_smooth 1 A).contDiffAt j).differentiableAt
      (by simp)
  have hT : HalfTurnMaxwellParity.Invariant (DebyeCalculus.toroidal (RestrictedTEFields.potential 1 A)) :=
    HalfTurnMaxwellParity.toroidal_invariant _ (RestrictedTEFields.potential_smooth 1 A)
      (RestrictedTEFields.potential_half_turn 1 A)
  intro x i
  have hc := HalfTurnMaxwellParity.curl_invariant _ hf hT x i
  change (-I/((1 : ℝ) : ℂ))*curl (DebyeCalculus.toroidal (RestrictedTEFields.potential 1 A)) (HalfTurnMaxwellParity.halfTurn x) i=
    -(SphereReactionKernel.sign i : ℂ)*((-I/((1 : ℝ) : ℂ))*curl (DebyeCalculus.toroidal
      (RestrictedTEFields.potential 1 A)) x i)
  rw [hc]
  ring

/-- Pointwise covariance of the incident electric field under the half-turn action `x ↦ rot x`,
in the form used by `HalfTurnVectorAction.U_eq_iff`. -/
theorem electric_rot (A : Index →₀ ℂ) (x : Space) (i : Fin 3) :
    electric A (HalfTurnVectorAction.rot x) i=(HalfTurnVectorAction.o i : ℂ)*electric A x i := by
  have h := electric_invariant A x i
  rw [halfTurn_eq_rot] at h
  rw [h]
  simp [HalfTurnVectorAction.o]

theorem magnetic_rot (A : Index →₀ ℂ) (x : Space) (i : Fin 3) :
    magnetic A (HalfTurnVectorAction.rot x) i=(HalfTurnVectorAction.o i : ℂ)*magnetic A x i := by
  have h := magnetic_invariant A x i
  rw [halfTurn_eq_rot] at h
  rw [h]
  simp [HalfTurnVectorAction.o]

/-- The weighted datum of a half-turn symmetric coefficient and any finite restricted TE incident field is
half-turn fixed. -/
theorem datum_fixed (c : StaticCoefficient.Coefficient) (hsym : HalfTurnVectorAction.Symmetric c)
    (d : BoundedMaterialKernel.SupportData c) (A : Index →₀ ℂ) :
    HalfTurnVectorAction.U (RestrictedTEMaterial.datum c d A)=RestrictedTEMaterial.datum c d A := by
  rw [HalfTurnVectorAction.U_eq_iff]
  intro j
  filter_upwards [HalfTurnVectorAction.ae_rot (RestrictedTEMaterial.datum_actual c d A j),
    RestrictedTEMaterial.datum_actual c d A j] with x h1 h2
  rw [h1, h2, hsym x, electric_rot A x j]
  ring

/-- The datum of the partner-ball coefficient is half-turn fixed. -/
theorem partner_datum_fixed {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Space) (r : ι → ℝ) (χ : ℝ)
    (hχ : 0≤χ) (R : ℝ) (hinside : ∀ l, ‖p l‖+r l≤R) (A : Index →₀ ℂ) :
    HalfTurnVectorAction.U (RestrictedTEMaterial.datum (RestrictedTEPartnerBalls.partnerCoefficient p r χ hχ)
      (RestrictedTEPartnerBalls.partnerSupport p r χ hχ R hinside) A)=
    RestrictedTEMaterial.datum (RestrictedTEPartnerBalls.partnerCoefficient p r χ hχ)
      (RestrictedTEPartnerBalls.partnerSupport p r χ hχ R hinside) A :=
  datum_fixed _ (RestrictedTEPartnerBalls.partner_symmetric p r χ hχ) _ A

/-- Every linear combination of finite restricted TE incident fields gives a half-turn fixed datum. -/
theorem datum_fixed_comb (c : StaticCoefficient.Coefficient) (hsym : HalfTurnVectorAction.Symmetric c)
    (d : BoundedMaterialKernel.SupportData c) {κ : Type*} [Fintype κ] (A : κ → Index →₀ ℂ) (cf : κ → ℂ) :
    HalfTurnVectorAction.U (RestrictedTEMaterial.datum c d (∑ k, cf k • A k))=
      RestrictedTEMaterial.datum c d (∑ k, cf k • A k) :=
  datum_fixed c hsym d _

end OQ14.RestrictedTEEvenDatum
#print axioms OQ14.RestrictedTEEvenDatum.halfTurn_eq_rot
#print axioms OQ14.RestrictedTEEvenDatum.electric_invariant
#print axioms OQ14.RestrictedTEEvenDatum.magnetic_invariant
#print axioms OQ14.RestrictedTEEvenDatum.electric_rot
#print axioms OQ14.RestrictedTEEvenDatum.magnetic_rot
#print axioms OQ14.RestrictedTEEvenDatum.datum_fixed
#print axioms OQ14.RestrictedTEEvenDatum.partner_datum_fixed
#print axioms OQ14.RestrictedTEEvenDatum.datum_fixed_comb
