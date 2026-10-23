import RestrictedTEPlaneLocal
import ParityMaterialMaxwell
import IncidentLocalization

/-! Actual finite harmonic TE weighted data and their literal parity material inverse. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEMaterial
open MeasureTheory Metric Set Maxwell RestrictedTEFields RestrictedTEPlaneLocal SymmetricHarmonicJets
abbrev Space := FourierL2.Space
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

theorem electric_smooth (A : Index →₀ ℂ) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => electric A x i) :=
  contDiff_iff_contDiffAt.mpr (fun x => DebyeCalculus.toroidal_smooth _ x (potential_smooth 1 A).contDiffAt i)

theorem magnetic_smooth (A : Index →₀ ℂ) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => magnetic A x i) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact contDiffAt_const.mul (ExteriorClassical.curl_smooth _
    (DebyeCalculus.toroidal_smooth _ x (potential_smooth 1 A).contDiffAt) i)

theorem testMaxwell (A : Index →₀ ℂ) :
    MaterialMaxwell.TestMaxwell 1 (fun _ => 1) (electric A) (magnetic A) :=
  MaterialMaxwell.classical_vacuum_testMaxwell 1 _ _
    (fun i => (electric_smooth A i).of_le (by simp))
    (fun i => (magnetic_smooth A i).of_le (by simp))
    (fun x => RestrictedTEFields.maxwell 1 one_ne_zero A x)

theorem electric_memLp (A : Index →₀ ℂ) (R : ℝ) (i : Fin 3) :
    MemLp (fun x => electric A x i) 2 (volume.restrict (closedBall 0 R)) := by
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall (0 : Space) R).measure_lt_top⟩
  have hc := (electric_smooth A i).continuous
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : Space) R).exists_bound_of_continuousOn hc.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable.restrict B
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  exact hB x hx

def datum (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (A : Index →₀ ℂ) : VectorL2 :=
  IncidentLocalization.datum c d.radius (electric A) d.ballZero (electric_memLp A d.radius)

theorem datum_actual (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (A : Index →₀ ℂ) (i : Fin 3) :
    (fun x => datum c d A (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*electric A x i :=
  IncidentLocalization.datum_actual c d.radius (electric A) d.ballZero (electric_memLp A d.radius) i

theorem inverse_testMaxwell (c : Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (B : ℝ) (hsmall : ParityReactionVolume.perturbationBound d 1 B<1) (A : Index →₀ ℂ) :
    MaterialMaxwell.TestMaxwell 1 (MaterialMaxwell.dielectric c)
      (ParityMaterialField.total c 1 B (ParityMaterialField.solution d 1 B (datum c d A)) (electric A))
      (ParityMaterialMaxwell.magnetic c 1 B (ParityMaterialField.solution d 1 B (datum c d A)) (magnetic A)) :=
  ParityMaterialMaxwell.inverse_testMaxwell c d 1 B hsmall _ _ _ (datum_actual c d A)
    (fun i => (electric_smooth A i).continuous.locallyIntegrable)
    (fun i => (magnetic_smooth A i).continuous.locallyIntegrable) (testMaxwell A)

end OQ14.RestrictedTEMaterial
#print axioms OQ14.RestrictedTEMaterial.electric_smooth
#print axioms OQ14.RestrictedTEMaterial.magnetic_smooth
#print axioms OQ14.RestrictedTEMaterial.testMaxwell
#print axioms OQ14.RestrictedTEMaterial.electric_memLp
#print axioms OQ14.RestrictedTEMaterial.datum_actual
#print axioms OQ14.RestrictedTEMaterial.inverse_testMaxwell
