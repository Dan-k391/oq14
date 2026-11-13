import FiniteAngularHerglotz
import RestrictedTEMaterial

/-! Continuity of the physical Herglotz electric field for arbitrary transverse L² input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FullChannelHerglotz
open Metric OQ14.Maxwell OQ14.HerglotzAngularL2
open scoped Topology

/-- The electric field of every transverse square-integrable angular amplitude is continuous.
The proof uses the existing uniform approximation by actual finite Maxwell waves. -/
theorem electric_continuous (k : ℝ) (F : ComplexVectorSphere.Ambient)
    (hF : ComplexVectorSphere.IsTangential F) (i : Fin 3) :
    Continuous (fun x : Maxwell.Space => HerglotzAngularL2.value k x i F) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨c, hc⟩ := HerglotzAngularL2.uniform_finite_approximation F hF (ε / 3) (by positivity)
  have hcont : Continuous (fun x : Maxwell.Space => HerglotzAngularL2.value k x i
      (HerglotzAngularL2.finiteAmplitude c)) := by
    have he := (FiniteAngularHerglotz.incident k c).smoothE i
    simpa only [FiniteAngularHerglotz.electric_value] using he.continuous
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuous_iff.mp hcont x (ε / 3) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have h1 := hc k x i
  have h2 := hc k y i
  have h3 := hnear y hy
  rw [dist_eq_norm] at h3 ⊢
  have ht : HerglotzAngularL2.value k y i F - HerglotzAngularL2.value k x i F =
      (HerglotzAngularL2.value k y i F - HerglotzAngularL2.value k y i (HerglotzAngularL2.finiteAmplitude c)) +
      (HerglotzAngularL2.value k y i (HerglotzAngularL2.finiteAmplitude c) - HerglotzAngularL2.value k x i (HerglotzAngularL2.finiteAmplitude c)) +
      (HerglotzAngularL2.value k x i (HerglotzAngularL2.finiteAmplitude c) - HerglotzAngularL2.value k x i F) := by ring
  rw [ht]
  have h2' : ‖HerglotzAngularL2.value k y i F - HerglotzAngularL2.value k y i (HerglotzAngularL2.finiteAmplitude c)‖ < ε/3 := by
    rw [norm_sub_rev]
    exact h2
  calc
    ‖_‖ ≤ ‖HerglotzAngularL2.value k y i F - HerglotzAngularL2.value k y i (HerglotzAngularL2.finiteAmplitude c)‖ +
        ‖HerglotzAngularL2.value k y i (HerglotzAngularL2.finiteAmplitude c) - HerglotzAngularL2.value k x i (HerglotzAngularL2.finiteAmplitude c)‖ +
        ‖HerglotzAngularL2.value k x i (HerglotzAngularL2.finiteAmplitude c) - HerglotzAngularL2.value k x i F‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ < ε := by linarith

/-- Arbitrary transverse input has a square-integrable electric restriction to each device ball. -/
theorem electric_memLp (k R : ℝ) (F : ComplexVectorSphere.Ambient)
    (hF : ComplexVectorSphere.IsTangential F) (i : Fin 3) :
    MeasureTheory.MemLp (fun x : Maxwell.Space => HerglotzAngularL2.value k x i F) 2
      (MeasureTheory.volume.restrict (Metric.closedBall 0 R)) := by
  exact SmallVolumeMaxwell.continuous_memLp_ball _ (electric_continuous k F hF i) R

/-- The actual weighted incident datum used in the material volume equation. -/
def datum (k : ℝ) (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F) :
    VectorFourier.VectorL2 :=
  IncidentLocalization.datum c d.radius (fun x i => HerglotzAngularL2.value k x i F)
    d.ballZero (electric_memLp k d.radius F hF)

/-- The datum is the physical electric field multiplied by the square root of susceptibility. -/
theorem datum_actual (k : ℝ) (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F) (i : Fin 3) :
    (fun x => datum k c d F hF (VectorFourier.coordinateMap x) i) =ᵐ[MeasureTheory.volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * HerglotzAngularL2.value k x i F :=
  IncidentLocalization.datum_actual c d.radius (fun x i => HerglotzAngularL2.value k x i F)
    d.ballZero (electric_memLp k d.radius F hF) i

/-- The actual volume solution for an arbitrary transverse L² angular illumination. -/
def solution (k : ℝ) (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F) :
    VectorFourier.VectorL2 := MaterialField.solution c k d.radius (datum k c d F hF)

/-- Invertibility of the physical volume block gives the self-consistent solution. -/
theorem solution_equation (k : ℝ) (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F)
    (hu : IsUnit (DynamicVolume.volumeBlock c k d.radius)) :
    DynamicVolume.volumeBlock c k d.radius (solution k c d F hF) = datum k c d F hF := by
  exact congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 => L (datum k c d F hF))
    (Ring.mul_inverse_cancel (DynamicVolume.volumeBlock c k d.radius) hu)

/-- The resulting compactly supported polarization equals susceptibility times the total field. -/
theorem solution_material_relation (k : ℝ) (c : StaticCoefficient.Coefficient)
    (d : BoundedMaterialKernel.SupportData c) (F : ComplexVectorSphere.Ambient)
    (hF : ComplexVectorSphere.IsTangential F) (hu : IsUnit (DynamicVolume.volumeBlock c k d.radius))
    (i : Fin 3) :
    DynamicVolume.source c (solution k c d F hF) i =ᵐ[MeasureTheory.volume] fun x =>
      (c.value (VectorFourier.coordinateMap x) : ℂ) *
        MaterialField.total c k (solution k c d F hF)
          (fun x i => HerglotzAngularL2.value k x i F) x i :=
  MaterialField.material_relation c k d.radius _ _ _ d.ballZero
    (datum_actual k c d F hF) (solution_equation k c d F hF hu) i

/-- The self-consistent polarization is an integrable compactly supported physical source. -/
theorem solution_source_integrable_compact (k : ℝ) (c : StaticCoefficient.Coefficient)
    (d : BoundedMaterialKernel.SupportData c) (F : ComplexVectorSphere.Ambient)
    (hF : ComplexVectorSphere.IsTangential F) (i : Fin 3) :
    MeasureTheory.Integrable (DynamicVolume.source c (solution k c d F hF) i) ∧
      HasCompactSupport (DynamicVolume.source c (solution k c d F hF) i) :=
  ⟨DynamicVolume.source_integrable c (solution k c d F hF) d.radius d.ballZero i,
    MaterialField.source_compact c (solution k c d F hF) d.radius d.ballZero i⟩

end OQ14.FullChannelHerglotz
#print axioms OQ14.FullChannelHerglotz.electric_continuous

#print axioms OQ14.FullChannelHerglotz.electric_memLp
#print axioms OQ14.FullChannelHerglotz.datum_actual

#print axioms OQ14.FullChannelHerglotz.solution_equation
#print axioms OQ14.FullChannelHerglotz.solution_material_relation

#print axioms OQ14.FullChannelHerglotz.solution_source_integrable_compact
