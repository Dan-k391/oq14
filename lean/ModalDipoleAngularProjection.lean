import ModalVectorAngularSlices
import ModalOrigin
import ModalVolumeData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ModalDipoleAngularProjection
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.ModalOrigin
  OQ14.ModalDipole OQ14.ComplexVectorSphere
open scoped ComplexInnerProductSpace

def axis : ComplexVectorSphere.Vector := (WithLp.equiv 2 (Fin 3 → ℂ)).symm ![0,0,1]

def radialMap : C(Sphere, ComplexVectorSphere.Vector) :=
  ⟨fun n => ((n : Space) 2 : ℂ) • embedVector (n : Space), by
    have hc : Continuous (fun n : Sphere => ((n : Space) 2 : ℂ)) := by
      simpa only [Function.comp_def] using (coordinate 2).continuous.comp continuous_subtype_val
    exact hc.smul (embedVector.continuous.comp continuous_subtype_val)⟩

def poloidalMap : C(Sphere, ComplexVectorSphere.Vector) :=
  ContinuousMap.const Sphere axis - radialMap

def radialMode : ComplexVectorSphere.Ambient := ContinuousMap.toLp 2 angularMeasure ℂ radialMap

def poloidalMode : ComplexVectorSphere.Ambient := ContinuousMap.toLp 2 angularMeasure ℂ poloidalMap

def dipoleSpace : Submodule ℂ ComplexVectorSphere.Ambient := Submodule.span ℂ {radialMode,poloidalMode}

instance : FiniteDimensional ℂ dipoleSpace :=
  FiniteDimensional.span_of_finite ℂ (Set.toFinite {radialMode,poloidalMode})

def projection : ComplexVectorSphere.Ambient →L[ℂ] ComplexVectorSphere.Ambient :=
  dipoleSpace.subtypeL.comp dipoleSpace.orthogonalProjection

theorem projection_fixed (v : ComplexVectorSphere.Ambient) (hv : v ∈ dipoleSpace) : projection v = v := by
  change ((dipoleSpace.orthogonalProjection v : dipoleSpace) : ComplexVectorSphere.Ambient) = v
  rw [dipoleSpace.orthogonalProjection_mem_subspace_eq_self ⟨v,hv⟩]

def electricMap (k : ℂ) (r : ℝ) : C(Sphere, ComplexVectorSphere.Vector) :=
  ⟨fun n => (WithLp.equiv 2 (Fin 3 → ℂ)).symm (centerE k (r • (n : Space))), by
    apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
    apply continuous_pi
    intro i
    exact (centerE_continuous k i).comp (continuous_const.smul continuous_subtype_val)⟩

theorem electricMap_decomposition (k : ℂ) (r : ℝ) (hr : 0 < r) :
    electricMap k r = (centerA k r) • poloidalMap +
      (centerA k r + (r : ℂ)^2 * centerB k r) • radialMap := by
  ext n i
  have hnorm : ‖r • (n : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hr]
  fin_cases i <;> simp [electricMap, centerE, axisField, radialMap, poloidalMap, axis,
    embed_apply, WithLp.equiv_symm_pi_apply, hnorm, PiLp.smul_apply, ofReal_mul] <;> ring

theorem dipole_slice_mem (k : ℂ) (r : ℝ) (hr : 0 < r) :
    ContinuousMap.toLp 2 angularMeasure ℂ (electricMap k r) ∈ dipoleSpace := by
  rw [electricMap_decomposition k r hr, map_add, map_smul, map_smul]
  change (centerA k r) • poloidalMode + (centerA k r + (r : ℂ)^2 * centerB k r) • radialMode ∈ dipoleSpace
  exact dipoleSpace.add_mem (dipoleSpace.smul_mem _ (Submodule.subset_span (by simp)))
    (dipoleSpace.smul_mem _ (Submodule.subset_span (by simp)))

theorem dipole_slice_projected (k : ℂ) (r : ℝ) (hr : 0 < r) :
    projection (ContinuousMap.toLp 2 angularMeasure ℂ (electricMap k r)) =
      ContinuousMap.toLp 2 angularMeasure ℂ (electricMap k r) :=
  projection_fixed _ (dipole_slice_mem k r hr)

#print axioms OQ14.ModalDipoleAngularProjection.projection_fixed
#print axioms OQ14.ModalDipoleAngularProjection.electricMap_decomposition
#print axioms OQ14.ModalDipoleAngularProjection.dipole_slice_projected
end OQ14.ModalDipoleAngularProjection




