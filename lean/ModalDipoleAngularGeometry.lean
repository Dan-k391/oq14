import ModalDipoleSlice
import AngularPowerZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ModalDipoleAngularGeometry
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower
  OQ14.ModalDipoleAngularProjection OQ14.ComplexVectorSphere
open scoped ComplexInnerProductSpace

theorem pointwise_orthogonal (n : Sphere) : ⟪radialMap n, poloidalMap n⟫ = (0 : ℂ) := by
  have hn := GreenKernel.coordinate_squares (n : Space)
  rw [sphere_norm] at hn
  have hc : ∑ i : Fin 3, ((n : Space) i : ℂ)^2 = 1 := by
    simpa [Fin.sum_univ_three] using hn
  simp only [radialMap, poloidalMap, ContinuousMap.sub_apply, ContinuousMap.const_apply,
    axis, PiLp.inner_apply, PiLp.sub_apply, PiLp.smul_apply, embed_apply,
    WithLp.equiv_symm_pi_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, RCLike.inner_apply,
    Complex.conj_ofReal, map_mul, map_sub, map_one, map_zero]
  simp only [embed_apply, Complex.conj_ofReal, Fin.sum_univ_three] at hc ⊢
  norm_num at hc ⊢
  simp only [embed_apply, Complex.conj_ofReal] at *
  linear_combination (-((n : Space) 2 : ℂ)^2) * hc

theorem orthogonal : ⟪radialMode, poloidalMode⟫ = (0 : ℂ) := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [radialMap.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
    poloidalMap.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n hr hp
  change radialMode n = radialMap n at hr
  change poloidalMode n = poloidalMap n at hp
  rw [hr,hp]
  exact pointwise_orthogonal n
theorem radial_ne_zero : radialMode ≠ 0 := by
  intro hz
  have ha : (radialMap : Sphere → ComplexVectorSphere.Vector) =ᵐ[angularMeasure] fun _ => 0 := by
    filter_upwards [radialMap.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
      Lp.coeFn_zero ComplexVectorSphere.Vector 2 angularMeasure] with ω h1 h0
    change radialMode ω = radialMap ω at h1
    rw [hz, h0] at h1
    exact h1.symm
  have he := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae ha) isOpen_univ radialMap.continuous.continuousOn
    continuous_const.continuousOn
  let p : Sphere := ⟨basis 2, by simp [Metric.mem_sphere, dist_zero_right, basis]⟩
  have hp := congrArg (fun v : ComplexVectorSphere.Vector => v 2) (he (Set.mem_univ p))
  simp [p, radialMap, embed_apply, basis, EuclideanSpace.single_apply, PiLp.smul_apply] at hp

theorem poloidal_ne_zero : poloidalMode ≠ 0 := by
  intro hz
  have ha : (poloidalMap : Sphere → ComplexVectorSphere.Vector) =ᵐ[angularMeasure] fun _ => 0 := by
    filter_upwards [poloidalMap.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
      Lp.coeFn_zero ComplexVectorSphere.Vector 2 angularMeasure] with ω h1 h0
    change poloidalMode ω = poloidalMap ω at h1
    rw [hz, h0] at h1
    exact h1.symm
  have he := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae ha) isOpen_univ poloidalMap.continuous.continuousOn
    continuous_const.continuousOn
  let p : Sphere := ⟨basis 0, by simp [Metric.mem_sphere, dist_zero_right, basis]⟩
  have hp := congrArg (fun v : ComplexVectorSphere.Vector => v 2) (he (Set.mem_univ p))
  simp [p, poloidalMap, radialMap, axis, embed_apply, basis, EuclideanSpace.single_apply,
    PiLp.smul_apply, PiLp.sub_apply, WithLp.equiv_symm_pi_apply] at hp

theorem coefficients_unique (a b : ℂ) (h : a • radialMode + b • poloidalMode = 0) :
    a = 0 ∧ b = 0 := by
  have hr : ⟪radialMode, radialMode⟫ ≠ (0 : ℂ) := by
    intro hzero
    exact radial_ne_zero (inner_self_eq_zero.mp hzero)
  have hp : ⟪poloidalMode, poloidalMode⟫ ≠ (0 : ℂ) := by
    intro hzero
    exact poloidal_ne_zero (inner_self_eq_zero.mp hzero)
  have hpr : ⟪poloidalMode, radialMode⟫ = (0 : ℂ) := by
    rw [← inner_conj_symm, orthogonal]
    simp
  have ha := congrArg (fun v => ⟪radialMode, v⟫) h
  have hb := congrArg (fun v => ⟪poloidalMode, v⟫) h
  simp only [inner_add_right, inner_smul_right, orthogonal, hpr, mul_zero, add_zero,
    zero_add, inner_zero_right] at ha hb
  exact ⟨(mul_eq_zero.mp ha).resolve_right hr, (mul_eq_zero.mp hb).resolve_right hp⟩

def explicitProjection (F : ComplexVectorSphere.Ambient) : ComplexVectorSphere.Ambient :=
  (⟪radialMode,F⟫ / ⟪radialMode,radialMode⟫) • radialMode +
    (⟪poloidalMode,F⟫ / ⟪poloidalMode,poloidalMode⟫) • poloidalMode

theorem explicitProjection_eq (F : ComplexVectorSphere.Ambient) :
    projection F = explicitProjection F := by
  have hr : ⟪radialMode,radialMode⟫ ≠ (0 : ℂ) := fun h => radial_ne_zero (inner_self_eq_zero.mp h)
  have hp : ⟪poloidalMode,poloidalMode⟫ ≠ (0 : ℂ) := fun h => poloidal_ne_zero (inner_self_eq_zero.mp h)
  have hpr : ⟪poloidalMode,radialMode⟫ = (0 : ℂ) := by rw [← inner_conj_symm, orthogonal]; simp
  have hm : explicitProjection F ∈ dipoleSpace := by
    exact dipoleSpace.add_mem (dipoleSpace.smul_mem _ (Submodule.subset_span (by simp)))
      (dipoleSpace.smul_mem _ (Submodule.subset_span (by simp)))
  have hR : ⟪radialMode, F-explicitProjection F⟫ = (0 : ℂ) := by
    simp only [explicitProjection, inner_sub_right, inner_add_right, inner_smul_right,
      orthogonal, mul_zero, add_zero]
    field_simp
  have hP : ⟪poloidalMode, F-explicitProjection F⟫ = (0 : ℂ) := by
    simp only [explicitProjection, inner_sub_right, inner_add_right, inner_smul_right,
      hpr, mul_zero, zero_add]
    field_simp
  have hk : dipoleSpace ≤ LinearMap.ker (innerSL ℂ (F-explicitProjection F)).toLinearMap := by
    apply Submodule.span_le.mpr
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · change ⟪F-explicitProjection F,radialMode⟫ = 0
      exact inner_eq_zero_symm.mpr hR
    · change ⟪F-explicitProjection F,poloidalMode⟫ = 0
      exact inner_eq_zero_symm.mpr hP
  change ((dipoleSpace.orthogonalProjection F : dipoleSpace) : ComplexVectorSphere.Ambient) = _
  apply dipoleSpace.eq_orthogonalProjection_of_mem_of_inner_eq_zero hm
  intro v hv
  exact hk hv

#print axioms OQ14.ModalDipoleAngularGeometry.explicitProjection_eq
#print axioms OQ14.ModalDipoleAngularGeometry.coefficients_unique
#print axioms OQ14.ModalDipoleAngularGeometry.radial_ne_zero
#print axioms OQ14.ModalDipoleAngularGeometry.poloidal_ne_zero
#print axioms OQ14.ModalDipoleAngularGeometry.pointwise_orthogonal
#print axioms OQ14.ModalDipoleAngularGeometry.orthogonal
end OQ14.ModalDipoleAngularGeometry







