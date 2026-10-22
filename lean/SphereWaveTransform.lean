import SphereReactionKernel
import SphereAxialMeasure
import SphereAngularSymmetry
import Mathlib.Analysis.InnerProductSpace.Projection

/-! The actual complex sphere wave integral, evaluated by axial coordinates and reflection. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SphereWaveTransform
open MeasureTheory Metric Set SphereReactionKernel
open scoped InnerProductSpace Topology

def scalar (k : ℝ) (x : Space) : ℂ := ∫ θ : Sphere, wave k x θ ∂surface

theorem integral_axial (f : Space → ℂ) (hf : Integrable (fun θ : Sphere => f θ) surface) :
    (∫ θ : Sphere, f θ ∂surface) =
      ∫ z in Ioo (-1 : ℝ) 1, ∫ t in Ioo (-Real.pi) Real.pi,
        f (AxialCoordinates.physical ![1,z,t]) := by
  have hm : AEStronglyMeasurable (fun θ : Sphere => f θ)
      (Measure.map SphereAxialMeasure.direction SphereAxialMeasure.parameterMeasure) := by
    rw [SphereAxialMeasure.direction_preserving.map_eq]
    exact hf.aestronglyMeasurable
  have he : (∫ θ : Sphere, f θ ∂surface) =
      ∫ q, f (SphereAxialMeasure.direction q : Space) ∂SphereAxialMeasure.parameterMeasure := by
    change (∫ θ : Sphere, f θ ∂AngularPower.angularMeasure) = _
    rw [← SphereAxialMeasure.direction_preserving.map_eq]
    exact integral_map SphereAxialMeasure.direction_preserving.measurable.aemeasurable hm
  have hp := (SphereAxialMeasure.direction_preserving.integrable_comp hf.aestronglyMeasurable).mpr hf
  have hi : IntegrableOn (fun q : ℝ × ℝ => f (AxialCoordinates.physical ![1,q.1,q.2]))
      SphereAxialMeasure.angularDomain := by
    rw [IntegrableOn, ← map_comap_subtype_coe SphereAxialMeasure.angularDomain_open.measurableSet]
    exact (MeasurableEmbedding.subtype_coe SphereAxialMeasure.angularDomain_open.measurableSet).integrable_map_iff.mpr hp
  rw [he]
  calc
    _ = ∫ q in SphereAxialMeasure.angularDomain, f (AxialCoordinates.physical ![1,q.1,q.2]) :=
      integral_subtype_comap SphereAxialMeasure.angularDomain_open.measurableSet
        (fun q : ℝ × ℝ => f (AxialCoordinates.physical ![1,q.1,q.2]))
    _ = _ := setIntegral_prod _ hi

theorem wave_integrable (k : ℝ) (x : Space) : Integrable (wave k x) surface := by
  apply (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall (fun θ => (wave_norm k x θ).le))
  apply Continuous.aestronglyMeasurable
  unfold wave
  fun_prop

theorem scalar_isometry (k : ℝ) (L : Space ≃ₗᵢ[ℝ] Space) (x : Space) :
    scalar k (L x) = scalar k x := by
  have he := (SphereAngularSymmetry.measurePreserving_sphereMap L).integral_comp
    (SphereAngularSymmetry.sphereMap L).measurableEmbedding (wave k (L x))
  change (∫ θ : AngularPower.Sphere, wave k (L x) θ ∂AngularPower.angularMeasure) = scalar k x
  rw [← he]
  apply integral_congr_ae
  filter_upwards with θ
  change Complex.exp (((k * ⟪L θ.val,L x⟫_ℝ : ℝ) : ℂ)*Complex.I) = _
  rw [L.inner_map_map]
  rfl

theorem scalar_axis (k r : ℝ) : scalar k (r • Maxwell.basis 2) =
    (2*Real.pi : ℂ) * ∫ z : ℝ in Ioo (-1 : ℝ) 1,
      Complex.exp ((Complex.I*(k*r : ℝ))*z) := by
  unfold scalar wave
  rw [integral_axial (fun y => Complex.exp (((k * ⟪y,r • Maxwell.basis 2⟫_ℝ : ℝ) : ℂ)*Complex.I))
    (wave_integrable k _)]
  have hw (z t : ℝ) :
      Complex.exp (((k * ⟪AxialCoordinates.physical ![1,z,t],r • Maxwell.basis 2⟫_ℝ : ℝ) : ℂ)*Complex.I) =
        Complex.exp ((Complex.I*(k*r : ℝ))*z) := by
    congr 1
    simp [inner_smul_right, Maxwell.basis, EuclideanSpace.inner_single_right,
      AxialCoordinates.physical, AxialCoordinates.map]
    ring
  simp_rw [hw]
  have hconst (z : ℝ) :
      (∫ t : ℝ in Ioo (-Real.pi) Real.pi, Complex.exp ((Complex.I*(k*r : ℝ))*z)) =
        (2*Real.pi : ℂ)*Complex.exp ((Complex.I*(k*r : ℝ))*z) := by
    simp [integral_const, Real.volume_Ioo, Measure.real, Real.pi_pos.le]
    ring
  simp_rw [hconst]
  exact integral_const_mul _ _

theorem scalar_axis_exp (k r : ℝ) (hkr : k*r ≠ 0) : scalar k (r • Maxwell.basis 2) =
    (2*Real.pi : ℂ) *
      ((Complex.exp (Complex.I*(k*r : ℝ))-Complex.exp (-(Complex.I*(k*r : ℝ))))/(Complex.I*(k*r : ℝ))) := by
  rw [scalar_axis]
  congr 1
  have hc : Complex.I*(k*r : ℝ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hkr)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simpa only [mul_one, Complex.ofReal_neg, Complex.ofReal_one, mul_neg_one] using integral_exp_mul_complex
    (a := (-1 : ℝ)) (b := (1 : ℝ)) hc

theorem scalar_radial (k : ℝ) (x : Space) : scalar k x = scalar k (‖x‖ • Maxwell.basis 2) := by
  let L : Space ≃ₗᵢ[ℝ] Space := (ℝ ∙ (x-‖x‖ • Maxwell.basis 2))ᗮ.reflection
  have hn : ‖x‖ = ‖‖x‖ • Maxwell.basis 2‖ := by
    simp [Maxwell.basis, norm_smul, EuclideanSpace.norm_single]
  have hx : L x = ‖x‖ • Maxwell.basis 2 := Submodule.reflection_sub hn
  rw [← hx]
  exact (scalar_isometry k L x).symm

theorem scalar_radial_exp (k : ℝ) (x : Space) (hk : k ≠ 0) (hx : x ≠ 0) : scalar k x =
    (2*Real.pi : ℂ) * ((Complex.exp (Complex.I*(k*‖x‖ : ℝ))-
      Complex.exp (-(Complex.I*(k*‖x‖ : ℝ))))/(Complex.I*(k*‖x‖ : ℝ))) := by
  rw [scalar_radial]
  exact scalar_axis_exp k ‖x‖ (mul_ne_zero hk (norm_ne_zero_iff.mpr hx))

theorem scalar_phi (k : ℝ) (x : Space) (hk : k ≠ 0) (hx : x ≠ 0) : scalar k x =
    ((8*Real.pi^2 : ℝ) : ℂ)/(Complex.I*(k : ℂ)) * (GreenKernel.phi k x-GreenKernel.phi (-k) x) := by
  rw [scalar_radial_exp k x hk hx]
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hr : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx)
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold GreenKernel.phi GreenKernel.radial
  push_cast
  have he : Complex.I * -(k : ℂ) * (‖x‖ : ℂ) = -(Complex.I*((k : ℂ)*(‖x‖ : ℂ))) := by ring
  rw [he]
  field_simp
  ring_nf
end OQ14.SphereWaveTransform
#print axioms OQ14.SphereWaveTransform.integral_axial
#print axioms OQ14.SphereWaveTransform.wave_integrable
#print axioms OQ14.SphereWaveTransform.scalar_isometry
#print axioms OQ14.SphereWaveTransform.scalar_axis
#print axioms OQ14.SphereWaveTransform.scalar_axis_exp
#print axioms OQ14.SphereWaveTransform.scalar_radial
#print axioms OQ14.SphereWaveTransform.scalar_radial_exp



#print axioms OQ14.SphereWaveTransform.scalar_phi
