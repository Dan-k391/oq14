import Packet02Majorant
import SphereAxialMeasure
noncomputable section
namespace OQ14.Packet02SurfaceGeometry
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.AxialCoordinates
open OQ14.Packet02Majorant OQ14.SphereAxialMeasure

theorem norm_axis_sq (r s z θ : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    ‖r • physical ![1,z,θ] - s • basis 2‖^2 = r^2 + s^2 - 2*r*s*z := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_three, physical, AxialCoordinates.map, basis,
    EuclideanSpace.single_apply, PiLp.sub_apply, PiLp.smul_apply,
    Real.norm_eq_abs, sq_abs]
  have ht := transverse_sq z ⟨hz.1.le,hz.2.le⟩
  have hc := Real.cos_sq_add_sin_sq θ
  nlinarith [sq_nonneg (r * transverse z), mul_nonneg (sq_nonneg r) (sq_nonneg (transverse z))]

theorem angular_axis_integral (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s) :
    angular r (s • basis 2) =
      ∫ z in Ioo (-1 : ℝ) 1, (2 * Real.pi) * (r^2 + s^2 - 2*r*s*z)⁻¹ := by
  have hb : ‖basis 2‖ = 1 := by simp [basis, EuclideanSpace.norm_single]
  have hn : ‖s • basis 2‖ ≠ |r| := by
    simp only [norm_smul, Real.norm_eq_abs, hb, mul_one, abs_of_pos hr, abs_of_pos hs]
    exact hne.symm
  have hi := slice_integrable_of_norm_ne r (s • basis 2) hn
  have hi' : Integrable (fun n : Sphere => (‖r • (n : Space) - s • basis 2‖⁻¹)^2) angularMeasure := hi
  change (∫ ω : Sphere, (‖r • (ω : Space) - s • basis 2‖⁻¹)^2 ∂angularMeasure) = _
  rw [integral_axial_iterated (fun x => (‖r • x - s • basis 2‖⁻¹)^2) hi']
  apply setIntegral_congr_fun measurableSet_Ioo
  intro z hz
  have he : ∀ θ ∈ Ioo (-Real.pi) Real.pi,
      (‖r • physical ![1,z,θ] - s • basis 2‖⁻¹)^2 = (r^2+s^2-2*r*s*z)⁻¹ := by
    intro θ hθ
    rw [inv_pow, norm_axis_sq r s z θ hz]
  dsimp only
  rw [setIntegral_congr_fun measurableSet_Ioo he]
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
    sub_neg_eq_add, smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi + Real.pi)]
  ring
theorem angular_axis_formula (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s) :
    angular r (s • basis 2) =
      (2 * Real.pi / (r*s)) * Real.log ((r+s) / |r-s|) := by
  rw [angular_axis_integral r s hr hs hne]
  have hp : 0 < (r-s)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hq : 0 < (r+s)^2 := sq_pos_of_pos (add_pos hr hs)
  have hc : 2*r*s ≠ 0 := by positivity
  have hsub := intervalIntegral.integral_comp_sub_mul (fun x : ℝ => x⁻¹) hc (r^2+s^2)
    (a := (-1 : ℝ)) (b := 1)
  have hlo : r^2+s^2-(2*r*s)*1 = (r-s)^2 := by ring
  have hhi : r^2+s^2-(2*r*s)*(-1) = (r+s)^2 := by ring
  rw [hlo,hhi, integral_inv_of_pos hp hq] at hsub
  have hlog : Real.log ((r+s)^2 / (r-s)^2) = 2 * Real.log ((r+s)/|r-s|) := by
    rw [← sq_abs (r-s), ← div_pow, Real.log_pow]
    push_cast
    ring
  rw [hlog] at hsub
  have hint : (∫ z in Ioo (-1 : ℝ) 1, (r^2+s^2-2*r*s*z)⁻¹) =
      (2*r*s)⁻¹ * (2 * Real.log ((r+s)/|r-s|)) := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hsub
  rw [integral_const_mul, hint]
  field_simp
  ring
theorem angular_formula (r : ℝ) (y : Space) (hr : 0 < r)
    (hy : y ≠ 0) (hne : ‖y‖ ≠ r) :
    angular r y = (2 * Real.pi / (r * ‖y‖)) * Real.log ((r + ‖y‖) / |r - ‖y‖|) := by
  have hs : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hb : ‖basis 2‖ = 1 := by simp [basis, EuclideanSpace.norm_single]
  have hn : ‖y‖ = ‖‖y‖ • basis 2‖ := by
    simp [norm_smul, hb]
  rw [angular_radial r y (‖y‖ • basis 2) hn]
  exact angular_axis_formula r ‖y‖ hr hs hne.symm

theorem angular_formula_ae (r : ℝ) (hr : 0 < r) :
    (angular r) =ᵐ[volume] (fun y : Space =>
      (2 * Real.pi / (r * ‖y‖)) * Real.log ((r + ‖y‖) / |r - ‖y‖|)) := by
  have hne : ∀ᵐ y ∂(volume : Measure Space), ‖y‖ ≠ r := by
    rw [ae_iff]
    have hs : {y : Space | ¬ ‖y‖ ≠ r} = sphere 0 r := by
      ext y
      simp only [Set.mem_setOf_eq, not_not, mem_sphere, dist_zero_right]
    rw [hs]
    exact Measure.addHaar_sphere (volume : Measure Space) 0 r
  have hzero : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_eq_eq_singleton] using (measure_singleton (0 : Space))
  filter_upwards [hzero, hne] with y hy hny
  exact angular_formula r y hr hy hny
end OQ14.Packet02SurfaceGeometry
#print axioms OQ14.Packet02SurfaceGeometry.norm_axis_sq

#print axioms OQ14.Packet02SurfaceGeometry.angular_axis_integral

#print axioms OQ14.Packet02SurfaceGeometry.angular_axis_formula

#print axioms OQ14.Packet02SurfaceGeometry.angular_formula_ae

#print axioms OQ14.Packet02SurfaceGeometry.angular_formula
