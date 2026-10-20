import SphereAxialTests
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Lifting the actual matched cap profile to the actual geometric sphere weak equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace OQ14.SphereCapWeak
open MeasureTheory Metric Set Real OQ14.Maxwell OQ14.AngularPower
  OQ14.AxialCoordinates OQ14.SphereAxialMeasure OQ14.SphereAxialTests
  OQ14.CapLegendreSeries OQ14.CapAngularShooting OQ14.CapSturmLiouville
open scoped Topology ENNReal

@[simp] theorem latitude_axial (z θ : ℝ) : (latitude z θ) 2 = z := by
  simp [latitude,physical,AxialCoordinates.map]

theorem coordinate_range (n : Sphere) : (n : Space) 2 ∈ Icc (-1 : ℝ) 1 := by
  have h := PiLp.norm_apply_le (n : Space) 2
  rw [sphere_norm] at h
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using h)

theorem coordinate_ne_ae (s : ℝ) : ∀ᵐ n : Sphere ∂angularMeasure, (n : Space) 2 ≠ s := by
  rw [ae_iff]
  simpa only [not_not] using latitude_null s

theorem coordinate_interior_ae :
    ∀ᵐ n : Sphere ∂angularMeasure, (n : Space) 2 ∈ Ioo (-1 : ℝ) 1 := by
  filter_upwards [coordinate_ne_ae (-1),coordinate_ne_ae 1] with n hL hR
  have h := coordinate_range n
  exact ⟨lt_of_le_of_ne h.1 hL.symm,lt_of_le_of_ne h.2 hR⟩

theorem profile_continuous (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) :
    Continuous (fun n : Sphere => profile a t ((n : Space) 2)) := by
  exact (profile_continuousOn a t ha ht ht1).comp_continuous
    (f := fun n : Sphere => (n : Space) 2)
    (OQ14.ConicalAngularTrial.coordinate_continuous 2) coordinate_range

theorem slope_bound (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) :
    ∃ C ≥ (0 : ℝ), ∀ z ∈ Icc (-1 : ℝ) 1, ‖CapSturmLiouville.slope a t z‖ ≤ C := by
  have cL : ContinuousOn (negativeD a t) (Icc (-1 : ℝ) (-t)) :=
    fun z hz => (negativeD_hasDerivAt a t z ha (left_argument t z ht ht1 hz)).continuousAt.continuousWithinAt
  have cM : ContinuousOn (interiorD a t) (Icc (-t) t) :=
    fun z hz => (interiorD_hasDerivAt a t z ha (middle_argument t z ht1 hz)).continuousAt.continuousWithinAt
  have cR : ContinuousOn (exteriorD a t) (Icc t 1) :=
    fun z hz => (exteriorD_hasDerivAt a t z ha (right_argument t z ht ht1 hz)).continuousAt.continuousWithinAt
  obtain ⟨CL,hCL⟩ := isCompact_Icc.exists_bound_of_continuousOn cL
  obtain ⟨CM,hCM⟩ := isCompact_Icc.exists_bound_of_continuousOn cM
  obtain ⟨CR,hCR⟩ := isCompact_Icc.exists_bound_of_continuousOn cR
  refine ⟨|CL|+|CM|+|CR|,by positivity,fun z hz => ?_⟩
  by_cases hL : z < -t
  · rw [CapSturmLiouville.slope,if_pos hL]
    exact (hCL z ⟨hz.1,hL.le⟩).trans (by linarith [le_abs_self CL,abs_nonneg CM,abs_nonneg CR])
  · by_cases hM : z ≤ t
    · rw [CapSturmLiouville.slope,if_neg hL,if_pos hM]
      exact (hCM z ⟨le_of_not_gt hL,hM⟩).trans (by linarith [le_abs_self CM,abs_nonneg CL,abs_nonneg CR])
    · rw [CapSturmLiouville.slope,if_neg hL,if_neg hM]
      exact (hCR z ⟨le_of_not_ge hM,hz.2⟩).trans (by linarith [le_abs_self CR,abs_nonneg CL,abs_nonneg CM])

theorem slope_aestronglyMeasurable (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) :
    AEStronglyMeasurable (fun n : Sphere => CapSturmLiouville.slope a t ((n : Space) 2)) angularMeasure := by
  have hm : Measurable (fun n : Sphere => deriv (profile a t) ((n : Space) 2)) :=
    (measurable_deriv (profile a t)).comp
      (OQ14.ConicalAngularTrial.coordinate_continuous 2).measurable
  apply hm.aestronglyMeasurable.congr
  filter_upwards [coordinate_interior_ae,coordinate_ne_ae (-t),coordinate_ne_ae t] with n hz hL hR
  exact (profile_hasDerivAt a t ((n : Space) 2) ha ht ht1 hz hL hR).deriv

theorem slope_memLp (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (p : ℝ≥0∞) :
    MemLp (fun n : Sphere => CapSturmLiouville.slope a t ((n : Space) 2)) p angularMeasure := by
  obtain ⟨C,_,hC⟩ := slope_bound a t ha ht ht1
  exact MemLp.of_bound (slope_aestronglyMeasurable a t ha ht ht1) C
    (Filter.Eventually.of_forall (fun n => hC _ (coordinate_range n)))

theorem coefficient_integrable (f : Sphere → ℝ) (hf : Integrable f angularMeasure) (d t : ℝ) :
    Integrable (fun n : Sphere => coefficient d t ((n : Space) 2)*f n) angularMeasure := by
  let S : Set Sphere := {n | t < |(n : Space) 2|}
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const (OQ14.ConicalAngularTrial.coordinate_continuous 2).abs).measurableSet
  have he : (fun n : Sphere => coefficient d t ((n : Space) 2)*f n) =
      f+d • S.indicator f := by
    funext n
    by_cases hn : n ∈ S
    · simp only [S,mem_setOf_eq] at hn
      simp [coefficient,not_le.mpr hn,S,hn]
      ring
    · have hn' : |(n : Space) 2| ≤ t := le_of_not_gt hn
      simp [coefficient,hn',S,not_lt.mpr hn']
  rw [he]
  exact hf.add ((hf.indicator hS).smul d)

theorem slope_mul_integrable (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (f : Sphere → ℝ) (hf : Continuous f) :
    Integrable (fun n : Sphere => CapSturmLiouville.slope a t ((n : Space) 2)*f n) angularMeasure := by
  have hi := memLp_one_iff_integrable.mp (slope_memLp a t ha ht ht1 1)
  have h : IntegrableOn (fun n : Sphere => CapSturmLiouville.slope a t ((n : Space) 2)) univ angularMeasure := by
    simpa using hi
  simpa using h.mul_continuousOn hf.continuousOn isCompact_univ

theorem integral_axial_swapped (f : Space → ℝ)
    (hf : Integrable (fun n : Sphere => f n) angularMeasure) :
    (∫ n : Sphere, f n ∂angularMeasure) =
      ∫ θ in Ioo (-Real.pi) Real.pi, ∫ z in Ioo (-1 : ℝ) 1, f (latitude z θ) := by
  rw [integral_axial_iterated f hf]
  apply integral_integral_swap
  have h := integrable_axial f hf
  change Integrable (fun q : ℝ × ℝ => f (latitude q.1 q.2))
    (((volume : Measure ℝ).prod volume).restrict (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)) at h
  rw [← Measure.prod_restrict] at h
  exact h

theorem sphere_weak_identity (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hr : determinant d t a = 0)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    (∫ n : Sphere, coefficient d t ((n : Space) 2)*
      (CapSturmLiouville.slope a t ((n : Space) 2)*
        fderiv ℝ ψ n (basis 2-(n : Space) 2 • (n : Space))) ∂angularMeasure) =
    a*∫ n : Sphere, coefficient d t ((n : Space) 2)*
      (profile a t ((n : Space) 2)*ψ n) ∂angularMeasure := by
  have cx : Continuous (fun n : Sphere => (n : Space) 2) :=
    OQ14.ConicalAngularTrial.coordinate_continuous 2
  have cf : Continuous (fun n : Sphere => fderiv ℝ ψ n (basis 2-(n : Space) 2 • (n : Space))) :=
    ((hψ.continuous_fderiv le_rfl).comp continuous_subtype_val).clm_apply
      (continuous_const.sub (cx.smul continuous_subtype_val))
  have hiL := coefficient_integrable _ (slope_mul_integrable a t ha ht ht1 _ cf) d t
  have hiR := coefficient_integrable _ (OQ14.ConicalAngularTrial.continuous_integrable _
    ((profile_continuous a t ha ht ht1).mul (hψ.continuous.comp continuous_subtype_val))) d t
  rw [integral_axial_swapped (fun x : Space => coefficient d t (x 2)*
    (CapSturmLiouville.slope a t (x 2)*fderiv ℝ ψ x (basis 2-x 2 • x))) hiL,
    integral_axial_swapped (fun x : Space => coefficient d t (x 2)*(profile a t (x 2)*ψ x)) hiR,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with θ
  have hl : (∫ z in Ioo (-1 : ℝ) 1,
      coefficient d t ((latitude z θ) 2)*(CapSturmLiouville.slope a t ((latitude z θ) 2)*
        fderiv ℝ ψ (latitude z θ) (basis 2-(latitude z θ) 2 • latitude z θ))) =
      ∫ z in (-1 : ℝ)..1, coefficient d t z*((1-z^2)*CapSturmLiouville.slope a t z*testSlope ψ z θ) := by
    rw [intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro z hz
    simp only [latitude_axial]
    change coefficient d t z*(CapSturmLiouville.slope a t z*
      fderiv ℝ ψ (latitude z θ) (basis 2-z • latitude z θ)) = _
    rw [← test_tangent_identity ψ z θ hz]
    ring
  rw [hl,cap_latitude_weak a d t ha ht ht1 hr ψ hψ θ]
  congr 1
  rw [intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),integral_Ioc_eq_integral_Ioo]
  simp only [latitude_axial]

end OQ14.SphereCapWeak

#print axioms OQ14.SphereCapWeak.latitude_axial
#print axioms OQ14.SphereCapWeak.coordinate_range
#print axioms OQ14.SphereCapWeak.coordinate_ne_ae
#print axioms OQ14.SphereCapWeak.coordinate_interior_ae
#print axioms OQ14.SphereCapWeak.profile_continuous
#print axioms OQ14.SphereCapWeak.slope_bound
#print axioms OQ14.SphereCapWeak.slope_aestronglyMeasurable
#print axioms OQ14.SphereCapWeak.slope_memLp
#print axioms OQ14.SphereCapWeak.coefficient_integrable
#print axioms OQ14.SphereCapWeak.slope_mul_integrable
#print axioms OQ14.SphereCapWeak.integral_axial_swapped
#print axioms OQ14.SphereCapWeak.sphere_weak_identity
