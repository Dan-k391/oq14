import SphereAxialMeasure
import ConicalAngularTrial
import CapSturmEndpointTest
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-! Actual ambient test derivatives along latitudes, including their integrable pole bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace OQ14.SphereAxialTests
open MeasureTheory Metric Set Real OQ14.Maxwell OQ14.AngularPower
  OQ14.AxialCoordinates OQ14.SphereAxialMeasure
open scoped Topology InnerProductSpace

def latitude (z θ : ℝ) : Space := physical ![1,z,θ]
def latitudeD (z θ : ℝ) : Space := (WithLp.equiv 2 Coordinates).symm
  ![-z/transverse z*cos θ, -z/transverse z*sin θ, 1]

theorem latitude_continuous : Continuous (fun q : ℝ × ℝ => latitude q.1 q.2) := by
  apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [latitude,physical,AxialCoordinates.map] using
      (show Continuous (fun q : ℝ × ℝ => transverse q.1*cos q.2) by fun_prop)
  · simpa [latitude,physical,AxialCoordinates.map] using
      (show Continuous (fun q : ℝ × ℝ => transverse q.1*sin q.2) by fun_prop)
  · simpa [latitude,physical,AxialCoordinates.map] using
      (show Continuous (fun q : ℝ × ℝ => q.1) from continuous_fst)

theorem transverse_hasDerivAt (z : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt transverse (-z/transverse z) z := by
  have h := (((hasDerivAt_id z).pow 2).const_sub 1).sqrt
    (by have h := transverse_pos z hz; exact (Real.sqrt_pos.mp h).ne')
  convert h using 1
  dsimp only [transverse,id_eq]
  norm_num
  ring

theorem latitude_hasDerivAt (z θ : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y => latitude y θ) (latitudeD z θ) z := by
  have h : HasDerivAt (fun y : ℝ => ![transverse y*cos θ,transverse y*sin θ,y])
      ![-z/transverse z*cos θ,-z/transverse z*sin θ,1] z := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using (transverse_hasDerivAt z hz).mul_const (cos θ)
    · simpa using (transverse_hasDerivAt z hz).mul_const (sin θ)
    · simpa using hasDerivAt_id z
  simpa [Function.comp_def,latitude,physical,AxialCoordinates.map,latitudeD]
    using ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt z h)

theorem latitude_norm (z θ : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) : ‖latitude z θ‖ = 1 := by
  have hn : ‖latitude z θ‖^2 = 1^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [latitude,physical,AxialCoordinates.map,Fin.sum_univ_three,Real.norm_eq_abs,sq_abs]
    change (1*transverse z*cos θ)^2+(1*transverse z*sin θ)^2+(1*z)^2=1^2
    linear_combination (transverse z)^2*(Real.cos_sq_add_sin_sq θ)+transverse_sq z hz
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hn

theorem latitudeD_norm (z θ : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    ‖latitudeD z θ‖ = 1/transverse z := by
  have hp := transverse_pos z hz
  have hs := transverse_sq z ⟨hz.1.le,hz.2.le⟩
  have hn : ‖latitudeD z θ‖^2 = (1/transverse z)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [latitudeD,Fin.sum_univ_three,Real.norm_eq_abs,sq_abs]
    change (-z/transverse z*cos θ)^2+(-z/transverse z*sin θ)^2+1^2=(1/transverse z)^2
    field_simp [hp.ne']
    nlinarith [Real.cos_sq_add_sin_sq θ]
  exact (sq_eq_sq₀ (norm_nonneg _) (div_nonneg zero_le_one hp.le)).mp hn

theorem latitudeD_tangent (z θ : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    (1-z^2) • latitudeD z θ = basis 2-z • latitude z θ := by
  have hp := transverse_pos z hz
  have hs := transverse_sq z ⟨hz.1.le,hz.2.le⟩
  rw [← hs]
  ext i
  fin_cases i <;> simp [latitudeD,latitude,physical,AxialCoordinates.map,basis]
  · field_simp [hp.ne']
    ring
  · field_simp [hp.ne']
    ring
  · nlinarith

theorem inverse_transverse_intervalIntegrable :
    IntervalIntegrable (fun z => 1/transverse z) volume (-1) 1 := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    Real.continuous_arcsin.continuousOn
  · intro z hz
    have hz' : z ∈ Ioo (-1 : ℝ) 1 := by simpa using hz
    exact Real.hasDerivAt_arcsin (ne_of_gt hz'.1) (ne_of_lt hz'.2)
  · intro z _
    exact div_nonneg zero_le_one (Real.sqrt_nonneg _)

def testSlope (ψ : Space → ℝ) (z θ : ℝ) : ℝ :=
  fderiv ℝ ψ (latitude z θ) (latitudeD z θ)

theorem test_hasDerivAt (ψ : Space → ℝ) (hψ : Differentiable ℝ ψ)
    (z θ : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y => ψ (latitude y θ)) (testSlope ψ z θ) z := by
  exact (hψ (latitude z θ)).hasFDerivAt.comp_hasDerivAt z (latitude_hasDerivAt z θ hz)

theorem test_tangent_identity (ψ : Space → ℝ) (z θ : ℝ)
    (hz : z ∈ Ioo (-1 : ℝ) 1) :
    (1-z^2)*testSlope ψ z θ =
      fderiv ℝ ψ (latitude z θ) (basis 2-z • latitude z θ) := by
  rw [← latitudeD_tangent z θ hz]
  simp only [testSlope,map_smul,smul_eq_mul]

theorem latitudeD_continuousOn (θ : ℝ) :
    ContinuousOn (fun z => latitudeD z θ) (Ioo (-1 : ℝ) 1) := by
  apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · exact (continuousOn_id.neg.div transverse_continuous.continuousOn
      (fun z hz => (transverse_pos z hz).ne')).mul continuousOn_const
  · exact (continuousOn_id.neg.div transverse_continuous.continuousOn
      (fun z hz => (transverse_pos z hz).ne')).mul continuousOn_const
  · exact continuousOn_const

theorem test_continuous (ψ : Space → ℝ) (hψ : Continuous ψ) (θ : ℝ) :
    Continuous (fun z => ψ (latitude z θ)) := by
  have h : Continuous (fun z : ℝ => latitude z θ) :=
    latitude_continuous.comp (f := fun z : ℝ => (z,θ))
      (continuous_id.prodMk continuous_const)
  exact hψ.comp h

theorem testSlope_continuousOn (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (θ : ℝ) :
    ContinuousOn (fun z => testSlope ψ z θ) (Ioo (-1 : ℝ) 1) := by
  exact ((hψ.continuous_fderiv le_rfl).comp
    (f := fun z : ℝ => latitude z θ)
    (latitude_continuous.comp (f := fun z : ℝ => (z,θ))
      (continuous_id.prodMk continuous_const))).continuousOn.clm_apply
      (latitudeD_continuousOn θ)

theorem testSlope_bound (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    ∃ C : ℝ, ∀ z ∈ Ioo (-1 : ℝ) 1, ∀ θ : ℝ,
      ‖testSlope ψ z θ‖ ≤ C*(1/transverse z) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Space) 1).exists_bound_of_continuousOn
    (hψ.continuous_fderiv le_rfl).continuousOn
  refine ⟨C,fun z hz θ => ?_⟩
  calc
    ‖testSlope ψ z θ‖ ≤ ‖fderiv ℝ ψ (latitude z θ)‖*‖latitudeD z θ‖ :=
      (fderiv ℝ ψ (latitude z θ)).le_opNorm _
    _ ≤ C*(1/transverse z) := by
      rw [latitudeD_norm z θ hz]
      apply mul_le_mul_of_nonneg_right (hC _ _)
        (div_nonneg zero_le_one (transverse_pos z hz).le)
      rw [mem_closedBall,dist_zero_right,latitude_norm z θ ⟨hz.1.le,hz.2.le⟩]

theorem testSlope_intervalIntegrable (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (θ : ℝ) :
    IntervalIntegrable (fun z => testSlope ψ z θ) volume (-1) 1 := by
  obtain ⟨C,hC⟩ := testSlope_bound ψ hψ
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (show (-1 : ℝ) ≤ 1 by norm_num)).mp (inverse_transverse_intervalIntegrable.const_mul C)
  apply hi.mono' ((testSlope_continuousOn ψ hψ θ).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact hC z hz θ

theorem cap_latitude_weak (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hr : CapAngularShooting.determinant d t a = 0)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (θ : ℝ) :
    (∫ z in (-1 : ℝ)..1, CapSturmLiouville.coefficient d t z*
      ((1-z^2)*CapSturmLiouville.slope a t z*testSlope ψ z θ)) =
    a*∫ z in (-1 : ℝ)..1, CapSturmLiouville.coefficient d t z*
      (CapSturmLiouville.profile a t z*ψ (latitude z θ)) := by
  exact CapSturmEndpointTest.weighted_weak_identity a d t ha ht ht1 hr
    (fun z => ψ (latitude z θ)) (fun z => testSlope ψ z θ)
    (fun z hz => test_hasDerivAt ψ (hψ.differentiable le_rfl) z θ hz)
    (test_continuous ψ hψ.continuous θ).continuousOn
    (testSlope_intervalIntegrable ψ hψ θ)

end OQ14.SphereAxialTests

#print axioms OQ14.SphereAxialTests.latitude_continuous
#print axioms OQ14.SphereAxialTests.transverse_hasDerivAt
#print axioms OQ14.SphereAxialTests.latitude_hasDerivAt
#print axioms OQ14.SphereAxialTests.latitude_norm
#print axioms OQ14.SphereAxialTests.latitudeD_norm
#print axioms OQ14.SphereAxialTests.latitudeD_tangent
#print axioms OQ14.SphereAxialTests.inverse_transverse_intervalIntegrable
#print axioms OQ14.SphereAxialTests.test_hasDerivAt
#print axioms OQ14.SphereAxialTests.test_tangent_identity
#print axioms OQ14.SphereAxialTests.latitudeD_continuousOn
#print axioms OQ14.SphereAxialTests.test_continuous
#print axioms OQ14.SphereAxialTests.testSlope_continuousOn
#print axioms OQ14.SphereAxialTests.testSlope_bound
#print axioms OQ14.SphereAxialTests.testSlope_intervalIntegrable
#print axioms OQ14.SphereAxialTests.cap_latitude_weak
