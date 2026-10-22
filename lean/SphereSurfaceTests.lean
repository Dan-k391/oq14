import SphereAxialSurface
import CapProfileFirstOrder

/-! Actual ambient tests for first-order surface integration by parts. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.SphereSurfaceTests
open MeasureTheory Metric Set Real OQ14.Maxwell OQ14.AngularPower
  OQ14.AxialCoordinates OQ14.SphereAxialTests OQ14.SphereAxialSurface
open scoped Topology

def thetaSlope (ψ : Space → ℝ) (z θ : ℝ) : ℝ := fderiv ℝ ψ (latitude z θ) (azimuthD z θ)
def axialFlux (i : Fin 3) (ψ : Space → ℝ) (z θ : ℝ) : ℝ :=
  (axialTangent z θ) i*ψ (latitude z θ)
def axialFluxD (i : Fin 3) (ψ : Space → ℝ) (z θ : ℝ) : ℝ :=
  (axialTangentD z θ) i*ψ (latitude z θ)+(axialTangent z θ) i*testSlope ψ z θ
def thetaFlux (i : Fin 3) (ψ : Space → ℝ) (z θ : ℝ) : ℝ :=
  (azimuthCoefficient z θ) i*ψ (latitude z θ)
def thetaFluxD (i : Fin 3) (ψ : Space → ℝ) (z θ : ℝ) : ℝ :=
  (azimuthCoefficientD z θ) i*ψ (latitude z θ)+(azimuthCoefficient z θ) i*thetaSlope ψ z θ

theorem theta_test_hasDerivAt (ψ : Space → ℝ) (hψ : Differentiable ℝ ψ) (z θ : ℝ) :
    HasDerivAt (fun s => ψ (latitude z s)) (thetaSlope ψ z θ) θ :=
  (hψ _).hasFDerivAt.comp_hasDerivAt θ (latitude_hasDerivAt_azimuth z θ)

theorem axialFlux_hasDerivAt (i : Fin 3) (ψ : Space → ℝ) (hψ : Differentiable ℝ ψ)
    (z θ : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y => axialFlux i ψ y θ) (axialFluxD i ψ z θ) z := by
  exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt z
    (axialTangent_hasDerivAt z θ hz)).mul (test_hasDerivAt ψ hψ z θ hz)

theorem thetaFlux_hasDerivAt (i : Fin 3) (ψ : Space → ℝ) (hψ : Differentiable ℝ ψ) (z θ : ℝ) :
    HasDerivAt (fun s => thetaFlux i ψ z s) (thetaFluxD i ψ z θ) θ := by
  exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp_hasDerivAt θ
    (azimuthCoefficient_hasDerivAt z θ)).mul (theta_test_hasDerivAt ψ hψ z θ)

theorem surface_test_decomposition (i : Fin 3) (ψ : Space → ℝ)
    (z θ : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    fderiv ℝ ψ (latitude z θ) (basis i-(latitude z θ) i • latitude z θ)-
      2*(latitude z θ) i*ψ (latitude z θ) = axialFluxD i ψ z θ+thetaFluxD i ψ z θ := by
  have hc := congrArg (fun x : Space => x i) (coordinate_curvature z θ hz)
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hc
  rw [tangent_decomposition i z θ hz,map_add,map_smul,map_smul]
  simp only [smul_eq_mul,axialFluxD,thetaFluxD,testSlope,thetaSlope]
  linear_combination -ψ (latitude z θ)*hc

theorem axialFlux_at_poles (i : Fin 3) (ψ : Space → ℝ) (θ : ℝ) :
    axialFlux i ψ (-1) θ = 0 ∧ axialFlux i ψ 1 θ = 0 := by
  simp [axialFlux,(axialTangent_at_poles θ).1,(axialTangent_at_poles θ).2]

theorem thetaFlux_endpoint_matching (i : Fin 3) (ψ : Space → ℝ) (z : ℝ) :
    thetaFlux i ψ z (-Real.pi) = thetaFlux i ψ z Real.pi := by
  simp only [thetaFlux,(azimuth_endpoint_matching z).1,(azimuth_endpoint_matching z).2]

theorem azimuth_vectors_continuous (z : ℝ) :
    Continuous (azimuthD z) ∧ Continuous (azimuthCoefficient z) ∧ Continuous (azimuthCoefficientD z) := by
  constructor
  · apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp [azimuthD] <;> fun_prop
  · constructor
    · apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> simp [azimuthCoefficient] <;> fun_prop
    · apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> simp [azimuthCoefficientD] <;> fun_prop

theorem latitude_azimuth_continuous (z : ℝ) : Continuous (latitude z) :=
  SphereAxialTests.latitude_continuous.comp (f := fun θ : ℝ => (z,θ))
    (continuous_const.prodMk continuous_id)

theorem thetaFluxD_continuous (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (z : ℝ) :
    Continuous (thetaFluxD i ψ z) := by
  have hlat := latitude_azimuth_continuous z
  have hvec := azimuth_vectors_continuous z
  have hψlat : Continuous (fun θ => ψ (latitude z θ)) := hψ.continuous.comp hlat
  have hfd : Continuous (fun θ => fderiv ℝ ψ (latitude z θ) (azimuthD z θ)) :=
    ((hψ.continuous_fderiv le_rfl).comp (f := latitude z) hlat).clm_apply hvec.1
  exact (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp hvec.2.2).mul hψlat).add
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp hvec.2.1).mul hfd)

theorem thetaFluxD_integral_zero (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (z : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, thetaFluxD i ψ z θ) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => thetaFlux_hasDerivAt i ψ (hψ.differentiable le_rfl) z θ)
    ((thetaFluxD_continuous i ψ hψ z).intervalIntegrable _ _),thetaFlux_endpoint_matching]
  exact sub_self _

theorem transverse_le_one (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) : transverse z ≤ 1 := by
  have h := transverse_sq z hz
  have hp : 0 ≤ transverse z := Real.sqrt_nonneg _
  nlinarith [sq_nonneg z]

theorem axialTangent_norm_le (z θ : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) : ‖axialTangent z θ‖ ≤ 2 := by
  have hza : |z| ≤ 1 := abs_le.mpr hz
  calc
    ‖axialTangent z θ‖ ≤ ‖basis 2‖+‖z • latitude z θ‖ := norm_sub_le _ _
    _ = 1+|z| := by simp [basis,norm_smul,latitude_norm z θ hz]
    _ ≤ 2 := by linarith

theorem axialTangentD_norm_le (z θ : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    ‖axialTangentD z θ‖ ≤ 2*(1/transverse z) := by
  have hp := transverse_pos z hz
  have hi : 1 ≤ 1/transverse z := (le_div_iff₀ hp).mpr (by simpa using transverse_le_one z ⟨hz.1.le,hz.2.le⟩)
  have hm := mul_le_mul_of_nonneg_right (abs_le.mpr ⟨hz.1.le,hz.2.le⟩)
    (div_nonneg zero_le_one hp.le)
  calc
    ‖axialTangentD z θ‖ ≤ ‖-latitude z θ‖+‖z • latitudeD z θ‖ := norm_sub_le _ _
    _ = 1+|z| * (1/transverse z) := by rw [norm_neg,latitude_norm z θ ⟨hz.1.le,hz.2.le⟩,norm_smul,Real.norm_eq_abs,latitudeD_norm z θ hz]
    _ ≤ 2*(1/transverse z) := by linarith

theorem ambient_test_bound (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    ∃ C ≥ (0 : ℝ), ∀ z ∈ Icc (-1 : ℝ) 1, ∀ θ : ℝ,
      ‖ψ (latitude z θ)‖ ≤ C ∧ ‖fderiv ℝ ψ (latitude z θ)‖ ≤ C := by
  obtain ⟨CV,hCV⟩ := (isCompact_closedBall (0 : Space) 1).exists_bound_of_continuousOn hψ.continuous.continuousOn
  obtain ⟨CD,hCD⟩ := (isCompact_closedBall (0 : Space) 1).exists_bound_of_continuousOn
    (hψ.continuous_fderiv le_rfl).continuousOn
  refine ⟨|CV|+|CD|,by positivity,fun z hz θ => ?_⟩
  have hn : latitude z θ ∈ closedBall (0 : Space) 1 := by
    rw [mem_closedBall,dist_zero_right,latitude_norm z θ hz]
  exact ⟨(hCV _ hn).trans (by linarith [le_abs_self CV,abs_nonneg CD]),
    (hCD _ hn).trans (by linarith [le_abs_self CD,abs_nonneg CV])⟩

theorem axialFluxD_bound (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    ∃ C ≥ (0 : ℝ), ∀ z ∈ Ioo (-1 : ℝ) 1, ∀ θ : ℝ,
      ‖axialFluxD i ψ z θ‖ ≤ C*(1/transverse z) := by
  obtain ⟨C,hC,hb⟩ := ambient_test_bound ψ hψ
  refine ⟨4*C,by positivity,fun z hz θ => ?_⟩
  have hv := (hb z ⟨hz.1.le,hz.2.le⟩ θ).1
  have hd := (hb z ⟨hz.1.le,hz.2.le⟩ θ).2
  have hi : 0 ≤ 1/transverse z := div_nonneg zero_le_one (transverse_pos z hz).le
  have hA := (PiLp.norm_apply_le (axialTangent z θ) i).trans (axialTangent_norm_le z θ ⟨hz.1.le,hz.2.le⟩)
  have hAD := (PiLp.norm_apply_le (axialTangentD z θ) i).trans (axialTangentD_norm_le z θ hz)
  have hs : ‖testSlope ψ z θ‖ ≤ C*(1/transverse z) := by
    calc
      ‖testSlope ψ z θ‖ ≤ ‖fderiv ℝ ψ (latitude z θ)‖*‖latitudeD z θ‖ := (fderiv ℝ ψ _).le_opNorm _
      _ ≤ C*(1/transverse z) := by rw [latitudeD_norm z θ hz]; exact mul_le_mul_of_nonneg_right hd hi
  calc
    ‖axialFluxD i ψ z θ‖ ≤ ‖(axialTangentD z θ) i*ψ (latitude z θ)‖+
        ‖(axialTangent z θ) i*testSlope ψ z θ‖ := norm_add_le _ _
    _ ≤ (2*(1/transverse z))*C+2*(C*(1/transverse z)) := by
      simp only [norm_mul]
      exact add_le_add (mul_le_mul hAD hv (norm_nonneg _) (by positivity))
        (mul_le_mul hA hs (norm_nonneg _) (by norm_num))
    _ = (4*C)*(1/transverse z) := by ring

theorem axialFlux_continuous (i : Fin 3) (ψ : Space → ℝ) (hψ : Continuous ψ) (θ : ℝ) :
    Continuous (fun z => axialFlux i ψ z θ) := by
  have hl : Continuous (fun z => latitude z θ) :=
    SphereAxialTests.latitude_continuous.comp (f := fun z : ℝ => (z,θ))
      (continuous_id.prodMk continuous_const)
  have hA : Continuous (fun z : ℝ => axialTangent z θ) := continuous_const.sub (continuous_id.smul hl)
  exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp hA).mul
    (test_continuous ψ hψ θ)

theorem axialFluxD_continuousOn (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (θ : ℝ) :
    ContinuousOn (fun z => axialFluxD i ψ z θ) (Ioo (-1 : ℝ) 1) := by
  have hl : Continuous (fun z => latitude z θ) :=
    SphereAxialTests.latitude_continuous.comp (f := fun z : ℝ => (z,θ))
      (continuous_id.prodMk continuous_const)
  have hA : Continuous (fun z : ℝ => axialTangent z θ) := continuous_const.sub (continuous_id.smul hl)
  have hAD : ContinuousOn (fun z : ℝ => axialTangentD z θ) (Ioo (-1 : ℝ) 1) :=
    hl.neg.continuousOn.sub (continuousOn_id.smul (latitudeD_continuousOn θ))
  exact (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn hAD).mul
      (test_continuous ψ hψ.continuous θ).continuousOn).add
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp hA).continuousOn.mul
      (testSlope_continuousOn ψ hψ θ))

theorem axialFluxD_intervalIntegrable (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (θ : ℝ) :
    IntervalIntegrable (fun z => axialFluxD i ψ z θ) volume (-1) 1 := by
  obtain ⟨C,_,hC⟩ := axialFluxD_bound i ψ hψ
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le
    (show (-1 : ℝ) ≤ 1 by norm_num)).mp (inverse_transverse_intervalIntegrable.const_mul C)
  apply hi.mono' ((axialFluxD_continuousOn i ψ hψ θ).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact hC z hz θ

theorem profile_axialFlux_ibp (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (θ : ℝ) :
    (∫ z in (-1 : ℝ)..1, CapSturmLiouville.profile a t z*axialFluxD i ψ z θ) =
      -(∫ z in (-1 : ℝ)..1, CapSturmLiouville.slope a t z*axialFlux i ψ z θ) := by
  have h := CapProfileFirstOrder.profile_ibp a t ha ht ht1
    (fun z => axialFlux i ψ z θ) (fun z => axialFluxD i ψ z θ)
    (axialFlux_continuous i ψ hψ.continuous θ).continuousOn
    (fun z hz => axialFlux_hasDerivAt i ψ (hψ.differentiable le_rfl) z θ hz)
    (axialFluxD_intervalIntegrable i ψ hψ θ)
  simpa only [(axialFlux_at_poles i ψ θ).1,(axialFlux_at_poles i ψ θ).2,mul_zero,sub_self,zero_sub] using h

theorem surface_test_azimuth_continuous (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (z : ℝ) :
    Continuous (fun θ => fderiv ℝ ψ (latitude z θ)
      (basis i-(latitude z θ) i • latitude z θ)-2*(latitude z θ) i*ψ (latitude z θ)) := by
  have hl := latitude_azimuth_continuous z
  have hc : Continuous (fun θ => (latitude z θ) i) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp hl
  exact (((hψ.continuous_fderiv le_rfl).comp (f := latitude z) hl).clm_apply
    (continuous_const.sub (hc.smul hl))).sub
    ((continuous_const.mul hc).mul (hψ.continuous.comp (f := latitude z) hl))

theorem axialFluxD_azimuth_continuous (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (z : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) : Continuous (axialFluxD i ψ z) := by
  have h := (surface_test_azimuth_continuous i ψ hψ z).sub (thetaFluxD_continuous i ψ hψ z)
  apply h.congr
  intro θ
  have he := surface_test_decomposition i ψ z θ hz
  dsimp only [Pi.sub_apply]
  linarith

theorem surface_test_azimuth_integral (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (z : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) :
    (∫ θ in (-Real.pi)..Real.pi, fderiv ℝ ψ (latitude z θ)
      (basis i-(latitude z θ) i • latitude z θ)-2*(latitude z θ) i*ψ (latitude z θ)) =
      ∫ θ in (-Real.pi)..Real.pi, axialFluxD i ψ z θ := by
  have he : (fun θ => fderiv ℝ ψ (latitude z θ)
      (basis i-(latitude z θ) i • latitude z θ)-2*(latitude z θ) i*ψ (latitude z θ)) =
      fun θ => axialFluxD i ψ z θ+thetaFluxD i ψ z θ :=
    funext (fun θ => surface_test_decomposition i ψ z θ hz)
  rw [he,intervalIntegral.integral_add
    ((axialFluxD_azimuth_continuous i ψ hψ z hz).intervalIntegrable _ _)
    ((thetaFluxD_continuous i ψ hψ z).intervalIntegrable _ _),
    thetaFluxD_integral_zero i ψ hψ z,add_zero]

end OQ14.SphereSurfaceTests

#print axioms OQ14.SphereSurfaceTests.theta_test_hasDerivAt
#print axioms OQ14.SphereSurfaceTests.axialFlux_hasDerivAt
#print axioms OQ14.SphereSurfaceTests.thetaFlux_hasDerivAt
#print axioms OQ14.SphereSurfaceTests.surface_test_decomposition
#print axioms OQ14.SphereSurfaceTests.axialFlux_at_poles
#print axioms OQ14.SphereSurfaceTests.thetaFlux_endpoint_matching
#print axioms OQ14.SphereSurfaceTests.azimuth_vectors_continuous
#print axioms OQ14.SphereSurfaceTests.latitude_azimuth_continuous
#print axioms OQ14.SphereSurfaceTests.thetaFluxD_continuous
#print axioms OQ14.SphereSurfaceTests.thetaFluxD_integral_zero
#print axioms OQ14.SphereSurfaceTests.transverse_le_one
#print axioms OQ14.SphereSurfaceTests.axialTangent_norm_le
#print axioms OQ14.SphereSurfaceTests.axialTangentD_norm_le
#print axioms OQ14.SphereSurfaceTests.ambient_test_bound
#print axioms OQ14.SphereSurfaceTests.axialFluxD_bound
#print axioms OQ14.SphereSurfaceTests.axialFlux_continuous
#print axioms OQ14.SphereSurfaceTests.axialFluxD_continuousOn
#print axioms OQ14.SphereSurfaceTests.axialFluxD_intervalIntegrable
#print axioms OQ14.SphereSurfaceTests.profile_axialFlux_ibp
#print axioms OQ14.SphereSurfaceTests.surface_test_azimuth_continuous
#print axioms OQ14.SphereSurfaceTests.axialFluxD_azimuth_continuous
#print axioms OQ14.SphereSurfaceTests.surface_test_azimuth_integral
