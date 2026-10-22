import SphereSurfaceTests

/-! Actual integrability and product-measure closure for surface integration by parts. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.SphereSurfaceFubini
open MeasureTheory Metric Set Real OQ14.Maxwell OQ14.AngularPower
  OQ14.AxialCoordinates OQ14.SphereAxialMeasure OQ14.SphereAxialTests
  OQ14.SphereAxialSurface OQ14.SphereSurfaceTests
open scoped Topology

theorem latitudeD_joint_continuousOn :
    ContinuousOn (fun q : ℝ × ℝ => latitudeD q.1 q.2) angularDomain := by
  apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · change ContinuousOn (fun q : ℝ × ℝ => -q.1/transverse q.1*cos q.2) angularDomain
    exact (continuous_fst.neg.continuousOn.div
      (transverse_continuous.comp continuous_fst).continuousOn
      (fun q hq => (transverse_pos q.1 hq.1).ne')).mul (Real.continuous_cos.comp continuous_snd).continuousOn
  · change ContinuousOn (fun q : ℝ × ℝ => -q.1/transverse q.1*sin q.2) angularDomain
    exact (continuous_fst.neg.continuousOn.div
      (transverse_continuous.comp continuous_fst).continuousOn
      (fun q hq => (transverse_pos q.1 hq.1).ne')).mul (Real.continuous_sin.comp continuous_snd).continuousOn
  · exact continuousOn_const

theorem axialFluxD_joint_continuousOn (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    ContinuousOn (fun q : ℝ × ℝ => axialFluxD i ψ q.1 q.2) angularDomain := by
  have hl := SphereAxialTests.latitude_continuous
  have hA : Continuous (fun q : ℝ × ℝ => axialTangent q.1 q.2) := continuous_const.sub (continuous_fst.smul hl)
  have hAD : ContinuousOn (fun q : ℝ × ℝ => axialTangentD q.1 q.2) angularDomain :=
    hl.neg.continuousOn.sub (continuous_fst.continuousOn.smul latitudeD_joint_continuousOn)
  have hψlat : Continuous (fun q : ℝ × ℝ => ψ (latitude q.1 q.2)) := hψ.continuous.comp hl
  have hfd : ContinuousOn (fun q : ℝ × ℝ => testSlope ψ q.1 q.2) angularDomain :=
    ((hψ.continuous_fderiv le_rfl).comp (f := fun q : ℝ × ℝ => latitude q.1 q.2) hl).continuousOn.clm_apply
      latitudeD_joint_continuousOn
  exact (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp_continuousOn hAD).mul hψlat.continuousOn).add
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp hA).continuousOn.mul hfd)

theorem axialFluxD_integrableOn (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    IntegrableOn (fun q : ℝ × ℝ => axialFluxD i ψ q.1 q.2) angularDomain volume := by
  obtain ⟨C,_,hC⟩ := axialFluxD_bound i ψ hψ
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le (show (-1 : ℝ) ≤ 1 by norm_num)).mp
    (inverse_transverse_intervalIntegrable.const_mul C)
  have hprod := hi.mul_prod (integrable_const (1 : ℝ) (μ := volume.restrict (Ioo (-Real.pi) Real.pi)))
  have hmaj : IntegrableOn (fun q : ℝ × ℝ => C*(1/transverse q.1)) angularDomain volume := by
    change Integrable _ (((volume : Measure ℝ).prod volume).restrict (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi))
    rw [← Measure.prod_restrict]
    simpa only [mul_one] using hprod
  apply hmaj.mono' ((axialFluxD_joint_continuousOn i ψ hψ).aestronglyMeasurable angularDomain_open.measurableSet)
  filter_upwards [ae_restrict_mem angularDomain_open.measurableSet] with q hq
  exact hC q.1 hq.1 q.2

theorem profile_axialFluxD_integrableOn (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    IntegrableOn (fun q : ℝ × ℝ => CapSturmLiouville.profile a t q.1*axialFluxD i ψ q.1 q.2) angularDomain volume := by
  have hp := CapSturmLiouville.profile_continuousOn a t ha ht ht1
  have hpc : ContinuousOn (fun q : ℝ × ℝ => CapSturmLiouville.profile a t q.1) angularDomain :=
    hp.comp' continuous_fst.continuousOn (fun q hq => ⟨hq.1.1.le,hq.1.2.le⟩)
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  have hi := (axialFluxD_integrableOn i ψ hψ).norm.const_mul |M|
  apply hi.mono' ((hpc.aestronglyMeasurable angularDomain_open.measurableSet).mul
    ((axialFluxD_joint_continuousOn i ψ hψ).aestronglyMeasurable angularDomain_open.measurableSet))
  filter_upwards [ae_restrict_mem angularDomain_open.measurableSet] with q hq
  change ‖CapSturmLiouville.profile a t q.1*axialFluxD i ψ q.1 q.2‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right ((hM q.1 ⟨hq.1.1.le,hq.1.2.le⟩).trans (le_abs_self M)) (norm_nonneg _)

theorem profile_axialFluxD_swap (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    (∫ θ in Ioo (-Real.pi) Real.pi, ∫ z in Ioo (-1 : ℝ) 1,
      CapSturmLiouville.profile a t z*axialFluxD i ψ z θ) =
    ∫ z in Ioo (-1 : ℝ) 1, ∫ θ in Ioo (-Real.pi) Real.pi,
      CapSturmLiouville.profile a t z*axialFluxD i ψ z θ := by
  symm
  apply integral_integral_swap
  have h := profile_axialFluxD_integrableOn a t ha ht ht1 i ψ hψ
  change Integrable _ (((volume : Measure ℝ).prod volume).restrict (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)) at h
  rw [← Measure.prod_restrict] at h
  exact h

theorem cap_surface_ibp (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    (∫ n : Sphere, CapSturmLiouville.slope a t ((n : Space) 2)*
      (basis 2-(n : Space) 2 • (n : Space)) i*ψ n ∂angularMeasure) =
    -(∫ n : Sphere, CapSturmLiouville.profile a t ((n : Space) 2)*
      (fderiv ℝ ψ n (basis i-(n : Space) i • (n : Space))-
        2*(n : Space) i*ψ n) ∂angularMeasure) := by
  have cx (j : Fin 3) : Continuous (fun n : Sphere => (n : Space) j) :=
    OQ14.ConicalAngularTrial.coordinate_continuous j
  have ct : Continuous (fun n : Sphere => basis 2-(n : Space) 2 • (n : Space)) :=
    continuous_const.sub ((cx 2).smul continuous_subtype_val)
  have cf : Continuous (fun n : Sphere => (basis 2-(n : Space) 2 • (n : Space)) i*ψ n) :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp ct).mul
      (hψ.continuous.comp continuous_subtype_val)
  have cq : Continuous (fun n : Sphere => fderiv ℝ ψ n (basis i-(n : Space) i • (n : Space))-
      2*(n : Space) i*ψ n) :=
    (((hψ.continuous_fderiv le_rfl).comp continuous_subtype_val).clm_apply
      (continuous_const.sub ((cx i).smul continuous_subtype_val))).sub
      ((continuous_const.mul (cx i)).mul (hψ.continuous.comp continuous_subtype_val))
  have hiL : Integrable (fun n : Sphere => CapSturmLiouville.slope a t ((n : Space) 2)*
      (basis 2-(n : Space) 2 • (n : Space)) i*ψ n) angularMeasure := by
    simpa only [mul_assoc] using OQ14.SphereCapWeak.slope_mul_integrable a t ha ht ht1 _ cf
  have hiR := OQ14.ConicalAngularTrial.continuous_integrable _
    ((OQ14.SphereCapWeak.profile_continuous a t ha ht ht1).mul cq)
  rw [OQ14.SphereCapWeak.integral_axial_swapped
    (fun x : Space => CapSturmLiouville.slope a t (x 2)*(basis 2-x 2 • x) i*ψ x) hiL,
    integral_axial_iterated
    (fun x : Space => CapSturmLiouville.profile a t (x 2)*
      (fderiv ℝ ψ x (basis i-x i • x)-2*x i*ψ x)) hiR]
  have hleft : (∫ θ in Ioo (-Real.pi) Real.pi, ∫ z in Ioo (-1 : ℝ) 1,
      CapSturmLiouville.slope a t ((latitude z θ) 2)*
        (basis 2-(latitude z θ) 2 • latitude z θ) i*ψ (latitude z θ)) =
      -(∫ θ in Ioo (-Real.pi) Real.pi, ∫ z in Ioo (-1 : ℝ) 1,
        CapSturmLiouville.profile a t z*axialFluxD i ψ z θ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with θ
    have h := profile_axialFlux_ibp a t ha ht ht1 i ψ hψ θ
    simp only [intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num),integral_Ioc_eq_integral_Ioo] at h
    have he : (fun z => CapSturmLiouville.slope a t ((latitude z θ) 2)*
        (basis 2-(latitude z θ) 2 • latitude z θ) i*ψ (latitude z θ)) =
        fun z => CapSturmLiouville.slope a t z*axialFlux i ψ z θ := by
      funext z
      simp only [OQ14.SphereCapWeak.latitude_axial,axialFlux,axialTangent]
      ring
    rw [he]
    linarith
  rw [hleft,profile_axialFluxD_swap a t ha ht ht1 i ψ hψ]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro z hz
  change (∫ θ in Ioo (-Real.pi) Real.pi, CapSturmLiouville.profile a t z*axialFluxD i ψ z θ) =
    ∫ θ in Ioo (-Real.pi) Real.pi, CapSturmLiouville.profile a t ((latitude z θ) 2)*
      (fderiv ℝ ψ (latitude z θ) (basis i-(latitude z θ) i • latitude z θ)-
        2*(latitude z θ) i*ψ (latitude z θ))
  simp only [OQ14.SphereCapWeak.latitude_axial]
  rw [integral_const_mul,integral_const_mul]
  congr 1
  have h := surface_test_azimuth_integral i ψ hψ z hz
  simpa only [intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]),integral_Ioc_eq_integral_Ioo] using h.symm

end OQ14.SphereSurfaceFubini

#print axioms OQ14.SphereSurfaceFubini.latitudeD_joint_continuousOn
#print axioms OQ14.SphereSurfaceFubini.axialFluxD_joint_continuousOn
#print axioms OQ14.SphereSurfaceFubini.axialFluxD_integrableOn
#print axioms OQ14.SphereSurfaceFubini.profile_axialFluxD_integrableOn
#print axioms OQ14.SphereSurfaceFubini.profile_axialFluxD_swap
#print axioms OQ14.SphereSurfaceFubini.cap_surface_ibp
