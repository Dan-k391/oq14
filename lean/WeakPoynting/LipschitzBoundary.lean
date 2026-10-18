import WeakPoynting.Axial

/-! # Actual Maxwell plane/volume flux law with Lipschitz cutoffs in both directions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.LipschitzBoundary

open MeasureTheory OQ14.Maxwell OQ14.FluxSlices OQ14.FluxRepresentative
  OQ14.LipschitzAperture OQ14.LipschitzLine OQ14.WeakConservation Filter
open scoped Topology NNReal

theorem vertical_integrable (ψ : Aperture) (P : RealFlux)
    (hP : ∀ j, Integrable (fun x => P x j)) : Integrable (vertical ψ P) :=
  (densities_integrable ψ P hP).1

theorem lateral_integrable (ψ : Aperture) (P : RealFlux)
    (hP : ∀ j, Integrable (fun x => P x j)) : Integrable (lateral ψ P) :=
  (densities_integrable ψ P hP).2

theorem flux_integrable (ψ : Aperture) (P : RealFlux)
    (hP : ∀ j, Integrable (fun x => P x j)) : Integrable (flux ψ P) :=
  slice_integrable _ (vertical_integrable ψ P hP)

theorem lateralFlux_integrable (ψ : Aperture) (P : RealFlux)
    (hP : ∀ j, Integrable (fun x => P x j)) : Integrable (lateralFlux ψ P) :=
  slice_integrable _ (lateral_integrable ψ P hP)

theorem axis_derivative_weight_integrable (χ : Cutoff) (f : Space → ℝ) (hf : Integrable f) :
    Integrable (fun x => deriv χ.function (axis x) * f x) :=
  hf.bdd_mul ((measurable_deriv χ.function).comp axis.continuous.measurable).aestronglyMeasurable
    ⟨χ.lipschitzBound, fun _ => norm_deriv_le_of_lipschitz χ.lipschitz⟩

def volumeDensity (χ : Cutoff) (ψ : Aperture) (P : RealFlux) (x : Space) : ℝ :=
  deriv χ.function (axis x) * vertical ψ P x + χ.function (axis x) * lateral ψ P x

def cutoffTensor (χ : Cutoff) (ψ : Aperture) (x : Space) : ℝ :=
  χ.function (axis x) * ψ.function (transverse x)

theorem cutoffTensor_partial (χ : Cutoff) (ψ : Aperture) (x : Space)
    (hχ : DifferentiableAt ℝ χ.function (axis x))
    (hψ : DifferentiableAt ℝ ψ.function (transverse x)) (j : Fin 3) :
    fderiv ℝ (cutoffTensor χ ψ) x (basis j) =
      deriv χ.function (axis x) * axis (basis j) * ψ.function (transverse x) +
      χ.function (axis x) * fderiv ℝ ψ.function (transverse x) (transverse (basis j)) := by
  have ha := hχ.hasDerivAt.comp_hasFDerivAt x axis.hasFDerivAt
  have hb := hψ.hasFDerivAt.comp x transverse.hasFDerivAt
  have h := congrArg (fun L : Space →L[ℝ] ℝ => L (basis j)) (ha.mul hb).fderiv
  simpa [cutoffTensor, Function.comp_def, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc, add_comm] using h

theorem cutoffTensor_differentiable_factors_ae (χ : Cutoff) (ψ : Aperture) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ χ.function (axis x) ∧
      DifferentiableAt ℝ ψ.function (transverse x) := by
  have ht : Measure.QuasiMeasurePreserving axis volume volume :=
    Measure.quasiMeasurePreserving_fst.comp split_measurePreserving.quasiMeasurePreserving
  exact (ht.tendsto_ae.eventually (χ.lipschitz.ae_differentiableAt (μ := volume))).and
    (transverse_differentiable_ae ψ)

theorem volumeDensity_gradient_ae (χ : Cutoff) (ψ : Aperture) (P : RealFlux) :
    volumeDensity χ ψ P =ᵐ[volume] OQ14.LipschitzFlux.gradientFlux (cutoffTensor χ ψ) P := by
  filter_upwards [cutoffTensor_differentiable_factors_ae χ ψ] with x hx
  simp only [OQ14.LipschitzFlux.gradientFlux, cutoffTensor_partial χ ψ x hx.1 hx.2,
    transverse_basis_zero, transverse_basis_one, transverse_basis_two, map_zero]
  simp [volumeDensity, vertical, lateral, aperturePartial, axis, basis, EuclideanSpace.single_apply]
  ring

theorem volumeDensity_integrable (χ : Cutoff) (ψ : Aperture)
    (P : RealFlux) (hP : ∀ j, Integrable (fun x => P x j)) : Integrable (volumeDensity χ ψ P) :=
  (axis_derivative_weight_integrable χ _ (vertical_integrable ψ P hP)).add
    (axis_weight_integrable _ (lateral_integrable ψ P hP) _ χ.lipschitz.continuous χ.compact)

/-- Actual volume integration, with both axial and transverse a.e. derivatives. -/
theorem weighted_slab_Fubini (χ : Cutoff) (ψ : Aperture)
    (P : RealFlux) (hP : ∀ j, Integrable (fun x => P x j)) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in axis ⁻¹' Set.Ioc a b, volumeDensity χ ψ P x) =
      ∫ z in a..b, deriv χ.function z * flux ψ P z + χ.function z * lateralFlux ψ P z := by
  have hi := axis_derivative_weight_integrable χ _ (vertical_integrable ψ P hP)
  have hj := axis_weight_integrable _ (lateral_integrable ψ P hP) _ χ.lipschitz.continuous χ.compact
  have hif : Integrable (fun z => deriv χ.function z * flux ψ P z) :=
    (flux_integrable ψ P hP).bdd_mul (measurable_deriv χ.function).aestronglyMeasurable
      ⟨χ.lipschitzBound, fun _ => norm_deriv_le_of_lipschitz χ.lipschitz⟩
  have hjf : Integrable (fun z => χ.function z * lateralFlux ψ P z) :=
    (lateralFlux_integrable ψ P hP).bdd_mul χ.lipschitz.continuous.aestronglyMeasurable
      (χ.lipschitz.continuous.bounded_above_of_compact_support χ.compact)
  change (∫ x in axis ⁻¹' Set.Ioc a b,
    deriv χ.function (axis x) * vertical ψ P x + χ.function (axis x) * lateral ψ P x) = _
  rw [integral_add hi.integrableOn hj.integrableOn,
    OQ14.WeightedFlux.slab_coordinate_Fubini _ hi hab,
    OQ14.WeightedFlux.slab_coordinate_Fubini _ hj hab]
  simp_rw [axis_join, integral_const_mul]
  exact (intervalIntegral.integral_add hif.intervalIntegrable hjf.intervalIntegrable).symm

theorem maxwell_weighted_flux {Ω : Set Space} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (ψ : Aperture)
    (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (E H : OQ14.DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω μ ε E H) {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ I)
    (χ : Cutoff) (ha : χ.function a = 1) (hb : χ.function b = 0) :
    ∃ F : ℝ → ℝ, Continuous F ∧
      flux ψ (zeroExtendedPower Ω E H) =ᵐ[volume.restrict (Set.Icc a b)] F ∧
      (∀ c ∈ Set.Icc a b, ∀ d ∈ Set.Icc a b,
        F d - F c = ∫ z in c..d, lateralFlux ψ (zeroExtendedPower Ω E H) z) ∧
      F a = -(∫ x in axis ⁻¹' Set.Ioc a b, volumeDensity χ ψ (zeroExtendedPower Ω E H) x) := by
  obtain ⟨hf, hg, hw⟩ := aperture_weak_derivative hΩ ψ _
    (zeroExtendedPower_integrable hΩ.measurableSet E H) hbox
    (maxwell_zeroExtendedPower_divergence hΩ ω μ ε E H hM)
  obtain ⟨F, hF, hae, hinc⟩ := local_continuous_representative hI _ _ hf hg hw hsub
  refine ⟨F, hF, hae, hinc, ?_⟩
  rw [weighted_slab_Fubini χ ψ _ (zeroExtendedPower_integrable hΩ.measurableSet E H) hab.le]
  exact left_trace_identity hI _ _ hf hg hw hab hsub χ ha hb F hF hae

open OQ14.CrossFlux

def complexVertical (ψ : Aperture) (P : Space → Vector) (x : Space) : ℂ :=
  (ψ.function (transverse x) : ℂ) * P x 2

def complexTransverse (ψ : Aperture) (P : Space → Vector) (x : Space) : ℂ :=
  (aperturePartial ψ 0 (transverse x) : ℂ) * P x 0 +
    (aperturePartial ψ 1 (transverse x) : ℂ) * P x 1

def complexSlice (ψ : Aperture) (P : Space → Vector) (z : ℝ) : ℂ :=
  ∫ q : Plane, complexVertical ψ P (split.symm (z, q))

def complexDerivativeSlice (ψ : Aperture) (P : Space → Vector) (z : ℝ) : ℂ :=
  ∫ q : Plane, complexTransverse ψ P (split.symm (z, q))

theorem complexVertical_decomposition (ψ : Aperture) (P : Space → Vector) (x : Space) :
    complexVertical ψ P x = (vertical ψ (fun y j => (P y j).re) x : ℂ) +
      Complex.I * (vertical ψ (fun y j => (P y j).im) x : ℂ) := by
  apply Complex.ext <;> simp [complexVertical, vertical, Complex.mul_re, Complex.mul_im]

theorem complexTransverse_decomposition (ψ : Aperture) (P : Space → Vector) (x : Space) :
    complexTransverse ψ P x = (lateral ψ (fun y j => (P y j).re) x : ℂ) +
      Complex.I * (lateral ψ (fun y j => (P y j).im) x : ℂ) := by
  apply Complex.ext <;> simp [complexTransverse, lateral, Complex.mul_re, Complex.mul_im]

theorem complex_densities_integrable (ψ : Aperture) (P : Space → Vector)
    (hP : ∀ j, Integrable (fun x => P x j)) :
    Integrable (complexVertical ψ P) ∧ Integrable (complexTransverse ψ P) := by
  have hr (j : Fin 3) : Integrable (fun x => (P x j).re) := (hP j).re
  have hi (j : Fin 3) : Integrable (fun x => (P x j).im) := (hP j).im
  constructor
  · exact ((vertical_integrable ψ _ hr).ofReal.add
      ((vertical_integrable ψ _ hi).ofReal.const_mul Complex.I)).congr
      (Eventually.of_forall (fun x => (complexVertical_decomposition ψ P x).symm))
  · exact ((lateral_integrable ψ _ hr).ofReal.add
      ((lateral_integrable ψ _ hi).ofReal.const_mul Complex.I)).congr
      (Eventually.of_forall (fun x => (complexTransverse_decomposition ψ P x).symm))

theorem complexSlice_decomposition_ae (ψ : Aperture) (P : Space → Vector)
    (hP : ∀ j, Integrable (fun x => P x j)) :
    ∀ᵐ z ∂volume, complexSlice ψ P z =
      (flux ψ (fun y j => (P y j).re) z : ℂ) +
        Complex.I * (flux ψ (fun y j => (P y j).im) z : ℂ) := by
  simpa only [complexSlice, complexVertical, flux, vertical,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, zero_add, add_zero] using
    complex_slice_decomposition _ (complex_densities_integrable ψ P hP).1

theorem complexDerivativeSlice_decomposition_ae (ψ : Aperture) (P : Space → Vector)
    (hP : ∀ j, Integrable (fun x => P x j)) :
    ∀ᵐ z ∂volume, complexDerivativeSlice ψ P z =
      (lateralFlux ψ (fun y j => (P y j).re) z : ℂ) +
        Complex.I * (lateralFlux ψ (fun y j => (P y j).im) z : ℂ) := by
  simpa only [complexDerivativeSlice, complexTransverse, lateralFlux, lateral,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, zero_add, add_zero, Complex.add_re, Complex.add_im] using
    complex_slice_decomposition _ (complex_densities_integrable ψ P hP).2

def complexVolumeDensity (χ : Cutoff) (ψ : Aperture)
    (P : Space → Vector) (x : Space) : ℂ :=
  ((deriv χ.function (axis x) : ℝ) : ℂ) * complexVertical ψ P x +
    (χ.function (axis x) : ℂ) * complexTransverse ψ P x

theorem complexVolumeDensity_decomposition (χ : Cutoff) (ψ : Aperture)
    (P : Space → Vector) (x : Space) : complexVolumeDensity χ ψ P x =
      (volumeDensity χ ψ (fun y j => (P y j).re) x : ℂ) +
        Complex.I * (volumeDensity χ ψ (fun y j => (P y j).im) x : ℂ) := by
  apply Complex.ext <;>
    simp [complexVolumeDensity, complexVertical, complexTransverse, volumeDensity,
      vertical, lateral, Complex.mul_re, Complex.mul_im]

theorem complexVolumeDensity_integrable (χ : Cutoff) (ψ : Aperture)
    (P : Space → Vector) (hP : ∀ j, Integrable (fun x => P x j)) :
    Integrable (complexVolumeDensity χ ψ P) :=
  ((volumeDensity_integrable χ ψ _ (fun j => (hP j).re)).ofReal.add
    ((volumeDensity_integrable χ ψ _ (fun j => (hP j).im)).ofReal.const_mul Complex.I)).congr
    (Eventually.of_forall (fun x => (complexVolumeDensity_decomposition χ ψ P x).symm))

theorem complexVolumeDensity_gradient_ae (χ : Cutoff) (ψ : Aperture) (P : Space → Vector) :
    complexVolumeDensity χ ψ P =ᵐ[volume]
      OQ14.LipschitzFlux.complexGradientFlux (cutoffTensor χ ψ) P := by
  filter_upwards [cutoffTensor_differentiable_factors_ae χ ψ] with x hx
  simp only [OQ14.LipschitzFlux.complexGradientFlux, cutoffTensor_partial χ ψ x hx.1 hx.2,
    transverse_basis_zero, transverse_basis_one, transverse_basis_two, map_zero]
  simp [complexVolumeDensity, complexVertical, complexTransverse, aperturePartial,
    axis, basis, EuclideanSpace.single_apply]
  ring

theorem complex_slab_decomposition (χ : Cutoff) (ψ : Aperture)
    (P : Space → Vector) (hP : ∀ j, Integrable (fun x => P x j)) (a b : ℝ) :
    (∫ x in axis ⁻¹' Set.Ioc a b, complexVolumeDensity χ ψ P x) =
      ((∫ x in axis ⁻¹' Set.Ioc a b, volumeDensity χ ψ (fun y j => (P y j).re) x : ℝ) : ℂ) +
        Complex.I * ((∫ x in axis ⁻¹' Set.Ioc a b,
          volumeDensity χ ψ (fun y j => (P y j).im) x : ℝ) : ℂ) := by
  have hr := volumeDensity_integrable χ ψ _ (fun j => (hP j).re)
  have hi := volumeDensity_integrable χ ψ _ (fun j => (hP j).im)
  have heq : complexVolumeDensity χ ψ P = fun x =>
      (volumeDensity χ ψ (fun y j => (P y j).re) x : ℂ) +
        Complex.I * (volumeDensity χ ψ (fun y j => (P y j).im) x : ℂ) :=
    funext (complexVolumeDensity_decomposition χ ψ P)
  rw [heq]
  calc
    _ = (∫ x in axis ⁻¹' Set.Ioc a b,
        (volumeDensity χ ψ (fun y j => (P y j).re) x : ℂ)) +
        ∫ x in axis ⁻¹' Set.Ioc a b,
          Complex.I * (volumeDensity χ ψ (fun y j => (P y j).im) x : ℂ) :=
      integral_add hr.ofReal.integrableOn (hi.ofReal.const_mul Complex.I).integrableOn
    _ = _ := by rw [integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]

theorem complex_derivative_integral_decomposition (ψ : Aperture) (P : Space → Vector)
    (hP : ∀ j, Integrable (fun x => P x j)) (a b : ℝ) :
    (∫ z in a..b, complexDerivativeSlice ψ P z) =
      ((∫ z in a..b, lateralFlux ψ (fun y j => (P y j).re) z : ℝ) : ℂ) +
        Complex.I * ((∫ z in a..b, lateralFlux ψ (fun y j => (P y j).im) z : ℝ) : ℂ) := by
  have hr := lateralFlux_integrable ψ _ (fun j => (hP j).re)
  have hi := lateralFlux_integrable ψ _ (fun j => (hP j).im)
  have he := intervalIntegral.integral_congr_ae (a := a) (b := b)
    ((complexDerivativeSlice_decomposition_ae ψ P hP).mono (fun x hx _ => hx))
  rw [he]
  calc
    _ = (∫ z in a..b, (lateralFlux ψ (fun y j => (P y j).re) z : ℂ)) +
        ∫ z in a..b, Complex.I * (lateralFlux ψ (fun y j => (P y j).im) z : ℂ) :=
      intervalIntegral.integral_add hr.ofReal.intervalIntegrable
        (hi.ofReal.const_mul Complex.I).intervalIntegrable
    _ = _ := by rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]

/-- An actual integrable complex divergence-free vector field has canonical
continuous weighted plane flux, exact increments, and the full weighted volume law. -/
theorem complex_canonical_flux {Ω : Set Space} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (ψ : Aperture) (P : Space → Vector) (hP : ∀ j, Integrable (fun x => P x j))
    (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω)
    (hdivR : HasZeroDistributionalDivergence Ω (fun x j => (P x j).re))
    (hdivI : HasZeroDistributionalDivergence Ω (fun x j => (P x j).im))
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ I)
    (χ : Cutoff) (ha : χ.function a = 1) (hb : χ.function b = 0) :
    ∃ F : ℝ → ℂ, Continuous F ∧
      complexSlice ψ P =ᵐ[volume.restrict (Set.Icc a b)] F ∧
      (∀ c ∈ Set.Icc a b, ∀ d ∈ Set.Icc a b,
        F d - F c = ∫ z in c..d, complexDerivativeSlice ψ P z) ∧
      F a = -(∫ x in axis ⁻¹' Set.Ioc a b, complexVolumeDensity χ ψ P x) := by
  have hr (j : Fin 3) : Integrable (fun x => (P x j).re) := (hP j).re
  have hi (j : Fin 3) : Integrable (fun x => (P x j).im) := (hP j).im
  have hfr := flux_integrable ψ _ hr
  have hgr := lateralFlux_integrable ψ _ hr
  have hfi := flux_integrable ψ _ hi
  have hgi := lateralFlux_integrable ψ _ hi
  have hwr := (aperture_weak_derivative hΩ ψ _ hr hbox hdivR).2.2
  have hwi := (aperture_weak_derivative hΩ ψ _ hi hbox hdivI).2.2
  obtain ⟨Fr, hFr, har, hincr⟩ := local_continuous_representative hI _ _ hfr hgr hwr hsub
  obtain ⟨Fi, hFi, hai, hinci⟩ := local_continuous_representative hI _ _ hfi hgi hwi hsub
  refine ⟨fun z => (Fr z : ℂ) + Complex.I * (Fi z : ℂ),
    (Complex.continuous_ofReal.comp hFr).add
      (continuous_const.mul (Complex.continuous_ofReal.comp hFi)), ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae (complexSlice_decomposition_ae ψ P hP), har, hai]
      with z hz hzr hzi
    rw [hz, hzr, hzi]
  · intro c hc d hd
    rw [complex_derivative_integral_decomposition ψ P hP c d]
    calc
      _ = ((Fr d - Fr c : ℝ) : ℂ) + Complex.I * ((Fi d - Fi c : ℝ) : ℂ) := by
        push_cast
        ring
      _ = _ := by rw [hincr c hc d hd, hinci c hc d hd]
  · have her := left_trace_identity hI _ _ hfr hgr hwr hab hsub χ ha hb Fr hFr har
    have hei := left_trace_identity hI _ _ hfi hgi hwi hab hsub χ ha hb Fi hFi hai
    rw [← weighted_slab_Fubini χ ψ _ hr hab.le] at her
    rw [← weighted_slab_Fubini χ ψ _ hi hab.le] at hei
    dsimp only
    rw [complex_slab_decomposition χ ψ P hP a b, her, hei]
    push_cast
    ring

/-- The canonical complex plane value and volume law for two actual regional
Maxwell inputs, with no assumed polarization, trace, or representative theorem. -/
theorem maxwell_cross_flux {Ω : Set Space} {I : Set ℝ} (hΩ : IsOpen Ω) (hI : IsOpen I)
    (ψ : Aperture) (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (u v : State Ω)
    (hu : WeakMaxwell ω μ ε u.1 u.2) (hv : WeakMaxwell ω μ ε v.1 v.2)
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ I)
    (χ : Cutoff) (ha : χ.function a = 1) (hb : χ.function b = 0) :
    ∃ F : ℝ → ℂ, Continuous F ∧
      complexSlice ψ (crossFlux u v) =ᵐ[volume.restrict (Set.Icc a b)] F ∧
      (∀ c ∈ Set.Icc a b, ∀ d ∈ Set.Icc a b,
        F d - F c = ∫ z in c..d, complexDerivativeSlice ψ (crossFlux u v) z) ∧
      F a = -(∫ x in axis ⁻¹' Set.Ioc a b, complexVolumeDensity χ ψ (crossFlux u v) x) := by
  obtain ⟨hr, hi⟩ := crossFlux_components_conservation hΩ ω μ ε u v hu hv
  exact complex_canonical_flux hΩ hI ψ _ (crossFlux_integrable hΩ.measurableSet u v)
    hbox hr hi hab hsub χ ha hb

theorem complexSlice_symmetry {Ω : Set Space} (ψ : Aperture) (u v : State Ω) (z : ℝ) :
    complexSlice ψ (crossFlux u v) z = starRingEnd ℂ (complexSlice ψ (crossFlux v u) z) := by
  unfold complexSlice
  rw [← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall (fun q => by
    simp only [complexVertical, crossFlux_symmetry u v, map_mul, Complex.conj_ofReal])

theorem canonical_hermitian_symmetry {Ω : Set Space} (ψ : Aperture) (u v : State Ω)
    {a b : ℝ} (hab : a < b) (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hFa : complexSlice ψ (crossFlux u v) =ᵐ[volume.restrict (Set.Icc a b)] F)
    (hGa : complexSlice ψ (crossFlux v u) =ᵐ[volume.restrict (Set.Icc a b)] G) :
    ∀ x ∈ Set.Icc a b, F x = starRingEnd ℂ (G x) := by
  apply complex_representative_unique hab hF (Complex.continuous_conj.comp hG)
  filter_upwards [hFa, hGa] with x hx hy
  dsimp only [Function.comp_apply]
  rw [← hx, ← hy]
  exact complexSlice_symmetry ψ u v x

/-- The full actual gradient-volume formula for two regional weak Maxwell inputs
and arbitrary compact Lipschitz transverse and axial cutoffs. -/
theorem maxwell_cross_flux_gradient {Ω : Set Space} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (ψ : Aperture)
    (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (u v : State Ω)
    (hu : WeakMaxwell ω μ ε u.1 u.2) (hv : WeakMaxwell ω μ ε v.1 v.2)
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ I)
    (χ : Cutoff) (ha : χ.function a = 1) (hb : χ.function b = 0) :
    ∃ F : ℝ → ℂ, Continuous F ∧
      complexSlice ψ (crossFlux u v) =ᵐ[volume.restrict (Set.Icc a b)] F ∧
      (∀ c ∈ Set.Icc a b, ∀ d ∈ Set.Icc a b,
        F d - F c = ∫ z in c..d, complexDerivativeSlice ψ (crossFlux u v) z) ∧
      Integrable (OQ14.LipschitzFlux.complexGradientFlux (cutoffTensor χ ψ) (crossFlux u v)) ∧
      F a = -(∫ x in axis ⁻¹' Set.Ioc a b,
        OQ14.LipschitzFlux.complexGradientFlux (cutoffTensor χ ψ) (crossFlux u v) x) := by
  obtain ⟨F, hF, hae, hinc, hend⟩ := maxwell_cross_flux hΩ hI ψ hbox ω μ ε u v hu hv
    hab hsub χ ha hb
  have he := complexVolumeDensity_gradient_ae χ ψ (crossFlux u v)
  refine ⟨F, hF, hae, hinc, ?_, ?_⟩
  · exact (complexVolumeDensity_integrable χ ψ _
      (crossFlux_integrable hΩ.measurableSet u v)).congr he
  · rw [← integral_congr_ae (ae_restrict_of_ae he)]
    exact hend


end OQ14.LipschitzBoundary

#print axioms OQ14.LipschitzBoundary.cutoffTensor_differentiable_factors_ae
#print axioms OQ14.LipschitzBoundary.volumeDensity_gradient_ae
#print axioms OQ14.LipschitzBoundary.volumeDensity_integrable
#print axioms OQ14.LipschitzBoundary.weighted_slab_Fubini
#print axioms OQ14.LipschitzBoundary.maxwell_weighted_flux
#print axioms OQ14.LipschitzBoundary.complex_densities_integrable
#print axioms OQ14.LipschitzBoundary.complexSlice_decomposition_ae
#print axioms OQ14.LipschitzBoundary.complexVolumeDensity_integrable
#print axioms OQ14.LipschitzBoundary.complexVolumeDensity_gradient_ae
#print axioms OQ14.LipschitzBoundary.complex_canonical_flux
#print axioms OQ14.LipschitzBoundary.maxwell_cross_flux
#print axioms OQ14.LipschitzBoundary.complexSlice_symmetry
#print axioms OQ14.LipschitzBoundary.canonical_hermitian_symmetry
#print axioms OQ14.LipschitzBoundary.maxwell_cross_flux_gradient
