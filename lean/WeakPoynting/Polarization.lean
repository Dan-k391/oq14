import WeakPoynting.Weighted

/-!
# Hermitian cross-input flux for actual regional weak Maxwell fields

Complex linear closure is proved for the actual regional L2 weak curls.
Polarization is an explicit algebraic theorem about the physical cross products,
and its distributional and plane-value consequences are derived below.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.CrossFlux

open MeasureTheory OQ14.Maxwell OQ14.WeakConservation OQ14.FluxSlices
  OQ14.FluxRepresentative OQ14.WeightedFlux Filter
open scoped ComplexConjugate Topology

abbrev State (Ω : Set Space) := OQ14.DomainCurl.HCurl Ω × OQ14.DomainCurl.HCurl Ω

def field {Ω : Set Space} (u : OQ14.DomainCurl.HCurl Ω) : Field := fun x j => u.val.1 j x
def curlField {Ω : Set Space} (u : OQ14.DomainCurl.HCurl Ω) : Field := fun x j => u.val.2 j x

def combine {Ω : Set Space} (t : ℂ) (u v : State Ω) : State Ω := u + t • v

theorem field_combine_ae {Ω : Set Space} (t : ℂ) (u v : OQ14.DomainCurl.HCurl Ω) :
    ∀ᵐ x ∂OQ14.DomainCurl.regionMeasure Ω, ∀ j,
      field (u + t • v) x j = field u x j + t * field v x j := by
  have ha := ae_all_iff.mpr (fun j => Lp.coeFn_add (u.val.1 j) (t • v.val.1 j))
  have hs := ae_all_iff.mpr (fun j => Lp.coeFn_smul t (v.val.1 j))
  filter_upwards [ha, hs] with x ha hs
  intro j
  change (u.val.1 j + t • v.val.1 j) x = _
  rw [ha j]
  dsimp only [Pi.add_apply]
  rw [hs j]
  rfl

theorem curlField_combine_ae {Ω : Set Space} (t : ℂ) (u v : OQ14.DomainCurl.HCurl Ω) :
    ∀ᵐ x ∂OQ14.DomainCurl.regionMeasure Ω, ∀ j,
      curlField (u + t • v) x j = curlField u x j + t * curlField v x j := by
  have ha := ae_all_iff.mpr (fun j => Lp.coeFn_add (u.val.2 j) (t • v.val.2 j))
  have hs := ae_all_iff.mpr (fun j => Lp.coeFn_smul t (v.val.2 j))
  filter_upwards [ha, hs] with x ha hs
  intro j
  change (u.val.2 j + t • v.val.2 j) x = _
  rw [ha j]
  dsimp only [Pi.add_apply]
  rw [hs j]
  rfl

/-- The actual distributional Maxwell system is closed under complex combinations. -/
theorem maxwell_combine {Ω : Set Space} (ω : ℝ) (μ ε : Space → ℝ)
    (u v : State Ω) (hu : WeakMaxwell ω μ ε u.1 u.2)
    (hv : WeakMaxwell ω μ ε v.1 v.2) (t : ℂ) :
    WeakMaxwell ω μ ε (combine t u v).1 (combine t u v).2 := by
  constructor
  · filter_upwards [hu.1, hv.1, curlField_combine_ae t u.1 v.1,
      field_combine_ae t u.2 v.2] with x hu hv hc hf
    intro j
    change curlField (u.1 + t • v.1) x j = _
    rw [hc j]
    change _ = Complex.I * ω * μ x * field (u.2 + t • v.2) x j
    rw [hf j]
    dsimp only [curlField, field]
    rw [hu j, hv j]
    ring
  · filter_upwards [hu.2, hv.2, curlField_combine_ae t u.2 v.2,
      field_combine_ae t u.1 v.1] with x hu hv hc hf
    intro j
    change curlField (u.2 + t • v.2) x j = _
    rw [hc j]
    change _ = -Complex.I * ω * ε x * field (u.1 + t • v.1) x j
    rw [hf j]
    dsimp only [curlField, field]
    rw [hu j, hv j]
    ring

def diagonal (E H : Vector) (j : Fin 3) : ℝ :=
  (crossProduct E (conjugate H) j).re / 2

/-- The actual Hermitian cross-Poynting vector (normalization c0=1). -/
def hermitianPower (Ea Ha Eb Hb : Vector) (j : Fin 3) : ℂ :=
  (crossProduct Ea (conjugate Hb) j + crossProduct (conjugate Eb) Ha j) / 4

theorem hermitianPower_diagonal (E H : Vector) (j : Fin 3) :
    hermitianPower E H E H j = (diagonal E H j : ℂ) := by
  fin_cases j <;> apply Complex.ext <;>
    simp [hermitianPower, diagonal, conjugate, cross_apply,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem hermitianPower_symmetry (Ea Ha Eb Hb : Vector) (j : Fin 3) :
    hermitianPower Ea Ha Eb Hb j = conj (hermitianPower Eb Hb Ea Ha j) := by
  fin_cases j <;> simp [hermitianPower, conjugate, cross_apply, map_ofNat] <;> ring

/-- Explicit polarization into actual diagonal real fluxes; the +i sign is for
linearity in the first input and conjugate linearity in the second. -/
theorem hermitianPower_polarization (Ea Ha Eb Hb : Vector) (j : Fin 3) :
    hermitianPower Ea Ha Eb Hb j =
      (((diagonal (Ea + Eb) (Ha + Hb) j - diagonal (Ea - Eb) (Ha - Hb) j) / 4 : ℝ) : ℂ) +
      Complex.I * (((diagonal (Ea + Complex.I • Eb) (Ha + Complex.I • Hb) j -
        diagonal (Ea - Complex.I • Eb) (Ha - Complex.I • Hb) j) / 4 : ℝ) : ℂ) := by
  fin_cases j <;> apply Complex.ext <;>
    simp [hermitianPower, diagonal, conjugate, cross_apply,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.mul_re,
      Complex.mul_im] <;> ring

def mixedPower {Ω : Set Space} (t : ℂ) (u v : State Ω) : RealFlux :=
  zeroExtendedPower Ω (combine t u v).1 (combine t u v).2

def polarizedReal {Ω : Set Space} (t : ℂ) (u v : State Ω) : RealFlux :=
  fun x j => (mixedPower t u v x j - mixedPower (-t) u v x j) / 4

def crossFlux {Ω : Set Space} (u v : State Ω) (x : Space) (j : Fin 3) : ℂ :=
  Ω.indicator (fun y => hermitianPower (field u.1 y) (field u.2 y)
    (field v.1 y) (field v.2 y) j) x

theorem mixedPower_ae {Ω : Set Space} (_hΩ : MeasurableSet Ω) (t : ℂ) (u v : State Ω) :
    ∀ᵐ x ∂volume, ∀ j,
      mixedPower t u v x j = Ω.indicator (fun y =>
        diagonal (field u.1 y + t • field v.1 y)
          (field u.2 y + t • field v.2 y) j) x := by
  have he := ae_imp_of_ae_restrict (field_combine_ae t u.1 v.1)
  have hh := ae_imp_of_ae_restrict (field_combine_ae t u.2 v.2)
  filter_upwards [he, hh] with x he hh
  intro j
  by_cases hx : x ∈ Ω
  · have heq : field (u.1 + t • v.1) x = field u.1 x + t • field v.1 x :=
      funext (he hx)
    have hhq : field (u.2 + t • v.2) x = field u.2 x + t • field v.2 x :=
      funext (hh hx)
    change Ω.indicator (fun y => diagonal (field (u.1 + t • v.1) y)
      (field (u.2 + t • v.2) y) j) x = _
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, heq, hhq]
  · simp [mixedPower, zeroExtendedPower, hx]

/-- The actual cross product agrees a.e. with the polarization of actual L2 states. -/
theorem crossFlux_polarization_ae {Ω : Set Space} (hΩ : MeasurableSet Ω) (u v : State Ω) :
    ∀ᵐ x ∂volume, ∀ j, crossFlux u v x j =
      (polarizedReal 1 u v x j : ℂ) + Complex.I * (polarizedReal Complex.I u v x j : ℂ) := by
  filter_upwards [mixedPower_ae hΩ 1 u v, mixedPower_ae hΩ (-1) u v,
    mixedPower_ae hΩ Complex.I u v, mixedPower_ae hΩ (-Complex.I) u v] with x h1 hm hi hmi
  intro j
  by_cases hx : x ∈ Ω
  · simp only [polarizedReal, h1 j, hm j, hi j, hmi j,
      Set.indicator_of_mem hx]
    rw [show crossFlux u v x j = hermitianPower (field u.1 x) (field u.2 x)
      (field v.1 x) (field v.2 x) j from Set.indicator_of_mem hx _]
    simpa only [one_smul, neg_smul, one_smul, sub_eq_add_neg] using
      hermitianPower_polarization (field u.1 x) (field u.2 x) (field v.1 x) (field v.2 x) j
  · simp [crossFlux, polarizedReal, h1 j, hm j, hi j, hmi j, hx]

theorem polarizedReal_integrable {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (t : ℂ) (u v : State Ω) (j : Fin 3) : Integrable (fun x => polarizedReal t u v x j) :=
  ((zeroExtendedPower_integrable hΩ (combine t u v).1 (combine t u v).2 j).sub
    (zeroExtendedPower_integrable hΩ (combine (-t) u v).1 (combine (-t) u v).2 j)).div_const 4

theorem crossFlux_integrable {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (u v : State Ω) (j : Fin 3) : Integrable (fun x => crossFlux u v x j) := by
  have hi := (polarizedReal_integrable hΩ 1 u v j).ofReal.add
    ((polarizedReal_integrable hΩ Complex.I u v j).ofReal.const_mul Complex.I)
  apply hi.congr
  filter_upwards [crossFlux_polarization_ae hΩ u v] with x hx
  exact (hx j).symm

def testFlux {Ω : Set Space} (χ : RealTest Ω) (P : RealFlux) (x : Space) : ℝ :=
  fderiv ℝ χ.function x (basis 0) * P x 0 +
    fderiv ℝ χ.function x (basis 1) * P x 1 +
    fderiv ℝ χ.function x (basis 2) * P x 2

theorem testFlux_integrable {Ω : Set Space} (χ : RealTest Ω) (P : RealFlux)
    (hP : ∀ j, Integrable (fun x => P x j)) : Integrable (testFlux χ P) := by
  have hi (j : Fin 3) : Integrable (fun x => fderiv ℝ χ.function x (basis j) * P x j) := by
    have hc := (χ.regular.continuous_fderiv le_rfl).clm_apply (continuous_const (y := basis j))
    exact (hP j).bdd_mul hc.aestronglyMeasurable
      (hc.bounded_above_of_compact_support (χ.compact.fderiv_apply ℝ (basis j)))
  exact ((hi 0).add (hi 1)).add (hi 2)

theorem divergence_scaled_difference {Ω : Set Space} (P Q : RealFlux)
    (hP : ∀ j, Integrable (fun x => P x j)) (hQ : ∀ j, Integrable (fun x => Q x j))
    (hdP : HasZeroDistributionalDivergence Ω P) (hdQ : HasZeroDistributionalDivergence Ω Q) :
    HasZeroDistributionalDivergence Ω (fun x j => (P x j - Q x j) / 4) := by
  intro χ
  change (∫ x, testFlux χ (fun y j => (P y j - Q y j) / 4) x) = 0
  have heq : testFlux χ (fun y j => (P y j - Q y j) / 4) =
      fun x => (testFlux χ P x - testFlux χ Q x) / 4 := by
    funext x
    simp only [testFlux]
    ring
  rw [heq, integral_div, integral_sub (testFlux_integrable χ P hP)
    (testFlux_integrable χ Q hQ)]
  have hp : (∫ x, testFlux χ P x) = 0 := hdP χ
  have hq : (∫ x, testFlux χ Q x) = 0 := hdQ χ
  rw [hp, hq]
  norm_num

/-- Real and imaginary polarization components inherit conservation from actual
diagonal Maxwell conservation and the proved complex linear closure. -/
theorem polarizedReal_conservation {Ω : Set Space} (hΩ : IsOpen Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (u v : State Ω)
    (hu : WeakMaxwell ω μ ε u.1 u.2) (hv : WeakMaxwell ω μ ε v.1 v.2) (t : ℂ) :
    HasZeroDistributionalDivergence Ω (polarizedReal t u v) := by
  exact divergence_scaled_difference _ _
    (zeroExtendedPower_integrable hΩ.measurableSet (combine t u v).1 (combine t u v).2)
    (zeroExtendedPower_integrable hΩ.measurableSet (combine (-t) u v).1 (combine (-t) u v).2)
    (maxwell_zeroExtendedPower_divergence hΩ ω μ ε _ _ (maxwell_combine ω μ ε u v hu hv t))
    (maxwell_zeroExtendedPower_divergence hΩ ω μ ε _ _ (maxwell_combine ω μ ε u v hu hv (-t)))

theorem crossFlux_re_ae {Ω : Set Space} (hΩ : MeasurableSet Ω) (u v : State Ω) :
    ∀ᵐ x ∂volume, ∀ j, (crossFlux u v x j).re = polarizedReal 1 u v x j := by
  filter_upwards [crossFlux_polarization_ae hΩ u v] with x hx
  intro j
  rw [hx j]
  simp

theorem crossFlux_im_ae {Ω : Set Space} (hΩ : MeasurableSet Ω) (u v : State Ω) :
    ∀ᵐ x ∂volume, ∀ j, (crossFlux u v x j).im = polarizedReal Complex.I u v x j := by
  filter_upwards [crossFlux_polarization_ae hΩ u v] with x hx
  intro j
  rw [hx j]
  simp

theorem divergence_congr {Ω : Set Space} {P Q : RealFlux}
    (hae : ∀ᵐ x ∂volume, ∀ j, P x j = Q x j)
    (hQ : HasZeroDistributionalDivergence Ω Q) : HasZeroDistributionalDivergence Ω P := by
  intro χ
  have he : (fun x => testFlux χ P x) =ᵐ[volume] (fun x => testFlux χ Q x) := by
    filter_upwards [hae] with x hx
    simp only [testFlux, hx]
  exact (integral_congr_ae he).trans (hQ χ)

/-- Both components of the actual Hermitian cross product are divergence-free. -/
theorem crossFlux_components_conservation {Ω : Set Space} (hΩ : IsOpen Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (u v : State Ω)
    (hu : WeakMaxwell ω μ ε u.1 u.2) (hv : WeakMaxwell ω μ ε v.1 v.2) :
    HasZeroDistributionalDivergence Ω (fun x j => (crossFlux u v x j).re) ∧
    HasZeroDistributionalDivergence Ω (fun x j => (crossFlux u v x j).im) :=
  ⟨divergence_congr (crossFlux_re_ae hΩ.measurableSet u v)
    (polarizedReal_conservation hΩ ω μ ε u v hu hv 1),
   divergence_congr (crossFlux_im_ae hΩ.measurableSet u v)
    (polarizedReal_conservation hΩ ω μ ε u v hu hv Complex.I)⟩

def complexTestFlux {Ω : Set Space} (χ : RealTest Ω) (P : Space → Vector) (x : Space) : ℂ :=
  (fderiv ℝ χ.function x (basis 0) : ℂ) * P x 0 +
    (fderiv ℝ χ.function x (basis 1) : ℂ) * P x 1 +
    (fderiv ℝ χ.function x (basis 2) : ℂ) * P x 2

theorem complexTestFlux_decomposition {Ω : Set Space} (χ : RealTest Ω)
    (P : Space → Vector) (x : Space) : complexTestFlux χ P x =
      (testFlux χ (fun y j => (P y j).re) x : ℂ) +
        Complex.I * (testFlux χ (fun y j => (P y j).im) x : ℂ) := by
  apply Complex.ext <;> simp [complexTestFlux, testFlux, Complex.mul_re, Complex.mul_im]

/-- Genuine complex weak conservation, with independent integrability of the pairing. -/
theorem crossFlux_conservation {Ω : Set Space} (hΩ : IsOpen Ω) (χ : RealTest Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (u v : State Ω)
    (hu : WeakMaxwell ω μ ε u.1 u.2) (hv : WeakMaxwell ω μ ε v.1 v.2) :
    Integrable (complexTestFlux χ (crossFlux u v)) ∧
      (∫ x, complexTestFlux χ (crossFlux u v) x) = 0 := by
  have hi := testFlux_integrable χ _ (fun j => (crossFlux_integrable hΩ.measurableSet u v j).re)
  have hj := testFlux_integrable χ _ (fun j => (crossFlux_integrable hΩ.measurableSet u v j).im)
  simp only [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im] at hi hj
  obtain ⟨hr, hm⟩ := crossFlux_components_conservation hΩ ω μ ε u v hu hv
  have heq : complexTestFlux χ (crossFlux u v) = fun x =>
      (testFlux χ (fun y j => (crossFlux u v y j).re) x : ℂ) +
        Complex.I * (testFlux χ (fun y j => (crossFlux u v y j).im) x : ℂ) :=
    funext (complexTestFlux_decomposition χ (crossFlux u v))
  rw [heq]
  refine ⟨hi.ofReal.add (hj.ofReal.const_mul Complex.I), ?_⟩
  dsimp only
  have hadd : (∫ x, (testFlux χ (fun y j => (crossFlux u v y j).re) x : ℂ) +
        Complex.I * (testFlux χ (fun y j => (crossFlux u v y j).im) x : ℂ)) =
      (∫ x, (testFlux χ (fun y j => (crossFlux u v y j).re) x : ℂ)) +
        ∫ x, Complex.I * (testFlux χ (fun y j => (crossFlux u v y j).im) x : ℂ) :=
    integral_add hi.ofReal (hj.ofReal.const_mul Complex.I)
  rw [hadd, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  have hr0 : (∫ x, testFlux χ (fun y j => (crossFlux u v y j).re) x) = 0 := hr χ
  have hm0 : (∫ x, testFlux χ (fun y j => (crossFlux u v y j).im) x) = 0 := hm χ
  rw [hr0, hm0]
  simp

def complexVertical (ψ : PlaneTest) (P : Space → Vector) (x : Space) : ℂ :=
  (ψ.function (transverse x) : ℂ) * P x 2

def complexTransverse (ψ : PlaneTest) (P : Space → Vector) (x : Space) : ℂ :=
  (planePartial ψ 0 (transverse x) : ℂ) * P x 0 +
    (planePartial ψ 1 (transverse x) : ℂ) * P x 1

def complexSlice (ψ : PlaneTest) (P : Space → Vector) (z : ℝ) : ℂ :=
  ∫ q : Plane, complexVertical ψ P (split.symm (z, q))

def complexDerivativeSlice (ψ : PlaneTest) (P : Space → Vector) (z : ℝ) : ℂ :=
  ∫ q : Plane, complexTransverse ψ P (split.symm (z, q))

theorem complexVertical_decomposition (ψ : PlaneTest) (P : Space → Vector) (x : Space) :
    complexVertical ψ P x = (verticalDensity ψ (fun y j => (P y j).re) x : ℂ) +
      Complex.I * (verticalDensity ψ (fun y j => (P y j).im) x : ℂ) := by
  apply Complex.ext <;> simp [complexVertical, verticalDensity, Complex.mul_re, Complex.mul_im]

theorem complexTransverse_decomposition (ψ : PlaneTest) (P : Space → Vector) (x : Space) :
    complexTransverse ψ P x = (transverseDensity ψ (fun y j => (P y j).re) x : ℂ) +
      Complex.I * (transverseDensity ψ (fun y j => (P y j).im) x : ℂ) := by
  apply Complex.ext <;> simp [complexTransverse, transverseDensity, Complex.mul_re, Complex.mul_im]

theorem complex_densities_integrable (ψ : PlaneTest) (P : Space → Vector)
    (hP : ∀ j, Integrable (fun x => P x j)) :
    Integrable (complexVertical ψ P) ∧ Integrable (complexTransverse ψ P) := by
  have hr (j : Fin 3) : Integrable (fun x => (P x j).re) := (hP j).re
  have hi (j : Fin 3) : Integrable (fun x => (P x j).im) := (hP j).im
  constructor
  · exact ((verticalDensity_integrable ψ _ hr).ofReal.add
      ((verticalDensity_integrable ψ _ hi).ofReal.const_mul Complex.I)).congr
      (Eventually.of_forall (fun x => (complexVertical_decomposition ψ P x).symm))
  · exact ((transverseDensity_integrable ψ _ hr).ofReal.add
      ((transverseDensity_integrable ψ _ hi).ofReal.const_mul Complex.I)).congr
      (Eventually.of_forall (fun x => (complexTransverse_decomposition ψ P x).symm))

theorem complex_slice_integrable (f : Space → ℂ) (hf : Integrable f) :
    Integrable (fun z : ℝ => ∫ q : Plane, f (split.symm (z, q))) := by
  have hi : Integrable (fun p : ℝ × Plane => f (split.symm p)) :=
    ((MeasurePreserving.symm split split_measurePreserving).integrable_comp_emb
      split.symm.measurableEmbedding).mpr hf
  exact hi.integral_prod_left

theorem complex_slice_decomposition (f : Space → ℂ) (hf : Integrable f) :
    ∀ᵐ z ∂volume, (∫ q : Plane, f (split.symm (z, q))) =
      ((∫ q : Plane, (f (split.symm (z, q))).re : ℝ) : ℂ) +
        Complex.I * ((∫ q : Plane, (f (split.symm (z, q))).im : ℝ) : ℂ) := by
  have hi : Integrable (fun p : ℝ × Plane => f (split.symm p)) :=
    ((MeasurePreserving.symm split split_measurePreserving).integrable_comp_emb
      split.symm.measurableEmbedding).mpr hf
  filter_upwards [hi.prod_right_ae] with z hz
  simpa only [RCLike.re_eq_complex_re, RCLike.im_eq_complex_im, RCLike.I_to_complex,
    mul_comm] using (integral_re_add_im hz).symm

theorem complexSlice_decomposition_ae (ψ : PlaneTest) (P : Space → Vector)
    (hP : ∀ j, Integrable (fun x => P x j)) :
    ∀ᵐ z ∂volume, complexSlice ψ P z =
      (fluxSlice ψ (fun y j => (P y j).re) z : ℂ) +
        Complex.I * (fluxSlice ψ (fun y j => (P y j).im) z : ℂ) := by
  simpa only [complexSlice, complexVertical, fluxSlice, verticalDensity,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, zero_add, add_zero] using
    complex_slice_decomposition _ (complex_densities_integrable ψ P hP).1

theorem complexDerivativeSlice_decomposition_ae (ψ : PlaneTest) (P : Space → Vector)
    (hP : ∀ j, Integrable (fun x => P x j)) :
    ∀ᵐ z ∂volume, complexDerivativeSlice ψ P z =
      (derivativeSlice ψ (fun y j => (P y j).re) z : ℂ) +
        Complex.I * (derivativeSlice ψ (fun y j => (P y j).im) z : ℂ) := by
  simpa only [complexDerivativeSlice, complexTransverse, derivativeSlice, transverseDensity,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, zero_add, add_zero, Complex.add_re, Complex.add_im] using
    complex_slice_decomposition _ (complex_densities_integrable ψ P hP).2

def complexVolumeDensity (χ : LineTest Set.univ) (ψ : PlaneTest)
    (P : Space → Vector) (x : Space) : ℂ :=
  ((deriv χ.function (axis x) : ℝ) : ℂ) * complexVertical ψ P x +
    (χ.function (axis x) : ℂ) * complexTransverse ψ P x

theorem complexVolumeDensity_decomposition (χ : LineTest Set.univ) (ψ : PlaneTest)
    (P : Space → Vector) (x : Space) : complexVolumeDensity χ ψ P x =
      (volumeDensity χ ψ (fun y j => (P y j).re) x : ℂ) +
        Complex.I * (volumeDensity χ ψ (fun y j => (P y j).im) x : ℂ) := by
  apply Complex.ext <;>
    simp [complexVolumeDensity, complexVertical, complexTransverse, volumeDensity,
      verticalDensity, transverseDensity, Complex.mul_re, Complex.mul_im]

theorem complexVolumeDensity_gradient (χ : LineTest Set.univ) (ψ : PlaneTest)
    (P : Space → Vector) (x : Space) : complexVolumeDensity χ ψ P x =
      ((fderiv ℝ (tensorFunction ψ χ) x (basis 0) : ℝ) : ℂ) * P x 0 +
      ((fderiv ℝ (tensorFunction ψ χ) x (basis 1) : ℝ) : ℂ) * P x 1 +
      ((fderiv ℝ (tensorFunction ψ χ) x (basis 2) : ℝ) : ℂ) * P x 2 := by
  rw [tensor_partial_zero, tensor_partial_one, tensor_partial_two]
  simp only [complexVolumeDensity, complexVertical, complexTransverse, Complex.ofReal_mul]
  ring

theorem complexVolumeDensity_integrable (χ : LineTest Set.univ) (ψ : PlaneTest)
    (P : Space → Vector) (hP : ∀ j, Integrable (fun x => P x j)) :
    Integrable (complexVolumeDensity χ ψ P) :=
  ((volumeDensity_integrable χ ψ _ (fun j => (hP j).re)).ofReal.add
    ((volumeDensity_integrable χ ψ _ (fun j => (hP j).im)).ofReal.const_mul Complex.I)).congr
    (Eventually.of_forall (fun x => (complexVolumeDensity_decomposition χ ψ P x).symm))

theorem complex_slab_decomposition (χ : LineTest Set.univ) (ψ : PlaneTest)
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

theorem complex_derivative_integral_decomposition (ψ : PlaneTest) (P : Space → Vector)
    (hP : ∀ j, Integrable (fun x => P x j)) (a b : ℝ) :
    (∫ z in a..b, complexDerivativeSlice ψ P z) =
      ((∫ z in a..b, derivativeSlice ψ (fun y j => (P y j).re) z : ℝ) : ℂ) +
        Complex.I * ((∫ z in a..b, derivativeSlice ψ (fun y j => (P y j).im) z : ℝ) : ℂ) := by
  have hr := derivativeSlice_integrable ψ _ (fun j => (hP j).re)
  have hi := derivativeSlice_integrable ψ _ (fun j => (hP j).im)
  have he := intervalIntegral.integral_congr_ae (a := a) (b := b)
    ((complexDerivativeSlice_decomposition_ae ψ P hP).mono (fun x hx _ => hx))
  rw [he]
  calc
    _ = (∫ z in a..b, (derivativeSlice ψ (fun y j => (P y j).re) z : ℂ)) +
        ∫ z in a..b, Complex.I * (derivativeSlice ψ (fun y j => (P y j).im) z : ℂ) :=
      intervalIntegral.integral_add hr.ofReal.intervalIntegrable
        (hi.ofReal.const_mul Complex.I).intervalIntegrable
    _ = _ := by rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]

/-- An actual integrable complex divergence-free vector field has canonical
continuous weighted plane flux, exact increments, and the full weighted volume law. -/
theorem complex_canonical_flux {Ω : Set Space} {I : Set ℝ} (hI : IsOpen I)
    (ψ : PlaneTest) (P : Space → Vector) (hP : ∀ j, Integrable (fun x => P x j))
    (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω)
    (hdivR : HasZeroDistributionalDivergence Ω (fun x j => (P x j).re))
    (hdivI : HasZeroDistributionalDivergence Ω (fun x j => (P x j).im))
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ I)
    (χ : LineTest Set.univ) (ha : χ.function a = 1) (hb : χ.function b = 0) :
    ∃ F : ℝ → ℂ, Continuous F ∧
      complexSlice ψ P =ᵐ[volume.restrict (Set.Icc a b)] F ∧
      (∀ c ∈ Set.Icc a b, ∀ d ∈ Set.Icc a b,
        F d - F c = ∫ z in c..d, complexDerivativeSlice ψ P z) ∧
      F a = -(∫ x in axis ⁻¹' Set.Ioc a b, complexVolumeDensity χ ψ P x) := by
  have hr (j : Fin 3) : Integrable (fun x => (P x j).re) := (hP j).re
  have hi (j : Fin 3) : Integrable (fun x => (P x j).im) := (hP j).im
  have hfr := fluxSlice_integrable ψ _ hr
  have hgr := derivativeSlice_integrable ψ _ hr
  have hfi := fluxSlice_integrable ψ _ hi
  have hgi := derivativeSlice_integrable ψ _ hi
  have hwr := fluxSlice_weak_derivative ψ _ hr hbox hdivR
  have hwi := fluxSlice_weak_derivative ψ _ hi hbox hdivI
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
    (ψ : PlaneTest) (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (u v : State Ω)
    (hu : WeakMaxwell ω μ ε u.1 u.2) (hv : WeakMaxwell ω μ ε v.1 v.2)
    {a b : ℝ} (hab : a < b) (hsub : Set.Icc a b ⊆ I)
    (χ : LineTest Set.univ) (ha : χ.function a = 1) (hb : χ.function b = 0) :
    ∃ F : ℝ → ℂ, Continuous F ∧
      complexSlice ψ (crossFlux u v) =ᵐ[volume.restrict (Set.Icc a b)] F ∧
      (∀ c ∈ Set.Icc a b, ∀ d ∈ Set.Icc a b,
        F d - F c = ∫ z in c..d, complexDerivativeSlice ψ (crossFlux u v) z) ∧
      F a = -(∫ x in axis ⁻¹' Set.Ioc a b, complexVolumeDensity χ ψ (crossFlux u v) x) := by
  obtain ⟨hr, hi⟩ := crossFlux_components_conservation hΩ ω μ ε u v hu hv
  exact complex_canonical_flux hI ψ _ (crossFlux_integrable hΩ.measurableSet u v)
    hbox hr hi hab hsub χ ha hb

theorem hermitianPower_add_left (Ea Ha Ec Hc Eb Hb : Vector) (j : Fin 3) :
    hermitianPower (Ea + Ec) (Ha + Hc) Eb Hb j =
      hermitianPower Ea Ha Eb Hb j + hermitianPower Ec Hc Eb Hb j := by
  fin_cases j <;> simp [hermitianPower, conjugate, cross_apply, Pi.add_apply] <;> ring

theorem hermitianPower_smul_left (t : ℂ) (Ea Ha Eb Hb : Vector) (j : Fin 3) :
    hermitianPower (t • Ea) (t • Ha) Eb Hb j = t * hermitianPower Ea Ha Eb Hb j := by
  fin_cases j <;>
    simp [hermitianPower, conjugate, cross_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem hermitianPower_smul_right (t : ℂ) (Ea Ha Eb Hb : Vector) (j : Fin 3) :
    hermitianPower Ea Ha (t • Eb) (t • Hb) j = conj t * hermitianPower Ea Ha Eb Hb j := by
  rw [hermitianPower_symmetry Ea Ha (t • Eb) (t • Hb),
    hermitianPower_smul_left, map_mul, ← hermitianPower_symmetry]

theorem complex_representative_unique {a b : ℝ} (hab : a < b) {F G : ℝ → ℂ}
    (hF : Continuous F) (hG : Continuous G)
    (hae : F =ᵐ[volume.restrict (Set.Icc a b)] G) : Set.EqOn F G (Set.Icc a b) := by
  have hr := representative_unique hab (Complex.continuous_re.comp hF)
    (Complex.continuous_re.comp hG) (hae.mono (fun _ hx => congrArg Complex.re hx))
  have hi := representative_unique hab (Complex.continuous_im.comp hF)
    (Complex.continuous_im.comp hG) (hae.mono (fun _ hx => congrArg Complex.im hx))
  intro x hx
  exact Complex.ext (hr hx) (hi hx)

theorem crossFlux_symmetry {Ω : Set Space} (u v : State Ω) (x : Space) (j : Fin 3) :
    crossFlux u v x j = conj (crossFlux v u x j) := by
  by_cases hx : x ∈ Ω
  · simp only [crossFlux, Set.indicator_of_mem hx]
    exact hermitianPower_symmetry _ _ _ _ j
  · simp [crossFlux, hx]

theorem complexSlice_symmetry {Ω : Set Space} (ψ : PlaneTest) (u v : State Ω) (z : ℝ) :
    complexSlice ψ (crossFlux u v) z = conj (complexSlice ψ (crossFlux v u) z) := by
  unfold complexSlice
  rw [← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall (fun q => by
    simp only [complexVertical, crossFlux_symmetry u v, map_mul, Complex.conj_ofReal])

/-- The canonical values, not only a.e. plane slices, inherit Hermitian symmetry. -/
theorem canonical_hermitian_symmetry {Ω : Set Space} (ψ : PlaneTest) (u v : State Ω)
    {a b : ℝ} (hab : a < b) (F G : ℝ → ℂ) (hF : Continuous F) (hG : Continuous G)
    (hFa : complexSlice ψ (crossFlux u v) =ᵐ[volume.restrict (Set.Icc a b)] F)
    (hGa : complexSlice ψ (crossFlux v u) =ᵐ[volume.restrict (Set.Icc a b)] G) :
    ∀ x ∈ Set.Icc a b, F x = conj (G x) := by
  apply complex_representative_unique hab hF (Complex.continuous_conj.comp hG)
  filter_upwards [hFa, hGa] with x hx hy
  dsimp only [Function.comp_apply]
  rw [← hx, ← hy]
  exact complexSlice_symmetry ψ u v x

end OQ14.CrossFlux

#print axioms OQ14.CrossFlux.field_combine_ae
#print axioms OQ14.CrossFlux.curlField_combine_ae
#print axioms OQ14.CrossFlux.maxwell_combine
#print axioms OQ14.CrossFlux.hermitianPower_diagonal
#print axioms OQ14.CrossFlux.hermitianPower_symmetry
#print axioms OQ14.CrossFlux.hermitianPower_polarization
#print axioms OQ14.CrossFlux.crossFlux_polarization_ae
#print axioms OQ14.CrossFlux.polarizedReal_integrable
#print axioms OQ14.CrossFlux.crossFlux_integrable
#print axioms OQ14.CrossFlux.polarizedReal_conservation
#print axioms OQ14.CrossFlux.crossFlux_components_conservation
#print axioms OQ14.CrossFlux.crossFlux_conservation
#print axioms OQ14.CrossFlux.complex_densities_integrable
#print axioms OQ14.CrossFlux.complex_slice_integrable
#print axioms OQ14.CrossFlux.complexSlice_decomposition_ae
#print axioms OQ14.CrossFlux.complexDerivativeSlice_decomposition_ae
#print axioms OQ14.CrossFlux.complexVolumeDensity_integrable
#print axioms OQ14.CrossFlux.complexVolumeDensity_gradient
#print axioms OQ14.CrossFlux.complex_slab_decomposition
#print axioms OQ14.CrossFlux.complex_derivative_integral_decomposition
#print axioms OQ14.CrossFlux.complex_canonical_flux
#print axioms OQ14.CrossFlux.maxwell_cross_flux
#print axioms OQ14.CrossFlux.hermitianPower_add_left
#print axioms OQ14.CrossFlux.hermitianPower_smul_left
#print axioms OQ14.CrossFlux.hermitianPower_smul_right
#print axioms OQ14.CrossFlux.complex_representative_unique
#print axioms OQ14.CrossFlux.complexSlice_symmetry
#print axioms OQ14.CrossFlux.canonical_hermitian_symmetry
