import FrequencyScalingMaxwell
import StaticNewton

/-!
# The dilation operator on `VectorL2` and its commutation with the static machinery

For `k > 0` the dilation `dilate k : VectorL2 →L[ℂ] VectorL2`, `(dilate k u) ξ = k • u (k ξ)` almost
everywhere, is a bounded operator with `‖dilate k u‖ = sqrt k⁻¹ * ‖u‖`, `dilate 1 = 1`,
`dilate k (dilate k' u) = dilate (k * k') u`, `dilate k ∘L dilate k⁻¹ = 1`.

Commutations (all for `k > 0`):
* `sqrtMultiplier (scaleCoeff k c) (dilate k u) = dilate k (sqrtMultiplier c u)`;
* `source (scaleCoeff k c) (dilate k u) j y = k * source c u j (k y)` almost everywhere;
* the Fourier intertwining `fourier (dilate k u) = k⁻¹ • dilate k⁻¹ (fourier u)` for the Mathlib
  normalization `𝓕 g (η) = ∫ e^{-2πi⟨x,η⟩} g x dx` (Schwartz change of variables and density);
* the longitudinal multiplier, `physicalProjection`, `newtonOperator`, the static `response` and
  `volumeBlock` of `scaleCoeff k c` commute with `dilate k` (the symbol is homogeneous of degree zero);
* `physicalCoordinate (dilate k F) i = k * physicalCoordinate F i (k ·)` almost everywhere.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.DilationL2
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate FourierTransform SchwartzMap

abbrev Frequency := VectorFourier.Frequency
abbrev Space := FourierL2.Space
abbrev VectorL2 := VectorFourier.VectorL2

/-! ### Measure-theoretic facts about the dilation of frequency space -/

theorem finrank_frequency : Module.finrank ℝ Frequency = 3 := by
  simp [Frequency, VectorFourier.Frequency, LongitudinalProjection.Frequency]

theorem finrank_space : Module.finrank ℝ Space = 3 := by
  simp [Space, FourierL2.Space]

theorem map_smul_frequency (k : ℝ) (hk : k ≠ 0) :
    Measure.map (fun ξ : Frequency => k • ξ) volume = ENNReal.ofReal (|(k ^ 3)⁻¹|) • volume := by
  have h := Measure.map_addHaar_smul (volume : Measure Frequency) hk
  rwa [finrank_frequency] at h

theorem smul_qmp_frequency (k : ℝ) (hk : k ≠ 0) :
    Measure.QuasiMeasurePreserving (fun ξ : Frequency => k • ξ) volume volume :=
  Measure.quasiMeasurePreserving_smul (volume : Measure Frequency) hk

theorem smul_qmp_space (k : ℝ) (hk : k ≠ 0) :
    Measure.QuasiMeasurePreserving (fun x : Space => k • x) volume volume :=
  Measure.quasiMeasurePreserving_smul (volume : Measure Space) hk

theorem ae_smul_frequency (k : ℝ) (hk : k ≠ 0) {P : Frequency → Prop}
    (h : ∀ᵐ ξ ∂(volume : Measure Frequency), P ξ) :
    ∀ᵐ ξ ∂(volume : Measure Frequency), P (k • ξ) :=
  (smul_qmp_frequency k hk).ae h

theorem ae_smul_space (k : ℝ) (hk : k ≠ 0) {P : Space → Prop}
    (h : ∀ᵐ x ∂(volume : Measure Space), P x) :
    ∀ᵐ x ∂(volume : Measure Space), P (k • x) :=
  (smul_qmp_space k hk).ae h

theorem integral_comp_smul_frequency {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Frequency → F) (k : ℝ) :
    ∫ ξ, f (k • ξ) = |(k ^ 3)⁻¹| • ∫ ξ, f ξ := by
  have h := Measure.integral_comp_smul (volume : Measure Frequency) f k
  rwa [finrank_frequency] at h

theorem integral_comp_smul_space {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Space → F) (k : ℝ) :
    ∫ x, f (k • x) = |(k ^ 3)⁻¹| • ∫ x, f x := by
  have h := Measure.integral_comp_smul (volume : Measure Space) f k
  rwa [finrank_space] at h

/-! ### The dilation operator -/

theorem memLp_dilate (k : ℝ) (hk : 0 < k) (u : VectorL2) :
    MemLp (fun ξ : Frequency => (k : ℂ) • u (k • ξ)) 2 volume := by
  have hmap : MemLp (u : Frequency → VectorFourier.Vector) 2
      (Measure.map (fun ξ : Frequency => k • ξ) volume) := by
    rw [map_smul_frequency k hk.ne']
    exact (Lp.memLp u).smul_measure ENNReal.ofReal_ne_top
  have h1 : MemLp ((u : Frequency → VectorFourier.Vector) ∘ fun ξ : Frequency => k • ξ) 2 volume :=
    (memLp_map_measure_iff hmap.1 (smul_qmp_frequency k hk.ne').aemeasurable).mp hmap
  exact h1.const_smul (k : ℂ)

/-- The dilation of a vector in `L²` as an element of `L²`. -/
def dilateFun (k : ℝ) (hk : 0 < k) (u : VectorL2) : VectorL2 :=
  (memLp_dilate k hk u).toLp (fun ξ : Frequency => (k : ℂ) • u (k • ξ))

theorem dilateFun_ae (k : ℝ) (hk : 0 < k) (u : VectorL2) :
    dilateFun k hk u =ᵐ[volume] fun ξ : Frequency => (k : ℂ) • u (k • ξ) :=
  (memLp_dilate k hk u).coeFn_toLp

theorem dilateFun_add (k : ℝ) (hk : 0 < k) (u v : VectorL2) :
    dilateFun k hk (u + v) = dilateFun k hk u + dilateFun k hk v := by
  apply Lp.ext
  have h := ae_smul_frequency k hk.ne' (Lp.coeFn_add u v)
  filter_upwards [dilateFun_ae k hk (u + v), dilateFun_ae k hk u, dilateFun_ae k hk v, h,
    Lp.coeFn_add (dilateFun k hk u) (dilateFun k hk v)] with ξ h1 h2 h3 h4 h5
  rw [h1, h5]
  simp only [Pi.add_apply, h2, h3]
  rw [h4]
  simp only [Pi.add_apply, smul_add]

theorem dilateFun_smul (k : ℝ) (hk : 0 < k) (c : ℂ) (u : VectorL2) :
    dilateFun k hk (c • u) = c • dilateFun k hk u := by
  apply Lp.ext
  have h := ae_smul_frequency k hk.ne' (Lp.coeFn_smul c u)
  filter_upwards [dilateFun_ae k hk (c • u), dilateFun_ae k hk u, h,
    Lp.coeFn_smul c (dilateFun k hk u)] with ξ h1 h2 h3 h4
  rw [h1, h4]
  simp only [Pi.smul_apply, h2]
  rw [h3]
  simp only [Pi.smul_apply]
  exact smul_comm _ _ _

theorem dilateFun_inner (k : ℝ) (hk : 0 < k) (u v : VectorL2) :
    ⟪dilateFun k hk u, dilateFun k hk v⟫_ℂ = ((k⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have h1 : ∫ ξ : Frequency, ⟪dilateFun k hk u ξ, dilateFun k hk v ξ⟫_ℂ =
      ∫ ξ : Frequency, ((k ^ 2 : ℝ) : ℂ) * ⟪u (k • ξ), v (k • ξ)⟫_ℂ := by
    apply integral_congr_ae
    filter_upwards [dilateFun_ae k hk u, dilateFun_ae k hk v] with ξ h1 h2
    rw [h1, h2, inner_smul_left, inner_smul_right]
    simp only [Complex.conj_ofReal]
    push_cast
    ring
  rw [h1, integral_const_mul, integral_comp_smul_frequency
    (fun ξ => ⟪u ξ, v ξ⟫_ℂ) k, abs_of_pos (by positivity)]
  have key : ∀ I : ℂ, ((k ^ 2 : ℝ) : ℂ) * (((k ^ 3)⁻¹ : ℝ) • I) = ((k⁻¹ : ℝ) : ℂ) * I := by
    intro I
    rw [Complex.real_smul]
    have hk0 : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
    push_cast
    field_simp
    ring
  exact key _

theorem dilateFun_norm_sq (k : ℝ) (hk : 0 < k) (u : VectorL2) :
    ‖dilateFun k hk u‖ ^ 2 = k⁻¹ * ‖u‖ ^ 2 := by
  have h := congrArg Complex.re (dilateFun_inner k hk u u)
  have e1 : (⟪dilateFun k hk u, dilateFun k hk u⟫_ℂ).re = ‖dilateFun k hk u‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (dilateFun k hk u))
  have e2 : (⟪u, u⟫_ℂ).re = ‖u‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using (inner_self_eq_norm_sq (𝕜 := ℂ) u)
  rw [e1] at h
  rw [h, Complex.re_ofReal_mul, e2]

theorem dilateFun_norm (k : ℝ) (hk : 0 < k) (u : VectorL2) :
    ‖dilateFun k hk u‖ = Real.sqrt k⁻¹ * ‖u‖ := by
  have h := dilateFun_norm_sq k hk u
  have h0 : 0 ≤ k⁻¹ := by positivity
  calc ‖dilateFun k hk u‖ = Real.sqrt (‖dilateFun k hk u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (k⁻¹ * ‖u‖ ^ 2) := by rw [h]
    _ = Real.sqrt k⁻¹ * Real.sqrt (‖u‖ ^ 2) := Real.sqrt_mul h0 _
    _ = Real.sqrt k⁻¹ * ‖u‖ := by rw [Real.sqrt_sq (norm_nonneg _)]

/-- The dilation `u ↦ k u(k ·)` for `k > 0` as a bounded operator. -/
def dilatePos (k : ℝ) (hk : 0 < k) : VectorL2 →L[ℂ] VectorL2 :=
  LinearMap.mkContinuous
    { toFun := dilateFun k hk
      map_add' := dilateFun_add k hk
      map_smul' := fun c u => dilateFun_smul k hk c u }
    (Real.sqrt k⁻¹) (fun u => (dilateFun_norm k hk u).le.trans (by rw [mul_comm]))

theorem dilatePos_apply (k : ℝ) (hk : 0 < k) (u : VectorL2) : dilatePos k hk u = dilateFun k hk u :=
  rfl

/-- The dilation `u ↦ k u(k ·)` as a bounded operator (the zero operator for `k ≤ 0`). -/
def dilate (k : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  if hk : 0 < k then dilatePos k hk else 0

theorem dilate_eq (k : ℝ) (hk : 0 < k) : dilate k = dilatePos k hk := dif_pos hk

theorem dilate_apply (k : ℝ) (hk : 0 < k) (u : VectorL2) : dilate k u = dilateFun k hk u := by
  rw [dilate_eq k hk]
  rfl

/-- **The characterizing lemma**: `(dilate k u) ξ = k • u (k ξ)` almost everywhere. -/
theorem dilate_ae (k : ℝ) (hk : 0 < k) (u : VectorL2) :
    dilate k u =ᵐ[volume] fun ξ : Frequency => (k : ℂ) • u (k • ξ) := by
  rw [dilate_apply k hk]
  exact dilateFun_ae k hk u

theorem dilate_inner (k : ℝ) (hk : 0 < k) (u v : VectorL2) :
    ⟪dilate k u, dilate k v⟫_ℂ = ((k⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  rw [dilate_apply k hk, dilate_apply k hk]
  exact dilateFun_inner k hk u v

theorem dilate_norm_sq (k : ℝ) (hk : 0 < k) (u : VectorL2) :
    ‖dilate k u‖ ^ 2 = k⁻¹ * ‖u‖ ^ 2 := by
  rw [dilate_apply k hk]
  exact dilateFun_norm_sq k hk u

theorem dilate_norm (k : ℝ) (hk : 0 < k) (u : VectorL2) :
    ‖dilate k u‖ = Real.sqrt k⁻¹ * ‖u‖ := by
  rw [dilate_apply k hk]
  exact dilateFun_norm k hk u

theorem dilate_one : dilate 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [dilate_ae 1 one_pos u] with ξ h
  rw [h]
  simp

theorem dilate_mul (k k' : ℝ) (hk : 0 < k) (hk' : 0 < k') (u : VectorL2) :
    dilate k (dilate k' u) = dilate (k * k') u := by
  apply Lp.ext
  have h := ae_smul_frequency k hk.ne' (dilate_ae k' hk' u)
  filter_upwards [dilate_ae k hk (dilate k' u), dilate_ae (k * k') (mul_pos hk hk') u, h] with ξ h1 h2 h3
  rw [h1, h2, h3]
  have e : k' • k • ξ = (k * k') • ξ := by rw [← mul_smul, mul_comm k' k]
  rw [e, smul_smul, Complex.ofReal_mul]

theorem dilate_comp_inv (k : ℝ) (hk : 0 < k) : dilate k ∘L dilate k⁻¹ = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  change dilate k (dilate k⁻¹ u) = u
  rw [dilate_mul k k⁻¹ hk (inv_pos.mpr hk), mul_inv_cancel₀ hk.ne', dilate_one]
  rfl

theorem dilate_inv_comp (k : ℝ) (hk : 0 < k) : dilate k⁻¹ ∘L dilate k = 1 := by
  have h := dilate_comp_inv k⁻¹ (inv_pos.mpr hk)
  rwa [inv_inv] at h

/-! ### Commutation with the square-root multiplier and the material source -/

theorem coordinateMap_smul' (k : ℝ) (y : Space) :
    VectorFourier.coordinateMap (k • y) = k • VectorFourier.coordinateMap y := rfl

theorem coordinateMap_symm_smul (k : ℝ) (ξ : Frequency) :
    VectorFourier.coordinateMap.symm (k • ξ) = k • VectorFourier.coordinateMap.symm ξ := rfl

theorem sqrtMultiplier_dilate (k : ℝ) (hk : 0 < k) (c : StaticCoefficient.Coefficient) (u : VectorL2) :
    StaticCoefficient.sqrtMultiplier (FrequencyScalingMaxwell.scaleCoeff k c) (dilate k u) =
      dilate k (StaticCoefficient.sqrtMultiplier c u) := by
  apply Lp.ext
  filter_upwards [StaticCoefficient.sqrtMultiplier_ae (FrequencyScalingMaxwell.scaleCoeff k c) (dilate k u),
    dilate_ae k hk u, dilate_ae k hk (StaticCoefficient.sqrtMultiplier c u),
    ae_smul_frequency k hk.ne' (StaticCoefficient.sqrtMultiplier_ae c u)] with ξ h1 h2 h3 h4
  rw [h1, h3, h4, h2]
  simp only [FrequencyScalingMaxwell.scaleCoeff_value]
  exact smul_comm _ _ _

theorem sqrtMultiplier_comp_dilate (k : ℝ) (hk : 0 < k) (c : StaticCoefficient.Coefficient) :
    StaticCoefficient.sqrtMultiplier (FrequencyScalingMaxwell.scaleCoeff k c) ∘L dilate k =
      dilate k ∘L StaticCoefficient.sqrtMultiplier c :=
  ContinuousLinearMap.ext fun u => sqrtMultiplier_dilate k hk c u

/-- **The material source under dilation**: `source (scaleCoeff k c) (dilate k u) j y = k * source c u j (k y)`
almost everywhere. -/
theorem source_dilate (k : ℝ) (hk : 0 < k) (c : StaticCoefficient.Coefficient) (u : VectorL2) (j : Fin 3) :
    ∀ᵐ y ∂(volume : Measure Space),
      DynamicVolume.source (FrequencyScalingMaxwell.scaleCoeff k c) (dilate k u) j y =
        (k : ℂ) * DynamicVolume.source c u j (k • y) := by
  filter_upwards [VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (dilate_ae k hk u)] with y hy
  unfold DynamicVolume.source
  rw [hy, coordinateMap_smul']
  simp only [FrequencyScalingMaxwell.scaleCoeff_value, Pi.smul_apply]
  change (Real.sqrt (c.value (k • VectorFourier.coordinateMap y)) : ℂ) *
      ((k : ℂ) * u (k • VectorFourier.coordinateMap y) j) =
    (k : ℂ) * ((Real.sqrt (c.value (k • VectorFourier.coordinateMap y)) : ℂ) *
      u (k • VectorFourier.coordinateMap y) j)
  ring

/-! ### The Fourier intertwining -/

/-- The Schwartz function `x ↦ k g (k x)`. -/
def dilS (k : ℝ) (hk : 0 < k) (g : 𝓢(Space, ℂ)) : 𝓢(Space, ℂ) :=
  (k : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ Space k hk.ne').toContinuousLinearEquiv g

theorem dilS_apply (k : ℝ) (hk : 0 < k) (g : 𝓢(Space, ℂ)) (x : Space) :
    dilS k hk g x = (k : ℂ) * g (k • x) := rfl

theorem fourier_apply_eq (g : 𝓢(Space, ℂ)) (η : Space) :
    𝓕 g η = ∫ x : Space, (𝐞 (-⟪x, η⟫_ℝ) : ℂ) • g x := rfl

/-- **Change of variables in the Fourier integral of a Schwartz function**:
`𝓕 [k g(k ·)] (η) = k⁻² 𝓕 g (k⁻¹ η)` for the Mathlib normalization `𝓕 g (η) = ∫ e^{-2πi⟨x,η⟩} g x dx`. -/
theorem fourier_dilS (k : ℝ) (hk : 0 < k) (g : 𝓢(Space, ℂ)) (η : Space) :
    𝓕 (dilS k hk g) η = (((k ^ 2)⁻¹ : ℝ) : ℂ) * 𝓕 g (k⁻¹ • η) := by
  have hk0 : k ≠ 0 := hk.ne'
  rw [fourier_apply_eq, fourier_apply_eq]
  set H : Space → ℂ := fun y => (𝐞 (-⟪k⁻¹ • y, η⟫_ℝ) : ℂ) • g y with hH
  have h1 : ∀ x : Space, (𝐞 (-⟪x, η⟫_ℝ) : ℂ) • dilS k hk g x = (k : ℂ) * H (k • x) := by
    intro x
    simp only [hH, dilS_apply, smul_smul, inv_smul_smul₀ hk0]
    simp only [smul_eq_mul]
    ring
  have h2 : ∀ y : Space, H y = (𝐞 (-⟪y, k⁻¹ • η⟫_ℝ) : ℂ) • g y := by
    intro y
    simp only [hH, real_inner_smul_left, real_inner_smul_right]
  simp_rw [h1, integral_const_mul, integral_comp_smul_space H k, abs_of_pos (by positivity : (0 : ℝ) < (k ^ 3)⁻¹)]
  simp_rw [h2]
  rw [Complex.real_smul]
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk0
  push_cast
  field_simp
  ring

theorem dilate_schwartzVector (k : ℝ) (hk : 0 < k) (f : Fin 3 → 𝓢(Space, ℂ)) :
    dilate k (VectorFourier.schwartzVector f) =
      VectorFourier.schwartzVector (fun i => dilS k hk (f i)) := by
  apply Lp.ext
  have hall : ∀ᵐ ξ ∂(volume : Measure Frequency), ∀ i : Fin 3,
      dilate k (VectorFourier.schwartzVector f) ξ i =
        VectorFourier.schwartzVector (fun i => dilS k hk (f i)) ξ i := by
    rw [ae_all_iff]
    intro i
    filter_upwards [dilate_ae k hk (VectorFourier.schwartzVector f),
      ae_smul_frequency k hk.ne' (VectorFourier.schwartzVector_ae f i),
      VectorFourier.schwartzVector_ae (fun i => dilS k hk (f i)) i] with ξ h1 h2 h3
    rw [h1, h3]
    simp only [PiLp.smul_apply, smul_eq_mul, h2, dilS_apply]
    rw [coordinateMap_symm_smul]
  filter_upwards [hall] with ξ h
  ext i
  exact h i

theorem fourier_dilate_schwartzVector (k : ℝ) (hk : 0 < k) (f : Fin 3 → 𝓢(Space, ℂ)) :
    VectorFourier.fourier (dilate k (VectorFourier.schwartzVector f)) =
      ((k⁻¹ : ℝ) : ℂ) • dilate k⁻¹ (VectorFourier.fourier (VectorFourier.schwartzVector f)) := by
  rw [dilate_schwartzVector k hk f]
  apply Lp.ext
  have hall : ∀ᵐ ξ ∂(volume : Measure Frequency), ∀ i : Fin 3,
      VectorFourier.fourier (VectorFourier.schwartzVector (fun i => dilS k hk (f i))) ξ i =
        (((k⁻¹ : ℝ) : ℂ) • dilate k⁻¹ (VectorFourier.fourier (VectorFourier.schwartzVector f))) ξ i := by
    rw [ae_all_iff]
    intro i
    have hki : 0 < k⁻¹ := inv_pos.mpr hk
    filter_upwards [VectorFourier.fourier_ae_integral (fun i => dilS k hk (f i)) i,
      Lp.coeFn_smul (((k⁻¹ : ℝ) : ℂ)) (dilate k⁻¹ (VectorFourier.fourier (VectorFourier.schwartzVector f))),
      dilate_ae k⁻¹ hki (VectorFourier.fourier (VectorFourier.schwartzVector f)),
      ae_smul_frequency k⁻¹ hki.ne' (VectorFourier.fourier_ae_integral f i)] with ξ h1 h2 h3 h4
    rw [h1, h2]
    simp only [Pi.smul_apply, h3, PiLp.smul_apply, smul_eq_mul, h4, fourier_dilS k hk, coordinateMap_symm_smul]
    push_cast
    ring
  filter_upwards [hall] with ξ h
  ext i
  exact h i

/-- **The Fourier intertwining of the dilation**: `fourier (dilate k u) = k⁻¹ • dilate k⁻¹ (fourier u)`. -/
theorem fourier_dilate (k : ℝ) (hk : 0 < k) (u : VectorL2) :
    VectorFourier.fourier (dilate k u) = ((k⁻¹ : ℝ) : ℂ) • dilate k⁻¹ (VectorFourier.fourier u) := by
  have hg1 : Continuous fun v : VectorL2 => VectorFourier.fourier (dilate k v) :=
    VectorFourier.fourier.continuous.comp (dilate k).continuous
  have hg2 : Continuous fun v : VectorL2 =>
      ((k⁻¹ : ℝ) : ℂ) • dilate k⁻¹ (VectorFourier.fourier v) :=
    ((dilate k⁻¹).continuous.comp VectorFourier.fourier.continuous).const_smul _
  have h := NewtonL2.schwartzVector_denseRange.equalizer hg1 hg2
    (funext fun f => fourier_dilate_schwartzVector k hk f)
  exact congrFun h u

theorem fourier_dilate_comp (k : ℝ) (hk : 0 < k) :
    VectorFourier.fourier.toContinuousLinearEquiv.toContinuousLinearMap ∘L dilate k =
      ((k⁻¹ : ℝ) : ℂ) • (dilate k⁻¹ ∘L VectorFourier.fourier.toContinuousLinearEquiv.toContinuousLinearMap) :=
  ContinuousLinearMap.ext fun u => fourier_dilate k hk u

/-! ### The longitudinal projection, the Newton operator and the static block commute with the dilation -/

theorem complexify_smul (k : ℝ) (ξ : Frequency) :
    LongitudinalProjection.complexify (k • ξ) = (k : ℂ) • LongitudinalProjection.complexify ξ := by
  ext i
  simp [LongitudinalProjection.complexify]

/-- The symbol is homogeneous of degree zero. -/
theorem symbol_smul (k : ℝ) (hk : 0 < k) (ξ : Frequency) :
    LongitudinalProjection.symbol (k • ξ) = LongitudinalProjection.symbol ξ := by
  apply ContinuousLinearMap.ext
  intro z
  rw [LongitudinalProjection.symbol_formula, LongitudinalProjection.symbol_formula, complexify_smul,
    inner_smul_left, norm_smul, smul_smul]
  have hn : ‖(k : ℂ)‖ = k := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  rw [hn]
  congr 1
  simp only [Complex.conj_ofReal]
  push_cast
  generalize ⟪LongitudinalProjection.complexify ξ, z⟫_ℂ = I
  generalize ((‖LongitudinalProjection.complexify ξ‖ : ℝ) : ℂ) = m
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  by_cases hm : m = 0
  · simp [hm]
  · field_simp
    ring

theorem multiplier_dilate (k : ℝ) (hk : 0 < k) (u : VectorL2) :
    LongitudinalProjection.multiplier (dilate k u) = dilate k (LongitudinalProjection.multiplier u) := by
  apply Lp.ext
  filter_upwards [LongitudinalProjection.multiplier_ae (dilate k u), dilate_ae k hk u,
    dilate_ae k hk (LongitudinalProjection.multiplier u),
    ae_smul_frequency k hk.ne' (LongitudinalProjection.multiplier_ae u)] with ξ h1 h2 h3 h4
  rw [h1, h3, h4, h2, symbol_smul k hk, map_smul]

theorem multiplier_comp_dilate (k : ℝ) (hk : 0 < k) :
    LongitudinalProjection.multiplier ∘L dilate k = dilate k ∘L LongitudinalProjection.multiplier :=
  ContinuousLinearMap.ext fun u => multiplier_dilate k hk u

theorem physicalProjection_dilate (k : ℝ) (hk : 0 < k) (u : VectorL2) :
    VectorFourier.physicalProjection (dilate k u) = dilate k (VectorFourier.physicalProjection u) := by
  apply VectorFourier.fourier.injective
  rw [VectorFourier.physicalProjection_intertwine, fourier_dilate k hk,
    fourier_dilate k hk, VectorFourier.physicalProjection_intertwine, map_smul,
    multiplier_dilate k⁻¹ (inv_pos.mpr hk)]

theorem physicalProjection_comp_dilate (k : ℝ) (hk : 0 < k) :
    VectorFourier.physicalProjection ∘L dilate k = dilate k ∘L VectorFourier.physicalProjection :=
  ContinuousLinearMap.ext fun u => physicalProjection_dilate k hk u

theorem newtonOperator_comp_dilate (k : ℝ) (hk : 0 < k) :
    NewtonL2.newtonOperator ∘L dilate k = dilate k ∘L NewtonL2.newtonOperator := by
  apply ContinuousLinearMap.ext
  intro u
  change -VectorFourier.physicalProjection (dilate k u) = dilate k (-VectorFourier.physicalProjection u)
  rw [physicalProjection_dilate k hk, map_neg]

theorem response_comp_dilate (k : ℝ) (hk : 0 < k) (c : StaticCoefficient.Coefficient) :
    StaticNewton.response (FrequencyScalingMaxwell.scaleCoeff k c) ∘L dilate k =
      dilate k ∘L StaticNewton.response c := by
  apply ContinuousLinearMap.ext
  intro u
  change NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier (FrequencyScalingMaxwell.scaleCoeff k c)
      (dilate k u)) = dilate k (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u))
  rw [sqrtMultiplier_dilate k hk]
  exact congrFun (congrArg DFunLike.coe (newtonOperator_comp_dilate k hk)) _

theorem volumeBlock_comp_dilate (k : ℝ) (hk : 0 < k) (c : StaticCoefficient.Coefficient) :
    StaticNewton.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) ∘L dilate k =
      dilate k ∘L StaticNewton.volumeBlock c := by
  apply ContinuousLinearMap.ext
  intro u
  change dilate k u - StaticCoefficient.sqrtMultiplier (FrequencyScalingMaxwell.scaleCoeff k c)
      (StaticNewton.response (FrequencyScalingMaxwell.scaleCoeff k c) (dilate k u)) =
    dilate k (u - StaticCoefficient.sqrtMultiplier c (StaticNewton.response c u))
  have h := congrFun (congrArg DFunLike.coe (response_comp_dilate k hk c)) u
  change StaticNewton.response (FrequencyScalingMaxwell.scaleCoeff k c) (dilate k u) =
    dilate k (StaticNewton.response c u) at h
  rw [h, sqrtMultiplier_dilate k hk, map_sub]

/-! ### The physical coordinate of a dilated field -/

/-- **The physical coordinate under dilation**:
`physicalCoordinate (dilate k F) i = k * physicalCoordinate F i (k ·)` almost everywhere. -/
theorem physicalCoordinate_dilate (k : ℝ) (hk : 0 < k) (F : VectorL2) (i : Fin 3) :
    NewtonL2.physicalCoordinate (dilate k F) i =ᵐ[volume]
      fun x : Space => (k : ℂ) * NewtonL2.physicalCoordinate F i (k • x) := by
  filter_upwards [NewtonL2.physicalCoordinate_ae (dilate k F) i,
    ae_smul_space k hk.ne' (NewtonL2.physicalCoordinate_ae F i),
    VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (dilate_ae k hk F)] with x h1 h2 h3
  rw [h1, h2, h3]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rfl

end OQ14.DilationL2

#print axioms OQ14.DilationL2.finrank_frequency
#print axioms OQ14.DilationL2.finrank_space
#print axioms OQ14.DilationL2.map_smul_frequency
#print axioms OQ14.DilationL2.smul_qmp_frequency
#print axioms OQ14.DilationL2.smul_qmp_space
#print axioms OQ14.DilationL2.ae_smul_frequency
#print axioms OQ14.DilationL2.ae_smul_space
#print axioms OQ14.DilationL2.integral_comp_smul_frequency
#print axioms OQ14.DilationL2.integral_comp_smul_space
#print axioms OQ14.DilationL2.memLp_dilate
#print axioms OQ14.DilationL2.dilateFun_ae
#print axioms OQ14.DilationL2.dilateFun_add
#print axioms OQ14.DilationL2.dilateFun_smul
#print axioms OQ14.DilationL2.dilateFun_inner
#print axioms OQ14.DilationL2.dilateFun_norm_sq
#print axioms OQ14.DilationL2.dilateFun_norm
#print axioms OQ14.DilationL2.dilatePos_apply
#print axioms OQ14.DilationL2.dilate_eq
#print axioms OQ14.DilationL2.dilate_apply
#print axioms OQ14.DilationL2.dilate_ae
#print axioms OQ14.DilationL2.dilate_inner
#print axioms OQ14.DilationL2.dilate_norm_sq
#print axioms OQ14.DilationL2.dilate_norm
#print axioms OQ14.DilationL2.dilate_one
#print axioms OQ14.DilationL2.dilate_mul
#print axioms OQ14.DilationL2.dilate_comp_inv
#print axioms OQ14.DilationL2.dilate_inv_comp
#print axioms OQ14.DilationL2.coordinateMap_smul'
#print axioms OQ14.DilationL2.coordinateMap_symm_smul
#print axioms OQ14.DilationL2.sqrtMultiplier_dilate
#print axioms OQ14.DilationL2.sqrtMultiplier_comp_dilate
#print axioms OQ14.DilationL2.source_dilate
#print axioms OQ14.DilationL2.dilS_apply
#print axioms OQ14.DilationL2.fourier_apply_eq
#print axioms OQ14.DilationL2.fourier_dilS
#print axioms OQ14.DilationL2.dilate_schwartzVector
#print axioms OQ14.DilationL2.fourier_dilate_schwartzVector
#print axioms OQ14.DilationL2.fourier_dilate
#print axioms OQ14.DilationL2.fourier_dilate_comp
#print axioms OQ14.DilationL2.complexify_smul
#print axioms OQ14.DilationL2.symbol_smul
#print axioms OQ14.DilationL2.multiplier_dilate
#print axioms OQ14.DilationL2.multiplier_comp_dilate
#print axioms OQ14.DilationL2.physicalProjection_dilate
#print axioms OQ14.DilationL2.physicalProjection_comp_dilate
#print axioms OQ14.DilationL2.newtonOperator_comp_dilate
#print axioms OQ14.DilationL2.response_comp_dilate
#print axioms OQ14.DilationL2.volumeBlock_comp_dilate
#print axioms OQ14.DilationL2.physicalCoordinate_dilate
