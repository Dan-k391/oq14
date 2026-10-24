import DilationL2
import DilationKernels
import DynamicVolume
import MaterialField


/-!
# Operator-level transport of the dynamic volume block and of the solution map under dilation

For `k > 0` (and `R` real, `R ≥ 0` only where the frozen solution equation needs it):

* `kernel_scale`: `DynamicConvolution.kernel k (R / k) i j z = k ^ 3 * DynamicConvolution.kernel 1 R i j (k z)`
  at every point (the indicator of `closedBall 0 (R / k)` at `z` is that of `closedBall 0 R` at `k z`, and
  `DilationKernels.remainder_scale`);
* `fourier_dilated`: `𝓕 [k ^ 3 q(k ·)] (ξ) = 𝓕 q (k⁻¹ ξ)` for every function `q` (Bochner integral, the Jacobian `k⁻³`
  cancels `k ^ 3`), hence `fourier_kernel_scale`;
* `dilateS k : ScalarL2 →L[ℂ] ScalarL2`, `(dilateS k G) x = k * G (k x)` almost everywhere (`dilateS_ae`), compatible
  with the coordinate maps (`component_dilate`, `insert_dilateS`), with the Fourier intertwining
  `fourierEquiv (dilateS k G) = k⁻¹ • dilateS k⁻¹ (fourierEquiv G)` (`fourierEquiv_dilateS`);
* `l1_operator_dilate`: `L1Convolution.operator q' ∘ dilateS k = dilateS k ∘ operator q` whenever
  `𝓕 q' ξ = 𝓕 q (k⁻¹ ξ)`, in particular for the truncated kernels (`kernel_operator_dilate`);
* `operator_comp_dilate`: `DynamicConvolution.operator k (R / k) ∘L dilate k = dilate k ∘L DynamicConvolution.operator 1 R`;
* `weightedRemainder_comp_dilate`, `volumeBlock_comp_dilate` and `errorBound_scale`
  (`errorBound (scaleCoeff k c) k (R / k) = errorBound c 1 R`);
* `isUnit_conj_iff`, `ring_inverse_conj`, `volumeBlock_isUnit_iff`, `ringInverse_volumeBlock_comp_dilate` and
  `solution_dilate`: `MaterialField.solution (scaleCoeff k c) k (R / k) (dilate k f) = dilate k (MaterialField.solution c 1 R f)`
  for every `f`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.DilationVolume
open MeasureTheory Metric
open scoped InnerProductSpace ComplexConjugate FourierTransform

abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

/-! ### The truncated remainder kernel and its Fourier transform under dilation -/

theorem mem_closedBall_div_iff (k R : ℝ) (hk : 0 < k) (z : Space) :
    z ∈ closedBall (0 : Space) (R / k) ↔ k • z ∈ closedBall (0 : Space) R := by
  simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
  rw [le_div_iff₀ hk, mul_comm]

/-- **The truncated kernel under dilation**:
`kernel k (R / k) i j z = k ^ 3 * kernel 1 R i j (k z)` at every point. -/
theorem kernel_scale (k R : ℝ) (hk : 0 < k) (i j : Fin 3) (z : Space) :
    DynamicConvolution.kernel k (R / k) i j z =
      (k : ℂ) ^ 3 * DynamicConvolution.kernel 1 R i j (k • z) := by
  unfold DynamicConvolution.kernel
  by_cases hz : z ∈ closedBall (0 : Space) (R / k)
  · have hz' := (mem_closedBall_div_iff k R hk z).mp hz
    rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz']
    exact DilationKernels.remainder_scale k hk z i j
  · have hz' : k • z ∉ closedBall (0 : Space) R := fun h => hz ((mem_closedBall_div_iff k R hk z).mpr h)
    simp [hz, hz']

theorem kernel_scale_fun (k R : ℝ) (hk : 0 < k) (i j : Fin 3) :
    DynamicConvolution.kernel k (R / k) i j =
      fun z : Space => (k : ℂ) ^ 3 * DynamicConvolution.kernel 1 R i j (k • z) :=
  funext (kernel_scale k R hk i j)

theorem fourier_apply_eq' (f : Space → ℂ) (η : Space) :
    𝓕 f η = ∫ x : Space, (𝐞 (-⟪x, η⟫_ℝ) : ℂ) • f x := rfl

/-- **Fourier transform of a dilated kernel** (no integrability hypothesis, the Jacobian `k⁻³` cancels `k ^ 3`):
`𝓕 [k ^ 3 q(k ·)] (ξ) = 𝓕 q (k⁻¹ ξ)`. -/
theorem fourier_dilated (k : ℝ) (hk : 0 < k) (q : Space → ℂ) (ξ : Space) :
    𝓕 (fun z : Space => (k : ℂ) ^ 3 * q (k • z)) ξ = 𝓕 q (k⁻¹ • ξ) := by
  have hk0 : k ≠ 0 := hk.ne'
  rw [fourier_apply_eq', fourier_apply_eq']
  set H : Space → ℂ := fun y => (𝐞 (-⟪k⁻¹ • y, ξ⟫_ℝ) : ℂ) • q y with hH
  have h1 : ∀ x : Space, (𝐞 (-⟪x, ξ⟫_ℝ) : ℂ) • ((k : ℂ) ^ 3 * q (k • x)) = (k : ℂ) ^ 3 * H (k • x) := by
    intro x
    simp only [hH, smul_smul, inv_smul_smul₀ hk0]
    simp only [smul_eq_mul]
    ring
  have h2 : ∀ y : Space, H y = (𝐞 (-⟪y, k⁻¹ • ξ⟫_ℝ) : ℂ) • q y := by
    intro y
    simp only [hH, real_inner_smul_left, real_inner_smul_right]
  simp_rw [h1, integral_const_mul, DilationL2.integral_comp_smul_space H k,
    abs_of_pos (by positivity : (0 : ℝ) < (k ^ 3)⁻¹)]
  simp_rw [h2]
  rw [Complex.real_smul]
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk0
  push_cast
  field_simp

/-- The Fourier transform of the truncated kernel at frequency `k` and radius `R / k` is that of the unit-frequency
kernel of radius `R` at `k⁻¹ ξ`. -/
theorem fourier_kernel_scale (k R : ℝ) (hk : 0 < k) (i j : Fin 3) (ξ : Space) :
    𝓕 (DynamicConvolution.kernel k (R / k) i j) ξ = 𝓕 (DynamicConvolution.kernel 1 R i j) (k⁻¹ • ξ) := by
  rw [kernel_scale_fun k R hk i j]
  exact fourier_dilated k hk _ ξ


/-! ### The scalar dilation on the Euclidean `L²` -/

/-- The scalar dilation `G ↦ k G(k ·)` on `L²(ℝ³)` (the coordinate-0 component of the vector dilation of the
first-coordinate insertion). -/
def dilateS (k : ℝ) : ScalarL2 →L[ℂ] ScalarL2 :=
  DynamicConvolution.component 0 ∘L DilationL2.dilate k ∘L DynamicConvolution.insert 0

theorem dilateS_apply (k : ℝ) (G : ScalarL2) :
    dilateS k G = DynamicConvolution.component 0 (DilationL2.dilate k (DynamicConvolution.insert 0 G)) := rfl

/-- **The characterizing lemma of the scalar dilation**: `(dilateS k G) x = k * G (k x)` almost everywhere. -/
theorem dilateS_ae (k : ℝ) (hk : 0 < k) (G : ScalarL2) :
    dilateS k G =ᵐ[volume] fun x : Space => (k : ℂ) * G (k • x) := by
  have hG : DynamicConvolution.component 0 (DynamicConvolution.insert 0 G) = G := by
    rw [DynamicConvolution.component_insert]
    simp
  have e : (NewtonL2.physicalCoordinate (DynamicConvolution.insert 0 G) 0 : Space → ℂ) = G := by
    have h := congrArg (fun H : ScalarL2 => (H : Space → ℂ)) hG
    exact h
  filter_upwards [DilationL2.physicalCoordinate_dilate k hk (DynamicConvolution.insert 0 G) 0] with x h1
  rw [dilateS_apply]
  change NewtonL2.physicalCoordinate (DilationL2.dilate k (DynamicConvolution.insert 0 G)) 0 x = _
  rw [h1, e]

theorem component_ext (F F' : VectorL2)
    (h : ∀ j : Fin 3, DynamicConvolution.component j F = DynamicConvolution.component j F') : F = F' := by
  apply VectorFourier.components.injective
  apply PiLp.ext
  intro j
  rw [VectorFourier.components_coordinate, VectorFourier.components_coordinate]
  exact VectorFourier.scalarCoordinates.injective (h j)

theorem component_dilate (k : ℝ) (hk : 0 < k) (j : Fin 3) (F : VectorL2) :
    DynamicConvolution.component j (DilationL2.dilate k F) =
      dilateS k (DynamicConvolution.component j F) := by
  apply Lp.ext
  exact (DilationL2.physicalCoordinate_dilate k hk F j).trans (dilateS_ae k hk _).symm

theorem insert_dilateS (k : ℝ) (hk : 0 < k) (i : Fin 3) (G : ScalarL2) :
    DynamicConvolution.insert i (dilateS k G) = DilationL2.dilate k (DynamicConvolution.insert i G) := by
  apply component_ext
  intro j
  rw [component_dilate k hk, DynamicConvolution.component_insert, DynamicConvolution.component_insert]
  split_ifs
  · rfl
  · exact (map_zero (dilateS k)).symm

theorem dilateS_comp_component (k : ℝ) (hk : 0 < k) (j : Fin 3) :
    DynamicConvolution.component j ∘L DilationL2.dilate k =
      dilateS k ∘L DynamicConvolution.component j :=
  ContinuousLinearMap.ext fun F => component_dilate k hk j F

theorem dilateS_comp_insert (k : ℝ) (hk : 0 < k) (i : Fin 3) :
    DynamicConvolution.insert i ∘L dilateS k =
      DilationL2.dilate k ∘L DynamicConvolution.insert i :=
  ContinuousLinearMap.ext fun G => insert_dilateS k hk i G

theorem component_fourier (j : Fin 3) (F : VectorL2) :
    DynamicConvolution.component j (VectorFourier.fourier F) =
      FourierL2.fourierEquiv (DynamicConvolution.component j F) := by
  change VectorFourier.scalarCoordinates (VectorFourier.coordinate j (VectorFourier.fourier F)) = _
  rw [VectorFourier.fourier_coordinate]
  change VectorFourier.scalarCoordinates (VectorFourier.scalarCoordinates.symm
    (FourierL2.fourierEquiv (VectorFourier.scalarCoordinates (VectorFourier.coordinate j F)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- **The Fourier intertwining of the scalar dilation**:
`fourierEquiv (dilateS k G) = k⁻¹ • dilateS k⁻¹ (fourierEquiv G)`. -/
theorem fourierEquiv_dilateS (k : ℝ) (hk : 0 < k) (G : ScalarL2) :
    FourierL2.fourierEquiv (dilateS k G) =
      ((k⁻¹ : ℝ) : ℂ) • dilateS k⁻¹ (FourierL2.fourierEquiv G) := by
  have hG : DynamicConvolution.component 0 (DynamicConvolution.insert 0 G) = G := by
    rw [DynamicConvolution.component_insert]
    simp
  have hki : 0 < k⁻¹ := inv_pos.mpr hk
  set F : VectorL2 := DynamicConvolution.insert 0 G with hF
  calc FourierL2.fourierEquiv (dilateS k G)
      = FourierL2.fourierEquiv (dilateS k (DynamicConvolution.component 0 F)) := by rw [hG]
    _ = FourierL2.fourierEquiv (DynamicConvolution.component 0 (DilationL2.dilate k F)) := by
        rw [component_dilate k hk]
    _ = DynamicConvolution.component 0 (VectorFourier.fourier (DilationL2.dilate k F)) :=
        (component_fourier 0 _).symm
    _ = DynamicConvolution.component 0
          (((k⁻¹ : ℝ) : ℂ) • DilationL2.dilate k⁻¹ (VectorFourier.fourier F)) := by
        rw [DilationL2.fourier_dilate k hk]
    _ = ((k⁻¹ : ℝ) : ℂ) • dilateS k⁻¹ (DynamicConvolution.component 0 (VectorFourier.fourier F)) := by
        rw [map_smul, component_dilate k⁻¹ hki]
    _ = ((k⁻¹ : ℝ) : ℂ) • dilateS k⁻¹ (FourierL2.fourierEquiv G) := by
        rw [component_fourier, hG]


/-! ### The Young-convolution operator and the dynamic convolution under dilation -/

theorem frequencyProduct_dilate (k : ℝ) (hk : 0 < k) (q q' : Space → ℂ)
    (hq : Integrable q) (hq' : Integrable q')
    (hF : ∀ ξ : Space, 𝓕 q' ξ = 𝓕 q (k⁻¹ • ξ)) (H : ScalarL2) :
    L1Convolution.frequencyProduct q' hq' (((k⁻¹ : ℝ) : ℂ) • dilateS k⁻¹ H) =
      ((k⁻¹ : ℝ) : ℂ) • dilateS k⁻¹ (L1Convolution.frequencyProduct q hq H) := by
  have hki : 0 < k⁻¹ := inv_pos.mpr hk
  apply Lp.ext
  filter_upwards [L1Convolution.frequencyProduct_ae q' hq' (((k⁻¹ : ℝ) : ℂ) • dilateS k⁻¹ H),
    Lp.coeFn_smul (((k⁻¹ : ℝ) : ℂ)) (dilateS k⁻¹ H), dilateS_ae k⁻¹ hki H,
    Lp.coeFn_smul (((k⁻¹ : ℝ) : ℂ)) (dilateS k⁻¹ (L1Convolution.frequencyProduct q hq H)),
    dilateS_ae k⁻¹ hki (L1Convolution.frequencyProduct q hq H),
    DilationL2.ae_smul_space k⁻¹ hki.ne' (L1Convolution.frequencyProduct_ae q hq H)]
    with ξ h1 h2 h3 h4 h5 h6
  rw [h1, h4]
  simp only [Pi.smul_apply, smul_eq_mul] at h2 h4 ⊢
  rw [h2, h3, h5, h6, hF ξ]
  ring

/-- **The `L¹`-kernel convolution operator under dilation**: if `𝓕 q' ξ = 𝓕 q (k⁻¹ ξ)` (for instance
`q' z = k ^ 3 q (k z)`), then `operator q' ∘ dilateS k = dilateS k ∘ operator q`. -/
theorem l1_operator_dilate (k : ℝ) (hk : 0 < k) (q q' : Space → ℂ)
    (hq : Integrable q) (hq' : Integrable q')
    (hF : ∀ ξ : Space, 𝓕 q' ξ = 𝓕 q (k⁻¹ • ξ)) (G : ScalarL2) :
    L1Convolution.operator q' hq' (dilateS k G) = dilateS k (L1Convolution.operator q hq G) := by
  apply FourierL2.fourierEquiv.injective
  rw [L1Convolution.operator_fourier, fourierEquiv_dilateS k hk, fourierEquiv_dilateS k hk,
    L1Convolution.operator_fourier, frequencyProduct_dilate k hk q q' hq hq' hF]

theorem l1_operator_comp_dilate (k : ℝ) (hk : 0 < k) (q q' : Space → ℂ)
    (hq : Integrable q) (hq' : Integrable q')
    (hF : ∀ ξ : Space, 𝓕 q' ξ = 𝓕 q (k⁻¹ • ξ)) :
    L1Convolution.operator q' hq' ∘L dilateS k = dilateS k ∘L L1Convolution.operator q hq :=
  ContinuousLinearMap.ext fun G => l1_operator_dilate k hk q q' hq hq' hF G

/-- The kernel entries: `operator (kernel k (R / k) i j) ∘ dilateS k = dilateS k ∘ operator (kernel 1 R i j)`. -/
theorem kernel_operator_dilate (k R : ℝ) (hk : 0 < k) (i j : Fin 3) (G : ScalarL2) :
    L1Convolution.operator (DynamicConvolution.kernel k (R / k) i j)
        (DynamicConvolution.kernel_integrable k (R / k) i j) (dilateS k G) =
      dilateS k (L1Convolution.operator (DynamicConvolution.kernel 1 R i j)
        (DynamicConvolution.kernel_integrable 1 R i j) G) :=
  l1_operator_dilate k hk _ _ _ _ (fun ξ => fourier_kernel_scale k R hk i j ξ) G

theorem row_dilate (k R : ℝ) (hk : 0 < k) (i : Fin 3) (F : VectorL2) :
    DynamicConvolution.row k (R / k) i (DilationL2.dilate k F) =
      dilateS k (DynamicConvolution.row 1 R i F) := by
  simp only [DynamicConvolution.row, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [component_dilate k hk j F, kernel_operator_dilate k R hk i j]

/-- **The dynamic convolution under dilation**:
`DynamicConvolution.operator k (R / k) ∘L dilate k = dilate k ∘L DynamicConvolution.operator 1 R`. -/
theorem operator_dilate (k R : ℝ) (hk : 0 < k) (F : VectorL2) :
    DynamicConvolution.operator k (R / k) (DilationL2.dilate k F) =
      DilationL2.dilate k (DynamicConvolution.operator 1 R F) := by
  simp only [DynamicConvolution.operator, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [row_dilate k R hk i F, insert_dilateS k hk i]

theorem operator_comp_dilate (k R : ℝ) (hk : 0 < k) :
    DynamicConvolution.operator k (R / k) ∘L DilationL2.dilate k =
      DilationL2.dilate k ∘L DynamicConvolution.operator 1 R :=
  ContinuousLinearMap.ext fun F => operator_dilate k R hk F

/-! ### The weighted remainder, the volume block and the error bound -/

theorem weightedRemainder_comp_dilate (k R : ℝ) (hk : 0 < k) (c : Coefficient) :
    DynamicVolume.weightedRemainder (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k) ∘L DilationL2.dilate k =
      DilationL2.dilate k ∘L DynamicVolume.weightedRemainder c 1 R := by
  apply ContinuousLinearMap.ext
  intro u
  change StaticCoefficient.sqrtMultiplier (FrequencyScalingMaxwell.scaleCoeff k c)
      (DynamicConvolution.operator k (2 * (R / k))
        (StaticCoefficient.sqrtMultiplier (FrequencyScalingMaxwell.scaleCoeff k c) (DilationL2.dilate k u))) =
    DilationL2.dilate k (StaticCoefficient.sqrtMultiplier c
      (DynamicConvolution.operator 1 (2 * R) (StaticCoefficient.sqrtMultiplier c u)))
  have h2 : 2 * (R / k) = (2 * R) / k := by ring
  rw [h2, DilationL2.sqrtMultiplier_dilate k hk, operator_dilate k (2 * R) hk,
    DilationL2.sqrtMultiplier_dilate k hk]

theorem volumeBlock_comp_dilate (k R : ℝ) (hk : 0 < k) (c : Coefficient) :
    DynamicVolume.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k) ∘L DilationL2.dilate k =
      DilationL2.dilate k ∘L DynamicVolume.volumeBlock c 1 R := by
  apply ContinuousLinearMap.ext
  intro u
  have h1 := congrFun (congrArg DFunLike.coe (DilationL2.volumeBlock_comp_dilate k hk c)) u
  have h2 := congrFun (congrArg DFunLike.coe (weightedRemainder_comp_dilate k R hk c)) u
  change StaticNewton.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) (DilationL2.dilate k u) =
    DilationL2.dilate k (StaticNewton.volumeBlock c u) at h1
  change DynamicVolume.weightedRemainder (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k)
      (DilationL2.dilate k u) = DilationL2.dilate k (DynamicVolume.weightedRemainder c 1 R u) at h2
  change StaticNewton.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) (DilationL2.dilate k u) -
      DynamicVolume.weightedRemainder (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k)
        (DilationL2.dilate k u) =
    DilationL2.dilate k (StaticNewton.volumeBlock c u - DynamicVolume.weightedRemainder c 1 R u)
  rw [h1, h2, map_sub]

theorem entryMass_scale (k R : ℝ) (hk : 0 < k) :
    DynamicConvolution.entryMass k (2 * (R / k)) = DynamicConvolution.entryMass 1 (2 * R) := by
  have hk0 : k ≠ 0 := hk.ne'
  unfold DynamicConvolution.entryMass
  field_simp
  ring

/-- **The error bound is dilation invariant**: `errorBound (scaleCoeff k c) k (R / k) = errorBound c 1 R`. -/
theorem errorBound_scale (k R : ℝ) (hk : 0 < k) (c : Coefficient) :
    DynamicVolume.errorBound (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k) =
      DynamicVolume.errorBound c 1 R := by
  unfold DynamicVolume.errorBound
  rw [entryMass_scale k R hk]
  rfl


/-! ### Transport of invertibility and of the solution map -/

/-- Conjugation by an invertible element preserves invertibility. -/
theorem isUnit_conj_iff {M : Type*} [Monoid M] (D E B : M) (hDE : D * E = 1) (hED : E * D = 1) :
    IsUnit (D * B * E) ↔ IsUnit B := by
  have hD : IsUnit D := ⟨⟨D, E, hDE, hED⟩, rfl⟩
  have hE : IsUnit E := ⟨⟨E, D, hED, hDE⟩, rfl⟩
  constructor
  · intro h
    have e : B = E * (D * B * E) * D := by
      calc B = (E * D) * B * (E * D) := by rw [hED, one_mul, mul_one]
        _ = E * (D * B * E) * D := by simp only [mul_assoc]
    rw [e]
    exact (hE.mul h).mul hD
  · intro h
    exact (hD.mul h).mul hE

/-- **The helper**: `Ring.inverse (D * B * E) = D * Ring.inverse B * E` when `D E = E D = 1`. -/
theorem ring_inverse_conj {M : Type*} [MonoidWithZero M] (D E B : M) (hDE : D * E = 1) (hED : E * D = 1) :
    Ring.inverse (D * B * E) = D * Ring.inverse B * E := by
  by_cases hB : IsUnit B
  · obtain ⟨u, rfl⟩ := hB
    let w : Mˣ := ⟨D * (u : M) * E, D * ((u⁻¹ : Mˣ) : M) * E, by
      calc D * (u : M) * E * (D * ((u⁻¹ : Mˣ) : M) * E)
          = D * (u : M) * (E * D) * ((u⁻¹ : Mˣ) : M) * E := by simp only [mul_assoc]
        _ = 1 := by rw [hED, mul_one, mul_assoc D, Units.mul_inv, mul_one, hDE], by
      calc D * ((u⁻¹ : Mˣ) : M) * E * (D * (u : M) * E)
          = D * ((u⁻¹ : Mˣ) : M) * (E * D) * (u : M) * E := by simp only [mul_assoc]
        _ = 1 := by rw [hED, mul_one, mul_assoc D, Units.inv_mul, mul_one, hDE]⟩
    have hw : D * (u : M) * E = (w : M) := rfl
    rw [hw, Ring.inverse_unit, Ring.inverse_unit]
    rfl
  · have hB' : ¬ IsUnit (D * B * E) := fun h => hB ((isUnit_conj_iff D E B hDE hED).mp h)
    rw [Ring.inverse_non_unit _ hB, Ring.inverse_non_unit _ hB']
    simp

/-- The dynamic volume block of the dilated coefficient is the conjugate by `dilate k` of the unit-frequency block. -/
theorem volumeBlock_eq_conj (k R : ℝ) (hk : 0 < k) (c : Coefficient) :
    DynamicVolume.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k) =
      DilationL2.dilate k * DynamicVolume.volumeBlock c 1 R * DilationL2.dilate k⁻¹ := by
  have h : DynamicVolume.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k) *
      DilationL2.dilate k = DilationL2.dilate k * DynamicVolume.volumeBlock c 1 R :=
    volumeBlock_comp_dilate k R hk c
  have hDE : DilationL2.dilate k * DilationL2.dilate k⁻¹ = 1 := DilationL2.dilate_comp_inv k hk
  calc DynamicVolume.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k)
      = DynamicVolume.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k) *
          (DilationL2.dilate k * DilationL2.dilate k⁻¹) := by rw [hDE, mul_one]
    _ = (DynamicVolume.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k) *
          DilationL2.dilate k) * DilationL2.dilate k⁻¹ := by rw [mul_assoc]
    _ = _ := by rw [h]

/-- **Unit transport**: the dilated dynamic volume block is invertible exactly when the unit-frequency block is. -/
theorem volumeBlock_isUnit_iff (k R : ℝ) (hk : 0 < k) (c : Coefficient) :
    IsUnit (DynamicVolume.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k)) ↔
      IsUnit (DynamicVolume.volumeBlock c 1 R) := by
  rw [volumeBlock_eq_conj k R hk c]
  exact isUnit_conj_iff _ _ _ (DilationL2.dilate_comp_inv k hk) (DilationL2.dilate_inv_comp k hk)

/-- The inverse of the dilated block (zero when it is not a unit) is the conjugate of the unit-frequency inverse. -/
theorem ringInverse_volumeBlock_scale (k R : ℝ) (hk : 0 < k) (c : Coefficient) :
    Ring.inverse (DynamicVolume.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k)) =
      DilationL2.dilate k * Ring.inverse (DynamicVolume.volumeBlock c 1 R) * DilationL2.dilate k⁻¹ := by
  rw [volumeBlock_eq_conj k R hk c]
  exact ring_inverse_conj _ _ _ (DilationL2.dilate_comp_inv k hk) (DilationL2.dilate_inv_comp k hk)

theorem ringInverse_volumeBlock_comp_dilate (k R : ℝ) (hk : 0 < k) (c : Coefficient) :
    Ring.inverse (DynamicVolume.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k)) ∘L
        DilationL2.dilate k =
      DilationL2.dilate k ∘L Ring.inverse (DynamicVolume.volumeBlock c 1 R) := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ringInverse_volumeBlock_scale k R hk c]
  change DilationL2.dilate k (Ring.inverse (DynamicVolume.volumeBlock c 1 R)
    (DilationL2.dilate k⁻¹ (DilationL2.dilate k f))) = _
  have h := congrFun (congrArg DFunLike.coe (DilationL2.dilate_inv_comp k hk)) f
  change DilationL2.dilate k⁻¹ (DilationL2.dilate k f) = f at h
  rw [h]
  rfl

/-- **The solution map under dilation**: `solution (scaleCoeff k c) k (R / k) (dilate k f) = dilate k (solution c 1 R f)`
for every `f`, with no smallness hypothesis. -/
theorem solution_dilate (k R : ℝ) (hk : 0 < k) (c : Coefficient) (f : VectorL2) :
    MaterialField.solution (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k) (DilationL2.dilate k f) =
      DilationL2.dilate k (MaterialField.solution c 1 R f) := by
  unfold MaterialField.solution
  exact congrFun (congrArg DFunLike.coe (ringInverse_volumeBlock_comp_dilate k R hk c)) f

/-- The smallness hypothesis is the same for the dilated and the unit-frequency problem. -/
theorem errorBound_lt_iff (k R : ℝ) (hk : 0 < k) (c : Coefficient) :
    DynamicVolume.errorBound (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k) < 1 ↔
      DynamicVolume.errorBound c 1 R < 1 := by
  rw [errorBound_scale k R hk c]

/-- Under the dilated small-volume hypothesis the dilated solution equation holds for `dilate k f`
(a consequence of the unit-frequency equation and the dilation intertwining). -/
theorem solution_equation_dilate (k R : ℝ) (hk : 0 < k) (hR : 0 ≤ R) (c : Coefficient)
    (hsmall : DynamicVolume.errorBound c 1 R < 1) (f : VectorL2) :
    DynamicVolume.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k)
      (MaterialField.solution (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k) (DilationL2.dilate k f)) =
      DilationL2.dilate k f := by
  rw [solution_dilate k R hk c f]
  have h := congrFun (congrArg DFunLike.coe (volumeBlock_comp_dilate k R hk c))
    (MaterialField.solution c 1 R f)
  change DynamicVolume.volumeBlock (FrequencyScalingMaxwell.scaleCoeff k c) k (R / k)
      (DilationL2.dilate k (MaterialField.solution c 1 R f)) =
    DilationL2.dilate k (DynamicVolume.volumeBlock c 1 R (MaterialField.solution c 1 R f)) at h
  rw [h, MaterialField.solution_equation c 1 R hR hsmall f]

end OQ14.DilationVolume

#print axioms OQ14.DilationVolume.mem_closedBall_div_iff
#print axioms OQ14.DilationVolume.kernel_scale
#print axioms OQ14.DilationVolume.kernel_scale_fun
#print axioms OQ14.DilationVolume.fourier_apply_eq'
#print axioms OQ14.DilationVolume.fourier_dilated
#print axioms OQ14.DilationVolume.fourier_kernel_scale
#print axioms OQ14.DilationVolume.dilateS_apply
#print axioms OQ14.DilationVolume.dilateS_ae
#print axioms OQ14.DilationVolume.component_ext
#print axioms OQ14.DilationVolume.component_dilate
#print axioms OQ14.DilationVolume.insert_dilateS
#print axioms OQ14.DilationVolume.dilateS_comp_component
#print axioms OQ14.DilationVolume.dilateS_comp_insert
#print axioms OQ14.DilationVolume.component_fourier
#print axioms OQ14.DilationVolume.fourierEquiv_dilateS
#print axioms OQ14.DilationVolume.frequencyProduct_dilate
#print axioms OQ14.DilationVolume.l1_operator_dilate
#print axioms OQ14.DilationVolume.l1_operator_comp_dilate
#print axioms OQ14.DilationVolume.kernel_operator_dilate
#print axioms OQ14.DilationVolume.row_dilate
#print axioms OQ14.DilationVolume.operator_dilate
#print axioms OQ14.DilationVolume.operator_comp_dilate
#print axioms OQ14.DilationVolume.weightedRemainder_comp_dilate
#print axioms OQ14.DilationVolume.volumeBlock_comp_dilate
#print axioms OQ14.DilationVolume.entryMass_scale
#print axioms OQ14.DilationVolume.errorBound_scale
#print axioms OQ14.DilationVolume.isUnit_conj_iff
#print axioms OQ14.DilationVolume.ring_inverse_conj
#print axioms OQ14.DilationVolume.volumeBlock_eq_conj
#print axioms OQ14.DilationVolume.volumeBlock_isUnit_iff
#print axioms OQ14.DilationVolume.ringInverse_volumeBlock_scale
#print axioms OQ14.DilationVolume.ringInverse_volumeBlock_comp_dilate
#print axioms OQ14.DilationVolume.solution_dilate
#print axioms OQ14.DilationVolume.errorBound_lt_iff
#print axioms OQ14.DilationVolume.solution_equation_dilate
