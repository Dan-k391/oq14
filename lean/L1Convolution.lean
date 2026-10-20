import NewtonL1L2

/-!
# Actual L1-kernel convolution on L2

The norm bound is derived from the ordinary Fourier integral. Its bounded L2
realization is identified with the literal convolution integral on every
integrable square-integrable source by test separation.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.L1Convolution

open MeasureTheory
open scoped SchwartzMap FourierTransform InnerProductSpace ComplexConjugate ContDiff

abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2

def mass (q : Space → ℂ) : ℝ := ∫ x, ‖q x‖

theorem mass_nonnegative (q : Space → ℂ) : 0 ≤ mass q :=
  integral_nonneg (fun x => norm_nonneg (q x))

theorem fourier_norm_le (q : Space → ℂ) (ξ : Space) : ‖𝓕 q ξ‖ ≤ mass q :=
  VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ Space) q ξ

theorem frequency_memLp (q : Space → ℂ) (hq : Integrable q) (F : ScalarL2) :
    MemLp (fun ξ => 𝓕 q ξ * F ξ) 2 (volume : Measure Space) := by
  apply (Lp.memLp F).of_le_mul
  · exact (NewtonL1L2.ordinary_fourier_continuous hq).aestronglyMeasurable.mul
      (Lp.memLp F).aestronglyMeasurable
  · filter_upwards with ξ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (fourier_norm_le q ξ) (norm_nonneg _)

def frequencyProduct (q : Space → ℂ) (hq : Integrable q) (F : ScalarL2) : ScalarL2 :=
  (frequency_memLp q hq F).toLp (fun ξ => 𝓕 q ξ * F ξ)

theorem frequencyProduct_ae (q : Space → ℂ) (hq : Integrable q) (F : ScalarL2) :
    frequencyProduct q hq F =ᵐ[volume] fun ξ => 𝓕 q ξ * F ξ :=
  (frequency_memLp q hq F).coeFn_toLp

theorem frequencyProduct_add (q : Space → ℂ) (hq : Integrable q) (F G : ScalarL2) :
    frequencyProduct q hq (F + G) = frequencyProduct q hq F + frequencyProduct q hq G := by
  apply Lp.ext
  filter_upwards [frequencyProduct_ae q hq (F + G), frequencyProduct_ae q hq F,
    frequencyProduct_ae q hq G, Lp.coeFn_add F G,
    Lp.coeFn_add (frequencyProduct q hq F) (frequencyProduct q hq G)] with ξ hfg hf hg ha hb
  rw [hfg, ha, hb]
  simp only [Pi.add_apply, hf, hg, mul_add]

theorem frequencyProduct_smul (q : Space → ℂ) (hq : Integrable q) (z : ℂ) (F : ScalarL2) :
    frequencyProduct q hq (z • F) = z • frequencyProduct q hq F := by
  apply Lp.ext
  filter_upwards [frequencyProduct_ae q hq (z • F), frequencyProduct_ae q hq F,
    Lp.coeFn_smul z F, Lp.coeFn_smul z (frequencyProduct q hq F)] with ξ hzf hf ha hb
  rw [hzf, ha, hb]
  simp only [Pi.smul_apply, hf, smul_eq_mul]
  ring

theorem frequencyProduct_norm (q : Space → ℂ) (hq : Integrable q) (F : ScalarL2) :
    ‖frequencyProduct q hq F‖ ≤ mass q * ‖F‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [frequencyProduct_ae q hq F] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_mul_of_nonneg_right (fourier_norm_le q ξ) (norm_nonneg _)

def frequencyLinear (q : Space → ℂ) (hq : Integrable q) : ScalarL2 →ₗ[ℂ] ScalarL2 where
  toFun := frequencyProduct q hq
  map_add' := frequencyProduct_add q hq
  map_smul' := frequencyProduct_smul q hq

def frequencyMultiplier (q : Space → ℂ) (hq : Integrable q) : ScalarL2 →L[ℂ] ScalarL2 :=
  (frequencyLinear q hq).mkContinuous (mass q) (frequencyProduct_norm q hq)

def operator (q : Space → ℂ) (hq : Integrable q) : ScalarL2 →L[ℂ] ScalarL2 :=
  FourierL2.fourierEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    frequencyMultiplier q hq ∘L
      FourierL2.fourierEquiv.toContinuousLinearEquiv.toContinuousLinearMap

theorem operator_fourier (q : Space → ℂ) (hq : Integrable q) (F : ScalarL2) :
    FourierL2.fourierEquiv (operator q hq F) =
      frequencyProduct q hq (FourierL2.fourierEquiv F) :=
  FourierL2.fourierEquiv.apply_symm_apply _

theorem operator_norm (q : Space → ℂ) (hq : Integrable q) (F : ScalarL2) :
    ‖operator q hq F‖ ≤ mass q * ‖F‖ := by
  rw [← FourierL2.fourierEquiv_norm, operator_fourier]
  exact (frequencyProduct_norm q hq _).trans_eq
    (by rw [FourierL2.fourierEquiv_norm])

theorem operator_norm_le (q : Space → ℂ) (hq : Integrable q) :
    ‖operator q hq‖ ≤ mass q :=
  ContinuousLinearMap.opNorm_le_bound _ (mass_nonnegative q) (operator_norm q hq)

theorem operator_pairing (q : Space → ℂ) (hq : Integrable q) (F : ScalarL2)
    (hF : Integrable (F : Space → ℂ)) (g : 𝓢(Space, ℂ)) :
    (∫ x, operator q hq F x * g x) =
      ∫ ξ, 𝓕 q ξ * 𝓕 (F : Space → ℂ) ξ *
        ((SchwartzMap.fourierTransformCLE ℂ).symm g) ξ := by
  rw [NewtonL2.scalar_bilinear_parseval, operator_fourier]
  apply integral_congr_ae
  filter_upwards [frequencyProduct_ae q hq (FourierL2.fourierEquiv F),
    NewtonL1L2.fourierEquiv_ae_integral F hF] with ξ hp hf
  rw [hp, hf]

theorem operator_spatial_pairing (q : Space → ℂ) (hq : Integrable q) (F : ScalarL2)
    (hF : Integrable (F : Space → ℂ)) (g : 𝓢(Space, ℂ)) :
    (∫ x, operator q hq F x * g x) =
      ∫ x, HeatFourier.convolution q F x * g x := by
  rw [operator_pairing q hq F hF]
  have h := FourierL2.fourier_mul_integral_flip (HeatFourier.convolution q F)
    ((SchwartzMap.fourierTransformCLE ℂ).symm g)
    (HeatFourier.convolution_integrable hq hF)
    ((SchwartzMap.fourierTransformCLE ℂ).symm g).integrable
  simp_rw [HeatFourier.fourier_convolution hq hF] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards with x
  have hi := congrArg (fun f : 𝓢(Space, ℂ) => f x)
    ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply g)
  change 𝓕 ((SchwartzMap.fourierTransformCLE ℂ).symm g) x = g x at hi
  rw [hi]

/-- The bounded L2 operator is represented by the genuine spatial convolution
for every actual L1-L2 source. -/
theorem operator_ae_convolution (q : Space → ℂ) (hq : Integrable q) (F : ScalarL2)
    (hF : Integrable (F : Space → ℂ)) :
    operator q hq F =ᵐ[volume] HeatFourier.convolution q F := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (operator q hq F)).locallyIntegrable
      (by norm_num : (1 : ENNReal) ≤ 2))
    (HeatFourier.convolution_integrable hq hF).locallyIntegrable
  intro φ hφ hc
  let ψ : 𝓢(Space, ℂ) := FourierL2.compactSmoothSchwartz (fun x => (φ x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hφ)
    (hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))
  have h := operator_spatial_pairing q hq F hF ψ
  change (∫ x, operator q hq F x * (φ x : ℂ)) =
    ∫ x, HeatFourier.convolution q F x * (φ x : ℂ) at h
  simpa only [Complex.real_smul, mul_comm] using h

theorem convolution_memLp (q : Space → ℂ) (hq : Integrable q) (F : ScalarL2)
    (hF : Integrable (F : Space → ℂ)) :
    MemLp (HeatFourier.convolution q F) 2 (volume : Measure Space) :=
  (memLp_congr_ae (operator_ae_convolution q hq F hF)).mp (Lp.memLp (operator q hq F))

theorem convolution_toLp_eq (q : Space → ℂ) (hq : Integrable q) (F : ScalarL2)
    (hF : Integrable (F : Space → ℂ)) :
    (convolution_memLp q hq F hF).toLp (HeatFourier.convolution q F) = operator q hq F := by
  apply Lp.ext
  exact (convolution_memLp q hq F hF).coeFn_toLp.trans
    (operator_ae_convolution q hq F hF).symm

/-- Young's L1-L2 bound for the literal spatial convolution. -/
theorem convolution_norm_bound (q : Space → ℂ) (hq : Integrable q) (F : ScalarL2)
    (hF : Integrable (F : Space → ℂ)) :
    ‖(convolution_memLp q hq F hF).toLp (HeatFourier.convolution q F)‖ ≤ mass q * ‖F‖ := by
  rw [convolution_toLp_eq q hq F hF]
  exact operator_norm q hq F

end OQ14.L1Convolution

#print axioms OQ14.L1Convolution.mass_nonnegative
#print axioms OQ14.L1Convolution.fourier_norm_le
#print axioms OQ14.L1Convolution.frequency_memLp
#print axioms OQ14.L1Convolution.frequencyProduct_ae
#print axioms OQ14.L1Convolution.frequencyProduct_add
#print axioms OQ14.L1Convolution.frequencyProduct_smul
#print axioms OQ14.L1Convolution.frequencyProduct_norm
#print axioms OQ14.L1Convolution.operator_fourier
#print axioms OQ14.L1Convolution.operator_norm
#print axioms OQ14.L1Convolution.operator_norm_le
#print axioms OQ14.L1Convolution.operator_pairing
#print axioms OQ14.L1Convolution.operator_spatial_pairing
#print axioms OQ14.L1Convolution.operator_ae_convolution
#print axioms OQ14.L1Convolution.convolution_memLp
#print axioms OQ14.L1Convolution.convolution_toLp_eq
#print axioms OQ14.L1Convolution.convolution_norm_bound
