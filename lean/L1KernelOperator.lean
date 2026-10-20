import L1Convolution
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
Actual integrable scalar kernels act complex-linearly and continuously in
bounded L2 operator norm. The construction agrees with the existing literal
convolution realization. A ball cutoff transfers global L2 kernels to L1.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace OQ14.L1KernelOperator
open MeasureTheory Metric
open scoped FourierTransform
abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2
abbrev KernelL1 := Lp ℂ 1 (volume : Measure Space)
abbrev Operator := ScalarL2 →L[ℂ] ScalarL2

theorem fourier_congr_ae (q r : Space → ℂ) (he : q =ᵐ[volume] r) (ξ : Space) :
    𝓕 q ξ = 𝓕 r ξ := by
  rw [HeatFourier.fourier_as_modulate, HeatFourier.fourier_as_modulate]
  apply integral_congr_ae
  filter_upwards [he] with x hx
  simp only [HeatFourier.modulate, hx]

theorem operator_congr (q r : Space → ℂ) (hq : Integrable q) (hr : Integrable r)
    (he : q =ᵐ[volume] r) : L1Convolution.operator q hq = L1Convolution.operator r hr := by
  apply ContinuousLinearMap.ext
  intro F
  apply FourierL2.fourierEquiv.injective
  rw [L1Convolution.operator_fourier, L1Convolution.operator_fourier]
  apply Lp.ext
  filter_upwards [L1Convolution.frequencyProduct_ae q hq (FourierL2.fourierEquiv F),
    L1Convolution.frequencyProduct_ae r hr (FourierL2.fourierEquiv F)] with ξ hqξ hrξ
  rw [hqξ, hrξ, fourier_congr_ae q r he ξ]

theorem fourier_add (q r : Space → ℂ) (hq : Integrable q) (hr : Integrable r) (ξ : Space) :
    𝓕 (q+r) ξ = 𝓕 q ξ + 𝓕 r ξ := by
  simp only [HeatFourier.fourier_as_modulate]
  have hf : HeatFourier.modulate ξ (q+r) =
      HeatFourier.modulate ξ q + HeatFourier.modulate ξ r := by
    funext x
    simp only [HeatFourier.modulate, Pi.add_apply, mul_add]
  rw [hf]
  simp only [Pi.add_apply]
  exact integral_add (HeatFourier.modulate_integrable ξ hq)
    (HeatFourier.modulate_integrable ξ hr)

theorem fourier_smul (q : Space → ℂ) (z : ℂ) (ξ : Space) :
    𝓕 (z • q) ξ = z * 𝓕 q ξ := by
  simp only [HeatFourier.fourier_as_modulate]
  have hf : HeatFourier.modulate ξ (z • q) =
      fun x => z * HeatFourier.modulate ξ q x := by
    funext x
    simp only [HeatFourier.modulate, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hf, integral_const_mul]

theorem operator_add (q r : Space → ℂ) (hq : Integrable q) (hr : Integrable r) :
    L1Convolution.operator (q+r) (hq.add hr) =
      L1Convolution.operator q hq + L1Convolution.operator r hr := by
  apply ContinuousLinearMap.ext
  intro F
  apply FourierL2.fourierEquiv.injective
  simp only [ContinuousLinearMap.add_apply, map_add, L1Convolution.operator_fourier]
  apply Lp.ext
  filter_upwards [L1Convolution.frequencyProduct_ae (q+r) (hq.add hr) (FourierL2.fourierEquiv F),
    L1Convolution.frequencyProduct_ae q hq (FourierL2.fourierEquiv F),
    L1Convolution.frequencyProduct_ae r hr (FourierL2.fourierEquiv F),
    Lp.coeFn_add (L1Convolution.frequencyProduct q hq (FourierL2.fourierEquiv F))
      (L1Convolution.frequencyProduct r hr (FourierL2.fourierEquiv F))] with ξ hqr hqξ hrξ ha
  rw [hqr, ha]
  simp only [Pi.add_apply, hqξ, hrξ, fourier_add q r hq hr ξ, add_mul]

theorem operator_smul (q : Space → ℂ) (hq : Integrable q) (z : ℂ) :
    L1Convolution.operator (z • q) (hq.smul z) = z • L1Convolution.operator q hq := by
  apply ContinuousLinearMap.ext
  intro F
  apply FourierL2.fourierEquiv.injective
  simp only [ContinuousLinearMap.smul_apply, map_smul, L1Convolution.operator_fourier]
  apply Lp.ext
  filter_upwards [L1Convolution.frequencyProduct_ae (z • q) (hq.smul z)
    (FourierL2.fourierEquiv F),
    L1Convolution.frequencyProduct_ae q hq (FourierL2.fourierEquiv F),
    Lp.coeFn_smul z (L1Convolution.frequencyProduct q hq (FourierL2.fourierEquiv F))]
    with ξ hz hqξ hs
  rw [hz, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hqξ, fourier_smul, mul_assoc]

def value (q : KernelL1) : Operator :=
  L1Convolution.operator q (L1.integrable_coeFn q)

theorem value_add (q r : KernelL1) : value (q+r) = value q + value r := by
  have h := operator_congr ((q+r : KernelL1) : Space → ℂ)
    ((q : Space → ℂ) + (r : Space → ℂ))
    (L1.integrable_coeFn (q+r)) ((L1.integrable_coeFn q).add (L1.integrable_coeFn r))
    (Lp.coeFn_add q r)
  exact h.trans (operator_add q r (L1.integrable_coeFn q) (L1.integrable_coeFn r))

theorem value_smul (q : KernelL1) (z : ℂ) : value (z • q) = z • value q := by
  have h := operator_congr ((z • q : KernelL1) : Space → ℂ) (z • (q : Space → ℂ))
    (L1.integrable_coeFn (z • q)) ((L1.integrable_coeFn q).smul z)
    (Lp.coeFn_smul z q)
  exact h.trans (operator_smul q (L1.integrable_coeFn q) z)
theorem mass_eq_norm (q : KernelL1) : L1Convolution.mass q = ‖q‖ := by
  rw [L1Convolution.mass, integral_norm_eq_lintegral_enorm (Lp.memLp q).aestronglyMeasurable,
    L1.norm_def]

theorem value_norm (q : KernelL1) : ‖value q‖ ≤ ‖q‖ := by
  exact (L1Convolution.operator_norm_le q (L1.integrable_coeFn q)).trans_eq (mass_eq_norm q)

def linear : KernelL1 →ₗ[ℂ] Operator where
  toFun := value
  map_add' := value_add
  map_smul' := fun z q => value_smul q z

def operator : KernelL1 →L[ℂ] Operator :=
  linear.mkContinuous 1 (fun q => by simpa only [one_mul] using value_norm q)

theorem operator_apply (q : KernelL1) :
    operator q = L1Convolution.operator q (L1.integrable_coeFn q) := rfl

theorem operator_norm_le : ‖operator‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun q => by
    simpa only [one_mul] using value_norm q)

theorem operator_toL1 (q : Space → ℂ) (hq : Integrable q) :
    operator (hq.toL1 q) = L1Convolution.operator q hq :=
  operator_congr (hq.toL1 q) q (L1.integrable_coeFn (hq.toL1 q)) hq hq.coeFn_toL1

theorem operator_spatial_ae (q : Space → ℂ) (hq : Integrable q)
    (F : ScalarL2) (hF : Integrable (F : Space → ℂ)) :
    operator (hq.toL1 q) F =ᵐ[volume] HeatFourier.convolution q F := by
  rw [operator_toL1 q hq]
  exact L1Convolution.operator_ae_convolution q hq F hF

def ballIndicator (R : ℝ) : ScalarL2 :=
  indicatorConstLp 2 measurableSet_closedBall
    (isCompact_closedBall (0 : Space) R).measure_ne_top (1 : ℂ)

theorem ballIndicator_ae (R : ℝ) :
    ballIndicator R =ᵐ[volume] (closedBall (0 : Space) R).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

def ballCutoff (R : ℝ) : ScalarL2 →L[ℂ] KernelL1 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume 2 2 1 (ballIndicator R)

theorem ballCutoff_ae (R : ℝ) (F : ScalarL2) :
    ballCutoff R F =ᵐ[volume] (closedBall (0 : Space) R).indicator (F : Space → ℂ) := by
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 1) (ballIndicator R) F
  filter_upwards [hm, ballIndicator_ae R] with x hx hi
  change ballCutoff R F x = _
  rw [show ballCutoff R F x = ballIndicator R x * F x from hx, hi]
  by_cases hb : x ∈ closedBall (0 : Space) R <;> simp [hb]

theorem ballCutoff_toL1 (R : ℝ) (F : ScalarL2) (q : Space → ℂ) (hq : Integrable q)
    (hF : (F : Space → ℂ) =ᵐ[volume] q)
    (hc : ∀ x, x ∉ closedBall 0 R → q x = 0) :
    ballCutoff R F = hq.toL1 q := by
  apply Lp.ext
  filter_upwards [ballCutoff_ae R F, hF, hq.coeFn_toL1] with x hx hf hq'
  rw [hx, hq']
  by_cases hb : x ∈ closedBall (0 : Space) R
  · simp only [Set.indicator_of_mem hb, hf]
  · simp only [Set.indicator_of_not_mem hb, hc x hb]

def localOperator (R : ℝ) : ScalarL2 →L[ℂ] Operator := operator ∘L ballCutoff R

theorem localOperator_toL1 (R : ℝ) (F : ScalarL2) (q : Space → ℂ) (hq : Integrable q)
    (hF : (F : Space → ℂ) =ᵐ[volume] q)
    (hc : ∀ x, x ∉ closedBall 0 R → q x = 0) :
    localOperator R F = L1Convolution.operator q hq := by
  change operator (ballCutoff R F) = _
  rw [ballCutoff_toL1 R F q hq hF hc, operator_toL1 q hq]

end OQ14.L1KernelOperator



#print axioms OQ14.L1KernelOperator.fourier_congr_ae
#print axioms OQ14.L1KernelOperator.operator_congr
#print axioms OQ14.L1KernelOperator.fourier_add
#print axioms OQ14.L1KernelOperator.fourier_smul
#print axioms OQ14.L1KernelOperator.operator_add
#print axioms OQ14.L1KernelOperator.operator_smul
#print axioms OQ14.L1KernelOperator.value_add
#print axioms OQ14.L1KernelOperator.value_smul
#print axioms OQ14.L1KernelOperator.mass_eq_norm
#print axioms OQ14.L1KernelOperator.value_norm
#print axioms OQ14.L1KernelOperator.operator_apply
#print axioms OQ14.L1KernelOperator.operator_norm_le
#print axioms OQ14.L1KernelOperator.operator_toL1
#print axioms OQ14.L1KernelOperator.operator_spatial_ae
#print axioms OQ14.L1KernelOperator.ballIndicator_ae
#print axioms OQ14.L1KernelOperator.ballCutoff_ae
#print axioms OQ14.L1KernelOperator.ballCutoff_toL1
#print axioms OQ14.L1KernelOperator.localOperator_toL1
