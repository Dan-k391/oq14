import L1Convolution
import KernelConvolution

/-! # Actual local L2 convolution by a locally integrable kernel

A compact source permits an exact finite-radius cutoff on each observation
ball. The previously constructed L1 convolution operator then proves local
L2 regularity of the literal spatial integral.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.LocalConvolution

open MeasureTheory Metric

abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2

def kernel (q : Space → ℂ) (T : ℝ) : Space → ℂ :=
  (closedBall 0 T).indicator q

theorem kernel_integrable (q : Space → ℂ) (hq : LocallyIntegrable q volume) (T : ℝ) :
    Integrable (kernel q T) :=
  (integrable_indicator_iff measurableSet_closedBall).mpr
    (hq.integrableOn_isCompact (isCompact_closedBall 0 T))

def operator (q : Space → ℂ) (hq : LocallyIntegrable q volume) (T : ℝ) :
    ScalarL2 →L[ℂ] ScalarL2 :=
  L1Convolution.operator (kernel q T) (kernel_integrable q hq T)

theorem kernel_source_eq (q ρ : Space → ℂ) (R S : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0)
    (x y : Space) (hx : x ∈ closedBall 0 R) :
    ρ y * kernel q (R+S) (x-y) = ρ y * q (x-y) := by
  by_cases hy : y ∈ closedBall (0 : Space) S
  · have hxy : x-y ∈ closedBall (0 : Space) (R+S) := by
      simp only [mem_closedBall, dist_zero_right] at hx hy ⊢
      exact (norm_sub_le _ _).trans (add_le_add hx hy)
    simp [kernel, hxy]
  · simp [hc y hy]

theorem operator_ae_on_ball (q : Space → ℂ) (hq : LocallyIntegrable q volume)
    (ρ : Space → ℂ) (hρ : Integrable ρ volume) (F : ScalarL2)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ) (R S : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0) :
    ∀ᵐ x ∂(volume : Measure Space), x ∈ closedBall 0 R →
      operator q hq (R+S) F x = KernelConvolution.response q ρ x := by
  have h := L1Convolution.operator_ae_convolution (kernel q (R+S))
    (kernel_integrable q hq (R+S)) F (hρ.congr hF.symm)
  filter_upwards [h] with x hx hxb
  apply hx.trans
  change MeasureTheory.convolution (kernel q (R+S)) F
    (ContinuousLinearMap.mul ℂ ℂ) volume x = _
  rw [MeasureTheory.convolution_mul_swap]
  unfold KernelConvolution.response
  apply integral_congr_ae
  filter_upwards [hF] with y hy
  change kernel q (R+S) (x-y) * F y = _
  rw [hy, mul_comm]
  exact kernel_source_eq q ρ R S hc x y hxb

theorem response_memLp_ball (q : Space → ℂ) (hq : LocallyIntegrable q volume)
    (ρ : Space → ℂ) (hρ : Integrable ρ volume) (F : ScalarL2)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ) (R S : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0) :
    MemLp (KernelConvolution.response q ρ) 2 (volume.restrict (closedBall 0 R)) := by
  have he : (fun x : Space => operator q hq (R+S) F x)
      =ᵐ[volume.restrict (closedBall 0 R)] KernelConvolution.response q ρ :=
    (ae_restrict_iff' measurableSet_closedBall).mpr
      (operator_ae_on_ball q hq ρ hρ F hF R S hc)
  exact ((Lp.memLp (operator q hq (R+S) F)).restrict (closedBall 0 R)).ae_eq he

theorem response_locallyIntegrable (q : Space → ℂ) (hq : LocallyIntegrable q volume)
    (ρ : Space → ℂ) (hρ : Integrable ρ volume) (F : ScalarL2)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ) (S : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0) :
    LocallyIntegrable (KernelConvolution.response q ρ) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 R).measure_ne_top
  have hi : IntegrableOn (KernelConvolution.response q ρ) (closedBall 0 R) :=
    (response_memLp_ball q hq ρ hρ F hF R S hc).integrable (by norm_num)
  exact hi.mono_set hR

end OQ14.LocalConvolution

#print axioms OQ14.LocalConvolution.kernel_integrable
#print axioms OQ14.LocalConvolution.kernel_source_eq
#print axioms OQ14.LocalConvolution.operator_ae_on_ball
#print axioms OQ14.LocalConvolution.response_memLp_ball
#print axioms OQ14.LocalConvolution.response_locallyIntegrable
