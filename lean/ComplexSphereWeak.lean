import ComplexResponseRealWeak
import ModalWeightedMode

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexSphereWeak
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.DynamicSource
  OQ14.ComplexKernelResponse OQ14.ComplexResponseTests OQ14.ComplexResponseRealWeak
open scoped SchwartzMap Topology
abbrev VectorL2 := VectorFourier.VectorL2

def pair (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2) (i : Fin 3) (f : Test) : ℂ :=
  testPair i f.val (response (ModalWeightedMode.coefficient n hn) z 1 u)

theorem source_pair (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ ball 0 1) :
    (∫ x, DynamicVolume.source (ModalWeightedMode.coefficient n hn) u i x * f.val x) =
      ((n : ℂ)^2-1) * pair n hn z u i f := by
  rw [pair, testPair_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ComplexResponseAnalytic.kernel_source_relation
    (ModalWeightedMode.coefficient n hn) z 1 u hker i] with x hx
  by_cases hi : x ∈ ball (0 : Space) 1
  · rw [hx, ModalWeightedMode.coefficient_value, if_pos (by simpa using hi)]
    push_cast
    ring
  · have hz : f.val x = 0 := image_eq_zero_of_nmem_tsupport (fun h => hi (hf h))
    simp [hz]

theorem curlcurl (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ ball 0 1) :
    MagneticResponse.curlPair (MagneticResponse.curlPair (pair n hn z u)) i f =
      (z*n)^2 * pair n hn z u i f := by
  have h := residual_zero (ModalWeightedMode.coefficient n hn) 1 (by norm_num) u
    (ModalWeightedMode.coefficient_support n hn) i f (hf.trans ball_subset_closedBall) z
  rw [MagneticResponse.curlPair_curlPair]
  unfold ComplexResponseRealWeak.residual at h
  rw [source_pair n hn z u hker i f hf] at h
  dsimp only [ComplexResponseRealWeak.residual, pair] at *
  linear_combination h

theorem div_curl (A : Fin 3 → Test → ℂ) (f : Test) :
    (∑ j : Fin 3, MagneticResponse.curlPair A j (testPartial j f)) = 0 := by
  have h01 := partial_commute (0 : Fin 3) 1 f
  have h02 := partial_commute (0 : Fin 3) 2 f
  have h12 := partial_commute (1 : Fin 3) 2 f
  simp [MagneticResponse.curlPair, WeakCurl.next, WeakCurl.previous,
    Fin.sum_univ_three, h01, h02, h12]
  ring

theorem divergence_zero (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ ball 0 1) :
    (∑ j : Fin 3, pair n hn z u j (testPartial j f)) = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have h := div_curl (MagneticResponse.curlPair (pair n hn z u)) f
  have he (j : Fin 3) := curlcurl n hn z u hker j (testPartial j f) ((partial_support j f).trans hf)
  simp_rw [he] at h
  rw [← Finset.mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 (mul_ne_zero hz hn0))

theorem component_helmholtz_test (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ ball 0 1) :
    (∑ j : Fin 3, pair n hn z u i (testPartial j (testPartial j f))) +
      (z*n)^2 * pair n hn z u i f = 0 := by
  have hc := curlcurl n hn z u hker i f hf
  rw [MagneticResponse.curlPair_curlPair] at hc
  have hd := divergence_zero n hn z hz u hker (testPartial i f) ((partial_support i f).trans hf)
  linear_combination hd - hc

#print axioms OQ14.ComplexSphereWeak.div_curl
#print axioms OQ14.ComplexSphereWeak.divergence_zero
#print axioms OQ14.ComplexSphereWeak.component_helmholtz_test
#print axioms OQ14.ComplexSphereWeak.source_pair
#print axioms OQ14.ComplexSphereWeak.curlcurl
end OQ14.ComplexSphereWeak



