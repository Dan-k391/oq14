import ModalVolumeData
import ModalDipoleOrigin
import ComplexConvolutionAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Analytic continuation of the actual sphere volume data from a real-frequency identity.
The real outgoing representation is an explicit premise of this bridge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ModalVolumeContinuation
open Complex MeasureTheory Set Metric OQ14.ModalVolumeData OQ14.ModalAlgebra
open scoped Topology

def left (n : ℝ) (hn : 1 < n) (k : ℂ) : VectorL2 :=
  ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) k 1
    (numerator n hn k)

def right (n : ℝ) (hn : 1 < n) (k : ℂ) : VectorL2 :=
  ModalDipoleOrigin.regularized (n : ℂ) k • incident n hn k

theorem left_analytic (n : ℝ) (hn : 1 < n) (k : ℂ) : AnalyticAt ℂ (left n hn) k := by
  have hd : Differentiable ℂ (left n hn) :=
    (ComplexConvolutionAnalytic.volumeBlock_differentiable
      (ModalWeightedMode.coefficient n hn) 1 (by norm_num)).clm_apply
      (fun z => (numerator_analytic n hn z).differentiableAt)
  exact hd.analyticAt k

theorem right_analytic (n : ℝ) (hn : 1 < n) (k : ℂ) : AnalyticAt ℂ (right n hn) k :=
  (ModalDipoleOrigin.regularized_analyticAt (n : ℂ) k).smul (incident_analytic n hn k)

theorem complex_identity_of_real (n : ℝ) (hn : 1 < n)
    (hreal : ∀ k : ℝ, 0 < k →
      DynamicVolume.volumeBlock (ModalWeightedMode.coefficient n hn) k 1 (numerator n hn k) =
        tmDet 1 (n : ℂ) k • incident n hn k) (z : ℂ) :
    left n hn z = right n hn z := by
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have heq (k : ℝ) (hk : 0 < k) : left n hn k = right n hn k := by
    rw [left, right, ComplexConvolutionAnalytic.volumeBlock_ofReal,
      ModalDipoleOrigin.regularized_eq _ _ hn0 (Complex.ofReal_ne_zero.mpr hk.ne')]
    exact hreal k hk
  have hclosure : (1 : ℂ) ∈ closure ({w | left n hn w = right n hn w} \ {(1 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let r : ℝ := 1+ε/2
    have hr : 0 < r := by dsimp [r]; linarith
    have hr1 : (r : ℂ) ≠ 1 := by
      have h : r ≠ 1 := by dsimp [r]; linarith
      exact_mod_cast h
    refine ⟨(r : ℂ), ⟨heq r hr, hr1⟩, ?_⟩
    have hsub : (r : ℂ)-1 = ((ε/2 : ℝ) : ℂ) := by dsimp [r]; push_cast; ring
    rw [dist_comm, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact (show AnalyticOnNhd ℂ (left n hn) Set.univ from fun w _ => left_analytic n hn w).eqOn_of_preconnected_of_mem_closure
      (fun w _ => right_analytic n hn w) isPreconnected_univ (mem_univ 1) hclosure (mem_univ z)

theorem nonzero_kernel_of_real_identity (n : ℝ) (hn : 1 < n)
    (hreal : ∀ k : ℝ, 0 < k →
      DynamicVolume.volumeBlock (ModalWeightedMode.coefficient n hn) k 1 (numerator n hn k) =
        tmDet 1 (n : ℂ) k • incident n hn k)
    (z : ℂ) (hz : z ≠ 0) (hroot : tmDet 1 (n : ℂ) z = 0) :
    numerator n hn z ≠ 0 ∧
      ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1
        (numerator n hn z) = 0 := by
  refine ⟨numerator_ne_zero n hn z hz, ?_⟩
  have he := complex_identity_of_real n hn hreal z
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  simpa only [left, right, ModalDipoleOrigin.regularized_eq _ _ hn0 hz, hroot, zero_smul] using he

end OQ14.ModalVolumeContinuation

#print axioms OQ14.ModalVolumeContinuation.left_analytic
#print axioms OQ14.ModalVolumeContinuation.right_analytic
#print axioms OQ14.ModalVolumeContinuation.complex_identity_of_real
#print axioms OQ14.ModalVolumeContinuation.nonzero_kernel_of_real_identity
