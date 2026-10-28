import ModalAxialConvolution
import ModalAxialStatic
import ComplexConvolutionAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ModalAxialVolume
open Complex MeasureTheory Metric Set Filter OQ14.ModalAxialRotation OQ14.ModalWeightedMode
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem real_comm (n : ℝ) (hn : 1 < n) (θ k : ℝ) (u : VectorL2) :
    action θ (DynamicVolume.volumeBlock (coefficient n hn) k 1 u) =
      DynamicVolume.volumeBlock (coefficient n hn) k 1 (action θ u) := by
  unfold DynamicVolume.volumeBlock
  simp only [ContinuousLinearMap.sub_apply, map_sub]
  rw [ModalAxialStatic.static_volume_comm n hn θ, ModalAxialConvolution.weightedRemainder_comm n hn θ k]

def left (n : ℝ) (hn : 1 < n) (θ : ℝ) (z : ℂ) : VectorL2 →L[ℂ] VectorL2 :=
  action θ ∘L ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1

def right (n : ℝ) (hn : 1 < n) (θ : ℝ) (z : ℂ) : VectorL2 →L[ℂ] VectorL2 :=
  ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 ∘L action θ

theorem complex_comm (n : ℝ) (hn : 1 < n) (θ : ℝ) (z : ℂ) :
    left n hn θ z = right n hn θ z := by
  have hl : Differentiable ℂ (left n hn θ) :=
    (differentiable_const (action θ)).clm_comp
      (ComplexConvolutionAnalytic.volumeBlock_differentiable (coefficient n hn) 1 (by norm_num))
  have hr : Differentiable ℂ (right n hn θ) :=
    (ComplexConvolutionAnalytic.volumeBlock_differentiable (coefficient n hn) 1 (by norm_num)).clm_comp
      (differentiable_const (action θ))
  have heq (t : ℝ) : left n hn θ t = right n hn θ t := by
    apply ContinuousLinearMap.ext; intro u
    simp only [left, right, ContinuousLinearMap.comp_apply, ComplexConvolutionAnalytic.volumeBlock_ofReal]
    exact real_comm n hn θ t u
  have hclosure : (1 : ℂ) ∈ closure ({w | left n hn θ w = right n hn θ w} \ {(1 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let r : ℝ := 1+ε/2
    have hr1 : (r : ℂ) ≠ 1 := by
      have h : r ≠ 1 := by dsimp [r]; linarith
      exact_mod_cast h
    refine ⟨(r : ℂ), ⟨heq r, hr1⟩, ?_⟩
    have hsub : (r : ℂ)-1 = ((ε/2 : ℝ) : ℂ) := by dsimp [r]; push_cast; ring
    rw [dist_comm, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact (show AnalyticOnNhd ℂ (left n hn θ) Set.univ from fun w _ => hl.analyticAt w).eqOn_of_preconnected_of_mem_closure
    (fun w _ => hr.analyticAt w) isPreconnected_univ (mem_univ 1) hclosure (mem_univ z)

theorem axial_invariant (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2) (hu : u ∈ axialSector) :
    ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u ∈ axialSector := by
  simp only [axialSector, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero] at hu ⊢
  intro θ
  have h := congrFun (congrArg DFunLike.coe (complex_comm n hn θ z)) u
  simp only [left, right, ContinuousLinearMap.comp_apply, hu θ] at h
  exact h

#print axioms OQ14.ModalAxialVolume.real_comm
#print axioms OQ14.ModalAxialVolume.complex_comm
#print axioms OQ14.ModalAxialVolume.axial_invariant
end OQ14.ModalAxialVolume

