import ModalMeridionalStatic
import ComplexConvolutionAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ModalMeridionalVolume
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ModalMeridionalReflection
  OQ14.ModalMeridionalStatic OQ14.ModalWeightedMode OQ14.HalfTurnVectorAction
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem remainder_reflect (k : ℝ) (z : Maxwell.Space) (i j : Fin 3) :
    DyadicKernel.remainder k (reflection z) i j =
      (sign i : ℂ)*(sign j : ℂ)*DyadicKernel.remainder k z i j := by
  unfold DyadicKernel.remainder DyadicKernel.dyadic GreenKernel.phiHessian GreenKernel.phi
  have hn : ‖reflection z‖ = ‖z‖ := reflection.norm_map z
  have hc (l : Fin 3) : ((reflection z l : ℝ) : ℂ)=(sign l : ℂ)*(z l : ℂ) := by
    rw [reflection_coordinate]; push_cast; ring
  simp only [hn,hc]
  fin_cases i <;> fin_cases j <;> simp [sign] <;> ring

theorem weighted_comm (n : ℝ) (hn : 1 < n) (k : ℝ) (u : VectorL2) :
    action (DynamicVolume.weightedRemainder (coefficient n hn) k 1 u) =
      DynamicVolume.weightedRemainder (coefficient n hn) k 1 (action u) := by
  let c := coefficient n hn
  let T := DynamicVolume.weightedRemainder c k 1
  have hT (u : VectorL2) (i : Fin 3) :
      (fun x => T u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
        ∑ j : Fin 3, ∫ y, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c u j y :=
    DynamicVolume.weightedRemainder_actual c u k 1 (coefficient_support n hn) i
  have hK (x y : Maxwell.Space) (i j : Fin 3) :
      DyadicKernel.remainder k (reflection x-reflection y) i j =
        (sign i : ℂ)*(sign j : ℂ)*DyadicKernel.remainder k (x-y) i j := by
    rw [← map_sub]; exact remainder_reflect k (x-y) i j
  apply vector_ext_pt
  intro i
  have I1 (x : Maxwell.Space) (j : Fin 3) :
      (∫ y, DyadicKernel.remainder k (reflection x-y) i j * DynamicVolume.source c u j y)=
        (sign i : ℂ)*(sign j : ℂ)*∫ y, DyadicKernel.remainder k (x-reflection y) i j * DynamicVolume.source c u j y := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have h := hK x (reflection y) i j
    rw [reflection_reflection] at h
    rw [h]; ring
  have I2 (x : Maxwell.Space) (j : Fin 3) :
      (∫ y, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c (action u) j y)=
        (sign j : ℂ)*∫ y, DyadicKernel.remainder k (x-reflection y) i j * DynamicVolume.source c u j y := by
    have h3 : (∫ y, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c (action u) j y)=
        ∫ y,(sign j : ℂ)*(DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c u j (reflection y)) := by
      apply integral_congr_ae
      filter_upwards [source_action n hn u j] with y hy
      rw [hy]; ring
    have h4 := reflection.measurePreserving.integral_comp reflection.toHomeomorph.measurableEmbedding
      (fun y' => DyadicKernel.remainder k (x-reflection y') i j * DynamicVolume.source c u j y')
    simp only [reflection_reflection] at h4
    rw [h3,integral_const_mul]
    congr 1
  filter_upwards [ModalMeridionalReflection.action_ae (T u) i,ae_reflect (hT u i),hT (action u) i] with x h1 h2 h3
  rw [h1,h3,h2,ModalMeridionalReflection.sphere_symmetric n hn x]
  simp only [I1,I2]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := sign_sq i
  linear_combination ((Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*(sign j : ℂ)*
    ∫ y, DyadicKernel.remainder k (x-reflection y) i j * DynamicVolume.source c u j y)*h

theorem real_comm (n : ℝ) (hn : 1 < n) (k : ℝ) (u : VectorL2) :
    action (DynamicVolume.volumeBlock (coefficient n hn) k 1 u) =
      DynamicVolume.volumeBlock (coefficient n hn) k 1 (action u) := by
  unfold DynamicVolume.volumeBlock
  simp only [ContinuousLinearMap.sub_apply, map_sub]
  rw [static_volume_comm n hn, weighted_comm n hn k]

def left (n : ℝ) (hn : 1 < n) (z : ℂ) : VectorL2 →L[ℂ] VectorL2 :=
  action ∘L ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1

def right (n : ℝ) (hn : 1 < n) (z : ℂ) : VectorL2 →L[ℂ] VectorL2 :=
  ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 ∘L action

theorem complex_comm (n : ℝ) (hn : 1 < n) (z : ℂ) : left n hn z = right n hn z := by
  have hl : Differentiable ℂ (left n hn) :=
    (differentiable_const action).clm_comp
      (ComplexConvolutionAnalytic.volumeBlock_differentiable (coefficient n hn) 1 (by norm_num))
  have hr : Differentiable ℂ (right n hn) :=
    (ComplexConvolutionAnalytic.volumeBlock_differentiable (coefficient n hn) 1 (by norm_num)).clm_comp
      (differentiable_const action)
  have heq (t : ℝ) : left n hn t = right n hn t := by
    apply ContinuousLinearMap.ext; intro u
    simp only [left, right, ContinuousLinearMap.comp_apply, ComplexConvolutionAnalytic.volumeBlock_ofReal]
    exact real_comm n hn t u
  have hclosure : (1 : ℂ) ∈ closure ({w | left n hn w = right n hn w} \ {(1 : ℂ)}) := by
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
  exact (show AnalyticOnNhd ℂ (left n hn) Set.univ from fun w _ => hl.analyticAt w).eqOn_of_preconnected_of_mem_closure
    (fun w _ => hr.analyticAt w) isPreconnected_univ (mem_univ 1) hclosure (mem_univ z)

theorem electricSector_invariant (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2) (hu : u ∈ electricSector) :
    ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u ∈ electricSector := by
  refine ⟨ModalAxialVolume.axial_invariant n hn z u hu.1, ?_⟩
  have hf : action u = u := by
    have h := hu.2
    change (action - 1) u = 0 at h
    simpa using sub_eq_zero.mp h
  change (action - 1) (ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u) = 0
  have h := congrFun (congrArg DFunLike.coe (complex_comm n hn z)) u
  simp only [left, right, ContinuousLinearMap.comp_apply, hf] at h
  simpa using sub_eq_zero.mpr h

#print axioms OQ14.ModalMeridionalVolume.complex_comm
#print axioms OQ14.ModalMeridionalVolume.electricSector_invariant
#print axioms OQ14.ModalMeridionalVolume.remainder_reflect
#print axioms OQ14.ModalMeridionalVolume.weighted_comm
end OQ14.ModalMeridionalVolume

