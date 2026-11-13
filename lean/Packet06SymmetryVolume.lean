import Packet06AxialConvolution
import Packet06MeridionalConvolution
import ComplexConvolutionAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SymmetryVolume
open Filter Metric Set OQ14.StaticCoefficient
open scoped Topology
abbrev V := VectorFourier.VectorL2
abbrev Space := FourierL2.Space

theorem real_comm_extension (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) (T : V →L[ℂ] V)
    (hreal : ∀ (k : ℝ) (u : V), T (DynamicVolume.volumeBlock c k R u) =
      DynamicVolume.volumeBlock c k R (T u)) (z : ℂ) :
    T * ComplexConvolutionAnalytic.volumeBlock c z R =
      ComplexConvolutionAnalytic.volumeBlock c z R * T := by
  let left : ℂ → V →L[ℂ] V := fun z => T ∘L ComplexConvolutionAnalytic.volumeBlock c z R
  let right : ℂ → V →L[ℂ] V := fun z => ComplexConvolutionAnalytic.volumeBlock c z R ∘L T
  have hl : Differentiable ℂ left := (differentiable_const T).clm_comp
    (ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR)
  have hr : Differentiable ℂ right := (ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR).clm_comp
    (differentiable_const T)
  have heq (t : ℝ) : left t = right t := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [left,right,ContinuousLinearMap.comp_apply,ComplexConvolutionAnalytic.volumeBlock_ofReal]
    exact hreal t u
  have hclosure : (1 : ℂ) ∈ closure ({w | left w = right w} \ {(1 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let r : ℝ := 1+ε/2
    have hr1 : (r : ℂ) ≠ 1 := by
      have h : r ≠ 1 := by dsimp [r]; linarith
      exact_mod_cast h
    refine ⟨(r : ℂ),⟨heq r,hr1⟩,?_⟩
    have hsub : (r : ℂ)-1 = ((ε/2 : ℝ) : ℂ) := by dsimp [r]; push_cast; ring
    rw [dist_comm,dist_eq_norm,hsub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact (show AnalyticOnNhd ℂ left Set.univ from fun w _ => hl.analyticAt w).eqOn_of_preconnected_of_mem_closure
    (fun w _ => hr.analyticAt w) isPreconnected_univ (mem_univ 1) hclosure (mem_univ z)

theorem axial_volume_comm (c : Coefficient) (hc : Packet06MaterialSymmetry.Axial c)
    (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (θ : ℝ) (z : ℂ) :
    ModalAxialRotation.action θ * ComplexConvolutionAnalytic.volumeBlock c z R =
      ComplexConvolutionAnalytic.volumeBlock c z R * ModalAxialRotation.action θ := by
  apply real_comm_extension c R hR (ModalAxialRotation.action θ)
  intro k u
  unfold DynamicVolume.volumeBlock
  simp only [ContinuousLinearMap.sub_apply,map_sub]
  rw [StaticNewton.volumeBlock_eq,Packet06MaterialSymmetry.axial_static_comm c hc,
    Packet06AxialConvolution.weightedRemainder_comm c hc R hR hsupp]

theorem meridional_volume_comm (c : Coefficient) (hc : Packet06MaterialSymmetry.Meridional c)
    (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) :
    ModalMeridionalReflection.action * ComplexConvolutionAnalytic.volumeBlock c z R =
      ComplexConvolutionAnalytic.volumeBlock c z R * ModalMeridionalReflection.action := by
  apply real_comm_extension c R hR ModalMeridionalReflection.action
  intro k u
  unfold DynamicVolume.volumeBlock
  simp only [ContinuousLinearMap.sub_apply,map_sub]
  rw [StaticNewton.volumeBlock_eq,Packet06MaterialSymmetry.meridional_static_comm c hc,
    Packet06MeridionalConvolution.weighted_comm c hc R hsupp]
#print axioms OQ14.Packet06SymmetryVolume.real_comm_extension
#print axioms OQ14.Packet06SymmetryVolume.axial_volume_comm
#print axioms OQ14.Packet06SymmetryVolume.meridional_volume_comm
end OQ14.Packet06SymmetryVolume
