import HalfTurnParityEquivariance
import ModalVolumeData
import ComplexConvolutionAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ModalHalfTurnSector
open Complex MeasureTheory Metric Set Filter OQ14.HalfTurnVectorAction
  OQ14.HalfTurnParityEquivariance OQ14.ModalWeightedMode
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

theorem real_comm (c : Coefficient) (hsym : Symmetric c) (R : ℝ)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (k : ℝ) (u : VectorL2) :
    U (DynamicVolume.volumeBlock c k R u) = DynamicVolume.volumeBlock c k R (U u) := by
  unfold DynamicVolume.volumeBlock
  simp only [ContinuousLinearMap.sub_apply, map_sub]
  rw [weightedRemainder_comm c hsym k R hc]
  congr 1
  rw [StaticNewton.volumeBlock_eq]
  unfold StaticCoefficient.weightedBlock
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, map_add]
  rw [sqrtMultiplier_comm c hsym, U_physicalProjection, sqrtMultiplier_comm c hsym]

def left (c : Coefficient) (R : ℝ) (z : ℂ) : VectorL2 →L[ℂ] VectorL2 :=
  U ∘L ComplexConvolutionAnalytic.volumeBlock c z R

def right (c : Coefficient) (R : ℝ) (z : ℂ) : VectorL2 →L[ℂ] VectorL2 :=
  ComplexConvolutionAnalytic.volumeBlock c z R ∘L U

theorem complex_comm (c : Coefficient) (hsym : Symmetric c) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) : left c R z = right c R z := by
  have hl : Differentiable ℂ (left c R) :=
    (differentiable_const U).clm_comp (ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR)
  have hr : Differentiable ℂ (right c R) :=
    (ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR).clm_comp (differentiable_const U)
  have heq (t : ℝ) : left c R t = right c R t := by
    apply ContinuousLinearMap.ext; intro u
    simp only [left, right, ContinuousLinearMap.comp_apply, ComplexConvolutionAnalytic.volumeBlock_ofReal]
    exact real_comm c hsym R hc t u
  have hclosure : (1 : ℂ) ∈ closure ({w | left c R w = right c R w} \ {(1 : ℂ)}) := by
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
  exact (show AnalyticOnNhd ℂ (left c R) Set.univ from fun w _ => hl.analyticAt w).eqOn_of_preconnected_of_mem_closure
    (fun w _ => hr.analyticAt w) isPreconnected_univ (mem_univ 1) hclosure (mem_univ z)

theorem sphere_symmetric (n : ℝ) (hn : 1 < n) : Symmetric (coefficient n hn) := by
  intro x
  rw [coefficient_value, coefficient_value, rot.norm_map]

def evenSector : Submodule ℂ VectorL2 := LinearMap.ker (U - 1 : VectorL2 →L[ℂ] VectorL2)

def oddSector : Submodule ℂ VectorL2 := LinearMap.ker (U + 1 : VectorL2 →L[ℂ] VectorL2)

theorem even_closed : IsClosed (evenSector : Set VectorL2) := ContinuousLinearMap.isClosed_ker (U - 1)
theorem odd_closed : IsClosed (oddSector : Set VectorL2) := ContinuousLinearMap.isClosed_ker (U + 1)

theorem even_invariant (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2) (hu : u ∈ evenSector) :
    ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u ∈ evenSector := by
  have hf : U u = u := by
    have h := hu; change (U - 1) u = 0 at h
    simpa using sub_eq_zero.mp h
  change (U - 1) (ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u) = 0
  have h := congrFun (congrArg DFunLike.coe
    (complex_comm (coefficient n hn) (sphere_symmetric n hn) 1 (by norm_num) (coefficient_support n hn) z)) u
  simp only [left, right, ContinuousLinearMap.comp_apply, hf] at h
  simpa using sub_eq_zero.mpr h

theorem odd_invariant (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2) (hu : u ∈ oddSector) :
    ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u ∈ oddSector := by
  have hf : U u = -u := by
    have h := hu; change (U + 1) u = 0 at h
    simpa using eq_neg_of_add_eq_zero_left h
  change (U + 1) (ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u) = 0
  have h := congrFun (congrArg DFunLike.coe
    (complex_comm (coefficient n hn) (sphere_symmetric n hn) 1 (by norm_num) (coefficient_support n hn) z)) u
  simp only [left, right, ContinuousLinearMap.comp_apply, hf, map_neg] at h
  simp [h]

theorem centerE_halfTurn (k : ℂ) (x : Maxwell.Space) (i : Fin 3) :
    (o i : ℂ) * ModalOrigin.centerE k (rot x) i = ModalOrigin.centerE k x i := by
  fin_cases i <;> simp [ModalOrigin.centerE, ModalDipole.axisField, rot.norm_map,
    rot_coordinate, o, SphereReactionKernel.sign]

theorem numerator_even (n : ℝ) (hn : 1 < n) (z : ℂ) :
    ModalVolumeData.numerator n hn z ∈ evenSector := by
  change (U - 1) (ModalVolumeData.numerator n hn z) = 0
  apply sub_eq_zero.mpr
  change U (ModalVolumeData.numerator n hn z) = ModalVolumeData.numerator n hn z
  apply vector_ext_pt
  intro i
  have ha := ae_rot (ModalVolumeData.numerator_actual n hn z i)
  filter_upwards [U_ae (ModalVolumeData.numerator n hn z) i, ha,
    ModalVolumeData.numerator_actual n hn z i] with x hu hr hx
  rw [hu, hr, hx, sphere_symmetric n hn x]
  have hc := centerE_halfTurn ((n : ℂ)*z) x i
  linear_combination (Real.sqrt ((coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) *
    (I/(n : ℂ))*hc

#print axioms OQ14.ModalHalfTurnSector.numerator_even
#print axioms OQ14.ModalHalfTurnSector.complex_comm
#print axioms OQ14.ModalHalfTurnSector.sphere_symmetric
#print axioms OQ14.ModalHalfTurnSector.even_closed
#print axioms OQ14.ModalHalfTurnSector.odd_closed
#print axioms OQ14.ModalHalfTurnSector.even_invariant
#print axioms OQ14.ModalHalfTurnSector.odd_invariant
end OQ14.ModalHalfTurnSector





