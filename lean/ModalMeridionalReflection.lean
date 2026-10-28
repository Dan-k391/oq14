import ModalAxialVolume

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OQ14.ModalMeridionalReflection
open Complex MeasureTheory OQ14.Maxwell OQ14.ModalOrigin OQ14.ModalDipole
  OQ14.ModalWeightedMode

def sign (i : Fin 3) : ℝ := if i = 1 then -1 else 1

def linear : Space →L[ℝ] Space := ContinuousLinearMap.id ℝ Space -
  (2 : ℝ) • (EuclideanSpace.proj 1).smulRight (basis 1)

theorem linear_coordinate (x : Space) (i : Fin 3) : linear x i = sign i * x i := by
  fin_cases i <;> simp [linear, sign, basis, smul_eq_mul, EuclideanSpace.single_apply]; ring

theorem linear_involutive (x : Space) : linear (linear x) = x := by
  ext i
  rw [linear_coordinate, linear_coordinate]
  fin_cases i <;> simp [sign]

theorem linear_norm (x : Space) : ‖linear x‖ = ‖x‖ := by
  have he : ‖linear x‖^2 = ‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_three, linear_coordinate, sign, Real.norm_eq_abs, sq_abs]
  nlinarith [norm_nonneg x, norm_nonneg (linear x)]

def reflection : Space ≃ₗᵢ[ℝ] Space :=
  { LinearEquiv.ofInvolutive linear.toLinearMap linear_involutive with norm_map' := linear_norm }

theorem reflection_coordinate (x : Space) (i : Fin 3) : reflection x i = sign i*x i := linear_coordinate x i

theorem sign_sq (i : Fin 3) : (sign i : ℂ)*(sign i : ℂ)=1 := by
  fin_cases i <;> simp [sign]

def pullback : FourierL2.ScalarL2 →L[ℂ] FourierL2.ScalarL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (reflection : Space → Space) reflection.measurePreserving).toContinuousLinearMap

theorem pullback_ae (g : FourierL2.ScalarL2) : pullback g =ᵐ[volume] fun x => g (reflection x) :=
  Lp.coeFn_compMeasurePreserving g reflection.measurePreserving

def action : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  ∑ i : Fin 3, (DynamicConvolution.insert i) ∘L ((sign i : ℂ) • pullback) ∘L (DynamicConvolution.component i)

theorem component_action (j : Fin 3) (F : VectorFourier.VectorL2) :
    DynamicConvolution.component j (action F) = (sign j : ℂ) • pullback (DynamicConvolution.component j F) := by
  simp only [action, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    DynamicConvolution.component_insert, ContinuousLinearMap.smul_apply]
  simp

theorem action_ae (F : VectorFourier.VectorL2) (j : Fin 3) :
    (fun x => action F (VectorFourier.coordinateMap x) j) =ᵐ[volume]
      fun x => (sign j : ℂ) * F (VectorFourier.coordinateMap (reflection x)) j := by
  have hr := reflection.measurePreserving.quasiMeasurePreserving.ae (HalfTurnVectorAction.component_ae F j)
  filter_upwards [HalfTurnVectorAction.component_ae (action F) j, hr, pullback_ae (DynamicConvolution.component j F),
    Lp.coeFn_smul (sign j : ℂ) (pullback (DynamicConvolution.component j F))] with x h1 h2 h3 h4
  rw [←h1, component_action, h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h3,h2]

theorem centerE_polar (k : ℂ) (x : Space) (i : Fin 3) :
    (sign i : ℂ)*centerE k (reflection x) i = centerE k x i := by
  fin_cases i <;> simp [centerE, axisField, reflection.norm_map, reflection_coordinate, sign]

theorem centerH_axial (κ k : ℂ) (x : Space) (i : Fin 3) :
    (sign i : ℂ)*centerH κ k (reflection x) i = -centerH κ k x i := by
  fin_cases i <;> simp [centerH, swirlField, reflection.norm_map, reflection_coordinate, sign]

theorem sphere_symmetric (n : ℝ) (hn : 1 < n) (x : Space) :
    (coefficient n hn).value (VectorFourier.coordinateMap (reflection x)) =
      (coefficient n hn).value (VectorFourier.coordinateMap x) := by
  rw [coefficient_value, coefficient_value, reflection.norm_map]

theorem reflection_reflection (x : Space) : reflection (reflection x) = x := linear_involutive x

theorem pullback_pullback (g : FourierL2.ScalarL2) : pullback (pullback g) = g := by
  apply Lp.ext
  have h := reflection.measurePreserving.quasiMeasurePreserving.ae (pullback_ae g)
  filter_upwards [pullback_ae (pullback g), h] with x h1 h2
  rw [h1, h2, reflection_reflection]

theorem action_involutive (F : VectorFourier.VectorL2) : action (action F) = F := by
  apply HalfTurnVectorAction.vector_eq_of_component
  intro j
  rw [component_action, component_action, map_smul, smul_smul, pullback_pullback, sign_sq, one_smul]

theorem numerator_fixed (n : ℝ) (hn : 1 < n) (z : ℂ) :
    action (ModalVolumeData.numerator n hn z) = ModalVolumeData.numerator n hn z := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hr := reflection.measurePreserving.quasiMeasurePreserving.ae
    (ModalVolumeData.numerator_actual n hn z i)
  filter_upwards [action_ae (ModalVolumeData.numerator n hn z) i, hr,
    ModalVolumeData.numerator_actual n hn z i] with x hu hr hx
  rw [hu, hr, hx, sphere_symmetric n hn x]
  have hc := centerE_polar ((n : ℂ)*z) x i
  linear_combination (Real.sqrt ((coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) *
    (I/(n : ℂ))*hc

def electricSector : Submodule ℂ VectorFourier.VectorL2 :=
  ModalAxialRotation.axialSector ⊓ LinearMap.ker (action - 1 : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2)

theorem electricSector_closed : IsClosed (electricSector : Set VectorFourier.VectorL2) := by
  have he : (electricSector : Set VectorFourier.VectorL2) =
      (ModalAxialRotation.axialSector : Set VectorFourier.VectorL2) ∩
        (LinearMap.ker (action - 1 : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2) : Set VectorFourier.VectorL2) := by
    ext u; simp [electricSector]
  rw [he]
  exact ModalAxialRotation.axialSector_closed.inter (ContinuousLinearMap.isClosed_ker (action - 1))

theorem numerator_in_electricSector (n : ℝ) (hn : 1 < n) (z : ℂ) :
    ModalVolumeData.numerator n hn z ∈ electricSector := by
  refine ⟨ModalAxialRotation.numerator_in_axialSector n hn z, ?_⟩
  change (action - 1) (ModalVolumeData.numerator n hn z) = 0
  simpa using sub_eq_zero.mpr (numerator_fixed n hn z)

#print axioms OQ14.ModalMeridionalReflection.numerator_in_electricSector
#print axioms OQ14.ModalMeridionalReflection.action_involutive
#print axioms OQ14.ModalMeridionalReflection.action_ae
#print axioms OQ14.ModalMeridionalReflection.centerE_polar
#print axioms OQ14.ModalMeridionalReflection.centerH_axial
#print axioms OQ14.ModalMeridionalReflection.sphere_symmetric
end OQ14.ModalMeridionalReflection





