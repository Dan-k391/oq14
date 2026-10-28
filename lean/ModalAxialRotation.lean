import ModalOrigin
import ModalVolumeData
import HalfTurnVectorAction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OQ14.ModalAxialRotation
open Complex OQ14.Maxwell OQ14.ModalOrigin OQ14.ModalDipole OQ14.ModalWeightedMode

def spatial (θ : ℝ) (x : Space) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![Real.cos θ*x 0 - Real.sin θ*x 1,
    Real.sin θ*x 0 + Real.cos θ*x 1, x 2]

def vector (θ : ℝ) (v : Vector) : Vector :=
  ![(Real.cos θ : ℂ)*v 0 - (Real.sin θ : ℂ)*v 1,
    (Real.sin θ : ℂ)*v 0 + (Real.cos θ : ℂ)*v 1, v 2]

theorem spatial_norm (θ : ℝ) (x : Space) : ‖spatial θ x‖ = ‖x‖ := by
  have he : ‖spatial θ x‖^2 = ‖x‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_three, spatial, WithLp.equiv_symm_pi_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Real.norm_eq_abs, sq_abs]
    norm_num [Matrix.vecHead, Matrix.vecTail, Function.comp_def]
    linear_combination (x 0)^2 * (Real.cos_sq_add_sin_sq θ) +
      (x 1)^2 * (Real.cos_sq_add_sin_sq θ)
  nlinarith [norm_nonneg (spatial θ x), norm_nonneg x]

theorem electric_covariant (k : ℂ) (θ : ℝ) (x : Space) :
    centerE k (spatial θ x) = vector θ (centerE k x) := by
  ext i
  simp only [centerE, axisField, spatial_norm]
  fin_cases i <;> simp [spatial, vector,
    WithLp.equiv_symm_pi_apply, ofReal_add, ofReal_sub, ofReal_mul] <;> ring

theorem magnetic_covariant (κ k : ℂ) (θ : ℝ) (x : Space) :
    centerH κ k (spatial θ x) = vector θ (centerH κ k x) := by
  ext i
  simp only [centerH, swirlField, spatial_norm]
  fin_cases i <;> simp [spatial, vector,
    WithLp.equiv_symm_pi_apply, ofReal_add, ofReal_sub, ofReal_mul] <;> ring

theorem material_invariant (n : ℝ) (hn : 1 < n) (θ : ℝ) (x : Space) :
    (coefficient n hn).value (VectorFourier.coordinateMap (spatial θ x)) =
      (coefficient n hn).value (VectorFourier.coordinateMap x) := by
  rw [coefficient_value, coefficient_value, spatial_norm]

theorem spatial_inverse (θ : ℝ) (x : Space) : spatial (-θ) (spatial θ x) = x := by
  ext i
  fin_cases i <;> simp [spatial, WithLp.equiv_symm_pi_apply, Real.cos_neg, Real.sin_neg]
  · linear_combination x 0 * (Real.cos_sq_add_sin_sq θ)
  · linear_combination x 1 * (Real.cos_sq_add_sin_sq θ)

def rotation (θ : ℝ) : Space ≃ₗᵢ[ℝ] Space where
  toFun := spatial θ
  invFun := spatial (-θ)
  left_inv := spatial_inverse θ
  right_inv := by
    intro x
    simpa only [neg_neg] using spatial_inverse (-θ) x
  map_add' := by
    intro x y; ext i
    fin_cases i <;> simp [spatial, WithLp.equiv_symm_pi_apply] <;> ring
  map_smul' := by
    intro a x; ext i
    fin_cases i <;> simp [spatial, WithLp.equiv_symm_pi_apply] <;> ring
  norm_map' := spatial_norm θ

def matrix (θ : ℝ) (i j : Fin 3) : ℂ :=
  !![(Real.cos θ : ℂ), -(Real.sin θ : ℂ), 0;
      (Real.sin θ : ℂ), (Real.cos θ : ℂ), 0;
      0, 0, 1] i j

def pullback (θ : ℝ) : FourierL2.ScalarL2 →L[ℂ] FourierL2.ScalarL2 :=
  (MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ (rotation (-θ) : Space → Space)
    (rotation (-θ)).measurePreserving).toContinuousLinearMap

theorem pullback_ae (θ : ℝ) (g : FourierL2.ScalarL2) :
    pullback θ g =ᵐ[MeasureTheory.volume] fun x => g (rotation (-θ) x) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving g (rotation (-θ)).measurePreserving

def action (θ : ℝ) : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (DynamicConvolution.insert i) ∘L ((matrix θ i j) • pullback θ) ∘L (DynamicConvolution.component j)

theorem component_action (θ : ℝ) (i : Fin 3) (F : VectorFourier.VectorL2) :
    DynamicConvolution.component i (action θ F) =
      ∑ j : Fin 3, (matrix θ i j) • pullback θ (DynamicConvolution.component j F) := by
  simp only [action, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    DynamicConvolution.component_insert, ContinuousLinearMap.smul_apply]
  simp

theorem action_ae (θ : ℝ) (F : VectorFourier.VectorL2) (i : Fin 3) :
    (fun x => action θ F (VectorFourier.coordinateMap x) i) =ᵐ[MeasureTheory.volume]
      fun x => ∑ j : Fin 3, matrix θ i j * F (VectorFourier.coordinateMap (rotation (-θ) x)) j := by
  let g : Fin 3 → FourierL2.ScalarL2 := fun j => matrix θ i j • pullback θ (DynamicConvolution.component j F)
  have hp (j : Fin 3) : (g j : Space → ℂ) =ᵐ[MeasureTheory.volume]
      fun x => matrix θ i j * F (VectorFourier.coordinateMap (rotation (-θ) x)) j := by
    have hrot := (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae
      (HalfTurnVectorAction.component_ae F j)
    filter_upwards [MeasureTheory.Lp.coeFn_smul (matrix θ i j) (pullback θ (DynamicConvolution.component j F)),
      pullback_ae θ (DynamicConvolution.component j F), hrot] with x h1 h2 h3
    simp only [g, h1, Pi.smul_apply, smul_eq_mul, h2, h3]
  have hsum : ((∑ j : Fin 3, g j : FourierL2.ScalarL2) : Space → ℂ) =ᵐ[MeasureTheory.volume]
      fun x => ∑ j : Fin 3, matrix θ i j * F (VectorFourier.coordinateMap (rotation (-θ) x)) j := by
    simp only [Fin.sum_univ_three]
    filter_upwards [MeasureTheory.Lp.coeFn_add (g 0 + g 1) (g 2),
      MeasureTheory.Lp.coeFn_add (g 0) (g 1), hp 0, hp 1, hp 2] with x h1 h2 h0 h1' h2'
    simp only [h1, h2, Pi.add_apply, h0, h1', h2']
  filter_upwards [HalfTurnVectorAction.component_ae (action θ F) i, hsum] with x h1 h2
  rw [←h1, component_action]
  exact h2

theorem matrix_vector (θ : ℝ) (v : Vector) (i : Fin 3) :
    (∑ j : Fin 3, matrix θ i j * v j) = vector θ v i := by
  fin_cases i <;> simp [matrix, vector, Fin.sum_univ_three, sub_eq_add_neg]

theorem numerator_fixed (n : ℝ) (hn : 1 < n) (z : ℂ) (θ : ℝ) :
    action θ (ModalVolumeData.numerator n hn z) = ModalVolumeData.numerator n hn z := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hrot : ∀ᵐ x : Space ∂MeasureTheory.volume, ∀ j : Fin 3,
      ModalVolumeData.numerator n hn z (VectorFourier.coordinateMap (rotation (-θ) x)) j =
        (Real.sqrt ((coefficient n hn).value (VectorFourier.coordinateMap (rotation (-θ) x))) : ℂ) *
          ((I/(n : ℂ))*centerE ((n : ℂ)*z) (rotation (-θ) x) j) :=
    MeasureTheory.ae_all_iff.mpr (fun j => (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae
      (ModalVolumeData.numerator_actual n hn z j))
  filter_upwards [action_ae θ (ModalVolumeData.numerator n hn z) i, hrot,
    ModalVolumeData.numerator_actual n hn z i] with x ha hr hx
  rw [ha, hx]
  have hm : (coefficient n hn).value (VectorFourier.coordinateMap (rotation (-θ) x)) =
      (coefficient n hn).value (VectorFourier.coordinateMap x) := material_invariant n hn (-θ) x
  simp_rw [hr, hm]
  have he : vector θ (centerE ((n : ℂ)*z) (rotation (-θ) x)) = centerE ((n : ℂ)*z) x := by
    rw [← electric_covariant]
    change centerE ((n : ℂ)*z) (spatial θ (spatial (-θ) x)) = _
    rw [show spatial θ (spatial (-θ) x) = x by simpa only [neg_neg] using spatial_inverse (-θ) x]
  have hi := congrFun he i
  rw [← matrix_vector] at hi
  rw [← hi]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def axialSector : Submodule ℂ VectorFourier.VectorL2 :=
  ⨅ θ : ℝ, LinearMap.ker (action θ - 1 : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2)

theorem axialSector_closed : IsClosed (axialSector : Set VectorFourier.VectorL2) := by
  rw [axialSector, Submodule.iInf_coe]
  exact isClosed_iInter (fun θ => ContinuousLinearMap.isClosed_ker (action θ - 1))

theorem numerator_in_axialSector (n : ℝ) (hn : 1 < n) (z : ℂ) :
    ModalVolumeData.numerator n hn z ∈ axialSector := by
  simp only [axialSector, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero]
  exact numerator_fixed n hn z

#print axioms OQ14.ModalAxialRotation.numerator_in_axialSector
#print axioms OQ14.ModalAxialRotation.axialSector_closed
#print axioms OQ14.ModalAxialRotation.numerator_fixed
#print axioms OQ14.ModalAxialRotation.action_ae
#print axioms OQ14.ModalAxialRotation.component_action
#print axioms OQ14.ModalAxialRotation.rotation
#print axioms OQ14.ModalAxialRotation.spatial_norm
#print axioms OQ14.ModalAxialRotation.electric_covariant
#print axioms OQ14.ModalAxialRotation.magnetic_covariant
#print axioms OQ14.ModalAxialRotation.material_invariant
end OQ14.ModalAxialRotation











