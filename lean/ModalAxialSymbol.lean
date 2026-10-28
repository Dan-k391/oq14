import ModalAxialFourier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ModalAxialSymbol
open Complex OQ14.Maxwell OQ14.ModalAxialRotation

def rotateVector (θ : ℝ) (v : VectorFourier.Vector) : VectorFourier.Vector :=
  (WithLp.equiv 2 (Fin 3 → ℂ)).symm (vector θ (fun j => v j))

theorem rotated_frequency (θ : ℝ) (x : Space) (i : Fin 3) :
    ((VectorFourier.coordinateMap (rotation (-θ) x)) i : ℂ) =
      ∑ j : Fin 3, matrix θ j i * (x j : ℂ) := by
  change ((rotation (-θ) x i : ℝ) : ℂ) = _
  fin_cases i <;> simp [rotation, spatial, matrix,
    WithLp.equiv_symm_pi_apply, Real.cos_neg, Real.sin_neg, Fin.sum_univ_three,
    sub_eq_add_neg]

theorem dot_cov (θ : ℝ) (x : Space) (v : VectorFourier.Vector) :
    (∑ j : Fin 3, ((VectorFourier.coordinateMap (rotation (-θ) x)) j : ℂ) * v j) =
      ∑ j : Fin 3, (x j : ℂ) * rotateVector θ v j := by
  simp_rw [rotated_frequency]
  simp [rotateVector, vector, matrix, WithLp.equiv_symm_pi_apply, Fin.sum_univ_three]
  ring

theorem square_cov (θ : ℝ) (x : Space) :
    (∑ j : Fin 3, ((VectorFourier.coordinateMap (rotation (-θ) x)) j : ℂ)^2) =
      ∑ j : Fin 3, (x j : ℂ)^2 := by
  simp_rw [rotated_frequency]
  simp [matrix, Fin.sum_univ_three]
  have h : ((Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2) = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  linear_combination ((x 0 : ℂ)^2 + (x 1 : ℂ)^2) * h

theorem rotate_back (θ : ℝ) (x : Space) (i : Fin 3) :
    (∑ j : Fin 3, matrix θ i j * ((VectorFourier.coordinateMap (rotation (-θ) x)) j : ℂ)) = (x i : ℂ) := by
  simp_rw [rotated_frequency]
  fin_cases i <;> simp [matrix, Fin.sum_univ_three]
  · have h : ((Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2) = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq θ
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    linear_combination (x 0 : ℂ) * h
  · have h : ((Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2) = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq θ
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    linear_combination (x 1 : ℂ) * h

theorem symbol_cov (θ : ℝ) (x : Space) (v : VectorFourier.Vector) (i : Fin 3) :
    (∑ j : Fin 3, matrix θ i j * LongitudinalProjection.symbol
      (VectorFourier.coordinateMap (rotation (-θ) x)) v j) =
      LongitudinalProjection.symbol (VectorFourier.coordinateMap x) (rotateVector θ v) i := by
  simp_rw [LongitudinalProjection.symbol_coordinate]
  rw [dot_cov, square_cov]
  change (∑ j : Fin 3, matrix θ i j * (((∑ j : Fin 3, (x j : ℂ) * rotateVector θ v j) / (∑ j : Fin 3, (x j : ℂ)^2)) * ((VectorFourier.coordinateMap (rotation (-θ) x)) j : ℂ))) = _
  change _ = ((∑ j : Fin 3, (x j : ℂ) * rotateVector θ v j) / (∑ j : Fin 3, (x j : ℂ)^2)) * (x i : ℂ)
  rw [← rotate_back θ x i]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem action_multiplier (θ : ℝ) (F : VectorFourier.VectorL2) :
    action θ (LongitudinalProjection.multiplier F) = LongitudinalProjection.multiplier (action θ F) := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hM := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (LongitudinalProjection.multiplier_ae F)
  have hM' := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (LongitudinalProjection.multiplier_ae (action θ F))
  have hU : ∀ᵐ x : Space ∂MeasureTheory.volume, ∀ j : Fin 3,
      action θ F (VectorFourier.coordinateMap x) j =
        ∑ l : Fin 3, matrix θ j l * F (VectorFourier.coordinateMap (rotation (-θ) x)) l :=
    MeasureTheory.ae_all_iff.mpr (action_ae θ F)
  have hr := (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae hM
  filter_upwards [action_ae θ (LongitudinalProjection.multiplier F) i, hr, hM', hU] with x h1 h2 h3 h4
  rw [h1, h3]
  have hv : action θ F (VectorFourier.coordinateMap x) =
      rotateVector θ (F (VectorFourier.coordinateMap (rotation (-θ) x))) := by
    ext j
    rw [h4 j]
    simp only [rotateVector, WithLp.equiv_symm_pi_apply]
    exact matrix_vector θ _ j
  rw [hv]
  simp_rw [h2]
  exact symbol_cov θ x _ i

#print axioms OQ14.ModalAxialSymbol.action_multiplier
#print axioms OQ14.ModalAxialSymbol.symbol_cov
end OQ14.ModalAxialSymbol


