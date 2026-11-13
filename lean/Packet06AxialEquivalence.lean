import Packet06AxialReciprocalTransport

/-! The actual L² axial field action is a continuous linear equivalence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06AxialEquivalence
open MeasureTheory Maxwell ModalAxialRotation

theorem action_inverse (θ : ℝ) (u : VectorFourier.VectorL2) : action (-θ) (action θ u) = u := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have he := (rotation θ).measurePreserving.quasiMeasurePreserving.ae (ae_all_iff.mpr (fun j => action_ae θ u j))
  filter_upwards [action_ae (-θ) (action θ u) i, he] with x hx hy
  rw [hx]
  simp only [neg_neg] at hy ⊢
  simp_rw [hy]
  have hinv : rotation (-θ) (rotation θ x)=x := spatial_inverse θ x
  rw [hinv]
  have h : ((Real.cos θ : ℂ)^2+(Real.sin θ : ℂ)^2)=1 := by exact_mod_cast Real.cos_sq_add_sin_sq θ
  simp only [Complex.ofReal_cos,Complex.ofReal_sin] at h
  fin_cases i <;> simp [matrix,Fin.sum_univ_three,Real.cos_neg,Real.sin_neg]
  · linear_combination (u (VectorFourier.coordinateMap x) 0) * h
  · linear_combination (u (VectorFourier.coordinateMap x) 1) * h

def equivalence (θ : ℝ) : VectorFourier.VectorL2 ≃L[ℂ] VectorFourier.VectorL2 where
  toFun := action θ
  invFun := action (-θ)
  left_inv := action_inverse θ
  right_inv := by intro u; simpa only [neg_neg] using action_inverse (-θ) u
  map_add' := (action θ).map_add
  map_smul' := (action θ).map_smul
  continuous_toFun := (action θ).continuous
  continuous_invFun := (action (-θ)).continuous

end OQ14.Packet06AxialEquivalence
#print axioms OQ14.Packet06AxialEquivalence.action_inverse
