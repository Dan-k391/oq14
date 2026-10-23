import SymmetricScalarJets
import DebyePlanarJets

/-! Genuine partial derivatives, Laplacians, and two-jets of finite scalar combinations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ScalarFiniteCalculus
open Maxwell ModalDipole ExteriorClassical ExteriorHelmholtz
variable {ι κ : Type*}

theorem partial_sum (s : Finset κ) (F : κ → Space → ℂ) (A : κ → ℂ) (x : Space) (i : Fin 3)
    (hd : ∀ j ∈ s, DifferentiableAt ℝ (F j) x) :
    dcoord (fun y => ∑ j ∈ s, A j*F j y) x i=∑ j ∈ s, A j*dcoord (F j) x i := by
  unfold dcoord
  rw [fderiv_sum (fun j hj => (hd j hj).const_mul (A j))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fderiv_const_mul (hd j hj)]
  rfl

theorem second_sum (s : Finset κ) (F : κ → Space → ℂ) (A : κ → ℂ) (x : Space) (i a : Fin 3)
    (hf : ∀ j ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F j)) :
    dcoord (fun y => dcoord (fun z => ∑ j ∈ s, A j*F j z) y i) x a=
      ∑ j ∈ s, A j*dcoord (fun z => dcoord (F j) z i) x a := by
  rw [show (fun y => dcoord (fun z => ∑ j ∈ s, A j*F j z) y i)=
      (fun y => ∑ j ∈ s, A j*dcoord (F j) y i) from
    funext (fun y => partial_sum s F A y i (fun j hj => (hf j hj).contDiffAt.differentiableAt (by simp)))]
  exact partial_sum s _ A x a (fun j hj =>
    (partial_smooth (hf j hj).contDiffAt i).differentiableAt (by simp))

theorem laplacian_sum (s : Finset κ) (F : κ → Space → ℂ) (A : κ → ℂ) (x : Space)
    (hf : ∀ j ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F j)) :
    laplacian (fun y => ∑ j ∈ s, A j*F j y) x=∑ j ∈ s, A j*laplacian (F j) x := by
  unfold laplacian
  simp only [second_sum s F A x _ _ hf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (Finset.mul_sum _ _ _).symm

theorem jet_sum (s : Finset κ) (F : κ → Space → ℂ) (A : κ → ℂ) (p : ι → Space)
    (hf : ∀ j ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F j)) :
    SymmetricScalarJets.jet (fun y => ∑ j ∈ s, A j*F j y) p=
      ∑ j ∈ s, A j • SymmetricScalarJets.jet (F j) p := by
  funext q
  rcases q with ⟨l,n⟩
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  fin_cases n <;> dsimp only [SymmetricScalarJets.jet]
  all_goals try rw [second_sum s F A _ _ _ hf]
  all_goals try rw [partial_sum s F A _ _ (fun j hj => (hf j hj).contDiffAt.differentiableAt (by simp))]

end OQ14.ScalarFiniteCalculus
#print axioms OQ14.ScalarFiniteCalculus.partial_sum
#print axioms OQ14.ScalarFiniteCalculus.second_sum
#print axioms OQ14.ScalarFiniteCalculus.laplacian_sum
#print axioms OQ14.ScalarFiniteCalculus.jet_sum
