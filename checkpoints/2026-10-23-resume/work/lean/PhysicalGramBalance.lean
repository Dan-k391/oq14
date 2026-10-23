import RestrictedTEOrthogonalKernel
import HermitianGramCompletion

/-! Exact physical incoming Gram balancing by actual finite null-jet corrections. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PhysicalGramBalance
open Complex Maxwell Matrix RestrictedTEInputJets
open scoped ComplexInnerProductSpace ComplexConjugate
abbrev Space := FourierL2.Space

def gram {n : ℕ} (v : Fin n → IncomingSpace) : Matrix (Fin n) (Fin n) ℂ := fun i j => ⟪v i,v j⟫

theorem gram_hermitian {n : ℕ} (v : Fin n → IncomingSpace) : (gram v).IsHermitian := by
  ext i j
  change conj (⟪v j,v i⟫ : ℂ)=⟪v i,v j⟫
  exact inner_conj_symm (𝕜 := ℂ) (v i) (v j)

theorem balance {ι : Type*} [Fintype ι] (p : ι → Space) (n : ℕ) (v : Fin n → IncomingSpace) :
    ∃ scale : ℝ, 0<scale ∧ ∃ u : Fin n → IncomingSpace,
      (∀ j, toJet p (u j)=toJet p (v j)) ∧
      (∀ i j, ⟪u i,u j⟫=(scale : ℂ)*(if i=j then 1 else 0)) := by
  classical
  obtain ⟨w,hw,hJ,hO⟩ := RestrictedTEOrthogonalKernel.orthogonal_null_jets p n v
  obtain ⟨scale,hscale,B,hB⟩ := HermitianGramCompletion.completion (gram v) (gram_hermitian v)
  let c : Fin n → IncomingSpace := fun j => ∑ k : Fin n, B k j • w k
  have hvC (i j : Fin n) : ⟪v i,c j⟫=0 := by
    simp [c,inner_sum,inner_smul_right,hO]
  have hCv (i j : Fin n) : ⟪c i,v j⟫=0 := by
    rw [← inner_conj_symm,hvC]
    simp
  have hCC (i j : Fin n) : ⟪c i,c j⟫=(Bᴴ*B) i j := by
    have hw' := orthonormal_iff_ite.mp hw
    simp [c,inner_sum,sum_inner,inner_smul_left,inner_smul_right,hw',Matrix.mul_apply,mul_comm]
  refine ⟨scale,hscale,(fun j => v j+c j),?_,?_⟩
  · intro j
    simp [c,map_add,map_sum,map_smul,hJ]
  · intro i j
    rw [inner_add_left,inner_add_right,inner_add_right,hvC,hCv,hCC,hB]
    simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,gram]
    ring

end OQ14.PhysicalGramBalance
#print axioms OQ14.PhysicalGramBalance.gram_hermitian
#print axioms OQ14.PhysicalGramBalance.balance
