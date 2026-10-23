import RestrictedTEKernel
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-! Genuine physical orthonormal null-jet corrections, orthogonal to prescribed inputs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEOrthogonalKernel
open Maxwell RestrictedTEInputJets
open scoped ComplexInnerProductSpace
abbrev Space := FourierL2.Space

theorem kernel_not_finite {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (f : IncomingSpace →ₗ[ℂ] W) : ¬FiniteDimensional ℂ (LinearMap.ker f) := by
  intro h
  letI := h
  letI : FiniteDimensional ℂ (IncomingSpace ⧸ LinearMap.ker f) :=
    FiniteDimensional.of_injective f.quotKerEquivRange.toLinearMap f.quotKerEquivRange.injective
  exact RestrictedTEKernel.incoming_not_finite (Module.Finite.of_submodule_quotient (LinearMap.ker f))

theorem orthonormal_of_not_finite {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (hV : ¬FiniteDimensional ℂ V) (n : ℕ) : ∃ w : Fin n → V, Orthonormal ℂ w := by
  classical
  let b := Basis.ofVectorSpace ℂ V
  have hi : Infinite (Basis.ofVectorSpaceIndex ℂ V) := by
    by_contra h
    haveI := not_infinite_iff_finite.mp h
    exact hV (FiniteDimensional.of_fintype_basis b)
  letI := hi
  let e : Fin n ↪ Basis.ofVectorSpaceIndex ℂ V :=
    (⟨Fin.val,Fin.val_injective⟩ : Fin n ↪ ℕ).trans (Infinite.natEmbedding _)
  have hl : LinearIndependent ℂ (fun j : Fin n => b (e j)) := b.linearIndependent.comp _ e.injective
  exact ⟨gramSchmidtNormed ℂ (fun j : Fin n => b (e j)),gramSchmidt_orthonormal hl⟩

def orthogonalityMap {n : ℕ} (v : Fin n → IncomingSpace) : IncomingSpace →ₗ[ℂ] (Fin n → ℂ) :=
  (ContinuousLinearMap.pi (fun i => innerSL ℂ (v i))).toLinearMap

theorem orthogonal_null_jets {ι : Type*} [Fintype ι] (p : ι → Space) (n : ℕ)
    (v : Fin n → IncomingSpace) :
    ∃ w : Fin n → IncomingSpace, Orthonormal ℂ w ∧ (∀ j, toJet p (w j)=0) ∧
      (∀ i j, ⟪v i,w j⟫=0) := by
  let f := (toJet p).prod (orthogonalityMap v)
  obtain ⟨w,hw⟩ := orthonormal_of_not_finite (V := LinearMap.ker f) (kernel_not_finite f) n
  refine ⟨fun j => (w j : IncomingSpace),hw.comp_linearIsometry (LinearMap.ker f).subtypeₗᵢ,?_,?_⟩
  · intro j
    have h := congrArg Prod.fst (w j).property
    exact h
  · intro i j
    have h := congrFun (congrArg Prod.snd (w j).property) i
    exact h

end OQ14.RestrictedTEOrthogonalKernel
#print axioms OQ14.RestrictedTEOrthogonalKernel.kernel_not_finite
#print axioms OQ14.RestrictedTEOrthogonalKernel.orthonormal_of_not_finite
#print axioms OQ14.RestrictedTEOrthogonalKernel.orthogonal_null_jets
