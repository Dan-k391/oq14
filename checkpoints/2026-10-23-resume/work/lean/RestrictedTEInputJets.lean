import RestrictedTEInput
import RestrictedTEJetMap
import Mathlib.LinearAlgebra.Isomorphisms

/-! Literal TE vector jets descend to actual physical incoming data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEInputJets
open Maxwell SymmetricHarmonicJets RestrictedTEJetMap
abbrev Space := FourierL2.Space
variable {ι : Type*}

theorem kernel_le (p : ι → Space) : LinearMap.ker RestrictedTEInput.input≤LinearMap.ker (jetMap p) := by
  intro A hA
  have hzero : RestrictedTEInput.input A=0 := hA
  obtain ⟨he,hh⟩ := RestrictedTEInput.input_zero_fields A hzero
  change jetMap p A=0
  rw [jetMap_eq]
  funext q
  rcases q with ⟨j,n⟩
  fin_cases n <;> dsimp only [fieldJet] <;> simp only [he,hh,Pi.zero_apply]

def IncomingSpace := LinearMap.range RestrictedTEInput.input

def toJet (p : ι → Space) : IncomingSpace →ₗ[ℂ] Jet ι :=
  ((LinearMap.ker RestrictedTEInput.input).liftQ (jetMap p) (kernel_le p)).comp
    RestrictedTEInput.input.quotKerEquivRange.symm.toLinearMap

theorem toJet_apply (p : ι → Space) (A : Index →₀ ℂ) :
    toJet p (RestrictedTEInput.input.rangeRestrict A)=fieldJet p A := by
  unfold toJet
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  change ((LinearMap.ker RestrictedTEInput.input).liftQ (jetMap p) (kernel_le p))
    (RestrictedTEInput.input.quotKerEquivRange.symm ⟨RestrictedTEInput.input A,⟨A,rfl⟩⟩)=_
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  change jetMap p A=fieldJet p A
  exact jetMap_eq p A

theorem surjective [Fintype ι] (r : ℝ) (hr : r≠0) (y : ι → ℝ) (hy : Function.Injective y)
    (p : ι → Space) (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0) :
    Function.Surjective (toJet p) := by
  intro v
  obtain ⟨A,hA⟩ := RestrictedTEJetMap.surjective r hr y hy p h0 h1 h2 v
  refine ⟨RestrictedTEInput.input.rangeRestrict A,?_⟩
  rw [toJet_apply,← jetMap_eq]
  exact hA

end OQ14.RestrictedTEInputJets
#print axioms OQ14.RestrictedTEInputJets.kernel_le
#print axioms OQ14.RestrictedTEInputJets.toJet_apply
#print axioms OQ14.RestrictedTEInputJets.surjective
