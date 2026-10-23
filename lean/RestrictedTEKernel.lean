import RestrictedTEInputJets
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Finiteness.Finsupp

/-! Arbitrarily many actual edge jets force an infinite physical TE kernel. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEKernel
open Maxwell RestrictedTEInputJets
abbrev Space := FourierL2.Space

def point (r y : ℝ) : Space := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![r,y,0]
def grid (n : ℕ) (j : Fin n) : Space := point 1 (j.val : ℝ)

theorem grid_surjective (n : ℕ) : Function.Surjective (toJet (grid n)) := by
  have hy : Function.Injective (fun j : Fin n => (j.val : ℝ)) := by
    intro i j h
    change (i.val : ℝ)=(j.val : ℝ) at h
    apply Fin.ext
    exact_mod_cast h
  exact RestrictedTEInputJets.surjective 1 one_ne_zero (fun j : Fin n => (j.val : ℝ)) hy (grid n)
    (fun j => rfl) (fun j => rfl) (fun j => rfl)

theorem incoming_not_finite : ¬FiniteDimensional ℂ IncomingSpace := by
  intro h
  letI := h
  let d := Module.finrank ℂ IncomingSpace
  have hd := LinearMap.finrank_range_le (toJet (grid (d+1)))
  rw [LinearMap.range_eq_top.mpr (grid_surjective (d+1))] at hd
  have he : Module.finrank ℂ (RestrictedTEJetMap.Jet (Fin (d+1)))=(d+1)*3 := by
    simp [RestrictedTEJetMap.Jet,Module.finrank_pi,Fintype.card_prod]
  have ht : Module.finrank ℂ (⊤ : Submodule ℂ (RestrictedTEJetMap.Jet (Fin (d+1)) ))=
      Module.finrank ℂ (RestrictedTEJetMap.Jet (Fin (d+1))) := (LinearEquiv.ofTop _ rfl).finrank_eq
  rw [ht,he] at hd
  change (d+1)*3≤d at hd
  omega

theorem kernel_not_finite {ι : Type*} [Fintype ι] (p : ι → Space) :
    ¬FiniteDimensional ℂ (LinearMap.ker (toJet p)) := by
  intro h
  letI := h
  letI : FiniteDimensional ℂ (IncomingSpace ⧸ LinearMap.ker (toJet p)) :=
    FiniteDimensional.of_injective (toJet p).quotKerEquivRange.toLinearMap
      (toJet p).quotKerEquivRange.injective
  exact incoming_not_finite (Module.Finite.of_submodule_quotient (LinearMap.ker (toJet p)))

end OQ14.RestrictedTEKernel
#print axioms OQ14.RestrictedTEKernel.grid_surjective
#print axioms OQ14.RestrictedTEKernel.incoming_not_finite
#print axioms OQ14.RestrictedTEKernel.kernel_not_finite
