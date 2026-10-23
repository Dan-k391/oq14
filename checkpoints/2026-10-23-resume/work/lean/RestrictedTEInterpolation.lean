import RestrictedTEFields
import EdgeTEJets

/-! Actual finite restricted TE fields interpolate electric and magnetic edge data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEInterpolation
open Maxwell RestrictedTEFields
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

theorem interpolate (k : ℝ) (hk : 0<k) (r : ℝ) (hr : r≠0)
    (y : ι → ℝ) (hy : Function.Injective y) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0)
    (v : (ι × Fin 3) → ℂ) :
    ∃ A : SymmetricHarmonicJets.Index →₀ ℂ,
      (∀ x, MaxwellAt k 1 1 (DebyeMaxwell.teElectric (potential k A))
        (DebyeMaxwell.teMagnetic k (potential k A)) x) ∧
      HalfTurnMaxwellParity.Invariant (DebyeMaxwell.teElectric (potential k A)) ∧
      (∀ j, DebyeMaxwell.teElectric (potential k A) (p j) 2=v (j,0) ∧
        DebyeMaxwell.teMagnetic k (potential k A) (p j) 0=v (j,1) ∧
        DebyeMaxwell.teMagnetic k (potential k A) (p j) 1=v (j,2)) := by
  obtain ⟨A,hA⟩ := RestrictedHarmonicInterpolation.finite_scalar_interpolant k hk r hr y hy p h0 h1 h2
    (EdgeTEJets.scalarTarget k r y v)
  refine ⟨A,maxwell k hk.ne' A,electric_half_turn k A,?_⟩
  exact EdgeTEJets.realizes (potential k A) (potential_smooth k A) k r hk.ne' hr y p h0 h1 h2
    (potential_helmholtz k A) v hA

end OQ14.RestrictedTEInterpolation
#print axioms OQ14.RestrictedTEInterpolation.interpolate
