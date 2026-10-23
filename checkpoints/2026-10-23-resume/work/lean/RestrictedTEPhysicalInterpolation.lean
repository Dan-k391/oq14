import RestrictedTEPower

/-! Actual finite restricted TE interpolation with strictly positive physical incoming power. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEPhysicalInterpolation
open Maxwell RestrictedTEFields RestrictedTEIncoming
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

theorem interpolate (r : ℝ) (hr : r≠0) (y : ι → ℝ) (hy : Function.Injective y) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0)
    (v : (ι × Fin 3) → ℂ) (hv : ∃ j : ι, ∃ n : Fin 3, v (j,n)≠0) :
    ∃ A : SymmetricHarmonicJets.Index →₀ ℂ,
      (∀ x, MaxwellAt 1 1 1 (DebyeMaxwell.teElectric (potential 1 A))
        (DebyeMaxwell.teMagnetic 1 (potential 1 A)) x) ∧
      HalfTurnMaxwellParity.Invariant (DebyeMaxwell.teElectric (potential 1 A)) ∧
      (∀ j, DebyeMaxwell.teElectric (potential 1 A) (p j) 2=v (j,0) ∧
        DebyeMaxwell.teMagnetic 1 (potential 1 A) (p j) 0=v (j,1) ∧
        DebyeMaxwell.teMagnetic 1 (potential 1 A) (p j) 1=v (j,2)) ∧ 0<physicalPower A := by
  obtain ⟨A,hM,hS,hJ⟩ := RestrictedTEInterpolation.interpolate 1 (by norm_num) r hr y hy p h0 h1 h2 v
  simp only [Complex.ofReal_one] at hM hJ
  refine ⟨A,hM,hS,hJ,?_⟩
  apply RestrictedTEPower.physical_power_pos A
  obtain ⟨j,n,hn⟩ := hv
  obtain ⟨he,hh0,hh1⟩ := hJ j
  fin_cases n
  · exact ⟨p j,2,Or.inl (by rw [he]; exact hn)⟩
  · exact ⟨p j,0,Or.inr (by rw [hh0]; exact hn)⟩
  · exact ⟨p j,1,Or.inr (by rw [hh1]; exact hn)⟩

end OQ14.RestrictedTEPhysicalInterpolation
#print axioms OQ14.RestrictedTEPhysicalInterpolation.interpolate
