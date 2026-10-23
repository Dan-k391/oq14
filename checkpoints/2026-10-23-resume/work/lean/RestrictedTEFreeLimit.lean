import RestrictedTESourceMass
import RestrictedTETrialLimit

/-! Actual harmonic finite-ball inverse free flux has its whole-plane static coherent limit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEFreeLimit
open MeasureTheory Metric Set Filter PlaneSourceKernel MaxwellRadiation SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_inverse_to_static (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0) (hγ : 0<γ)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|) (A : Index →₀ ℂ) :
    let S := RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A
    Tendsto (fun a : ℝ => ∫ q : Plane, ‖freeFlux (S a) ((a : ℂ)⁻¹ • A) q-
      staticMixed (S a) ((a : ℂ)⁻¹ • A) q‖) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,hC,M,hM,η,hη,hest⟩ := RestrictedTESourceMass.mass_and_gap p ρ χ δ R b γ hρ hχ hδ hb hsep hi hh A
  have hg : ∀ᶠ a : ℝ in 𝓝[>] 0,
      Admissible R (γ*a) (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a) ∧
      sourceMass (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a)≤M*a^2 := by
    have hn : ∀ᶠ a : ℝ in 𝓝[>] 0, a<η := nhdsWithin_le_nhds (gt_mem_nhds hη)
    filter_upwards [hn,self_mem_nhdsWithin] with a had ha
    have he := hest a ha had
    exact ⟨he.1,he.2.2.1⟩
  exact RestrictedTETrialLimit.trial_to_static A R γ M hR hγ hM _
    (hg.mono (fun _ h => h.1)) (hg.mono (fun _ h => h.2))

end OQ14.RestrictedTEFreeLimit
#print axioms OQ14.RestrictedTEFreeLimit.actual_inverse_to_static
