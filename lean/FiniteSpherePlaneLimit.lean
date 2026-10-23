import FiniteSphereActualSources
import ParityCompleteLimit

/-! Complete actual parity inverse plane flux compared to its constructed static trial. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteSpherePlaneLimit
open MeasureTheory Metric Set Filter PlaneSourceKernel MaxwellRadiation
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem actual_inverse_limit (p : ℝ → ι → Space) (ρ χ δ R k b γ T A₀ : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hδ : 0 < δ) (hb : b ≠ 0)
    (hR : 0 ≤ R) (hk : k ≠ 0) (hγ : 0 < γ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA₀ : 0 ≤ A₀)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ l n, l ≠ n → δ ≤ dist (p a l) (p a n))
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (hh : ∀ a, 0 < a → a ≤ 1 → ∀ l, (γ+ρ)*a ≤ |p a l 2|)
    (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ)
    (hq : ∀ a, 0 < a → a ≤ 1 → ∀ s, q a s ∈ closedBall 0 R)
    (hA : ∀ a, 0 < a → a ≤ 1 → (∑ s, ‖A a s‖) ≤ A₀/a) :
    let S := FiniteSphereActualSources.source p ρ χ R k b hρ hχ hi q j A
    let U := FiniteSphereActualSources.trial p ρ χ k q j A
    Tendsto (fun a => ∫ u : Plane,
      ‖ParityTotalFlux.totalFlux k (b/a) (S a) (q a) (j a) (A a) u-
        ParityTotalFlux.freeFlux k (U a) (q a) (j a) (A a) u‖) (𝓝[>] 0) (𝓝 0) := by
  let S := FiniteSphereActualSources.source p ρ χ R k b hρ hχ hi q j A
  let U := FiniteSphereActualSources.trial p ρ χ k q j A
  let C := |FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ k R b
    (SphereReactionKernel.entryBound k*A₀) (2*SphereReactionKernel.entryBound k*|k| * A₀)|
  let M := FiniteSphereQuadratic.massConstant (ι := ι) χ ρ δ k R b
    (SphereReactionKernel.entryBound k*A₀) (2*SphereReactionKernel.entryBound k*|k| * A₀)
  have hM : 0 ≤ M := by
    have hV := FiniteSphereScale.totalVolume_nonnegative (ι := ι) ρ hρ.le
    have hE := SphereReactionKernel.entryBound_nonnegative k
    dsimp [M]
    unfold FiniteSphereQuadratic.massConstant FiniteSphereSourceMass.trialConstant
    positivity
  obtain ⟨η,hη,he⟩ := FiniteSphereActualSources.mass_and_gap p ρ χ δ R k b γ T A₀
    hρ hχ hδ hb hR hk hγ hT hTR hA₀ hsep hi hh q j A hA
  have hg : ∀ᶠ a : ℝ in 𝓝[>] 0,
      Admissible R (γ*a) (S a) ∧ Admissible R (γ*a) (U a) ∧
      sourceMass (S a) ≤ M*a^2 ∧ sourceMass (U a) ≤ M*a^2 ∧ sourceMass (S a-U a) ≤ C*a^3 := by
    have hn : ∀ᶠ a : ℝ in 𝓝[>] 0, a < η := nhdsWithin_le_nhds (gt_mem_nhds hη)
    filter_upwards [hn,self_mem_nhdsWithin] with a had ha
    exact he a ha had
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a ≤ 1 :=
    (show ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 from nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)).mono (fun a ha => ha.le)
  have hq' : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ s, q a s ∈ closedBall 0 R := by
    filter_upwards [hsmall,self_mem_nhdsWithin] with a ha1 ha
    exact hq a ha ha1
  have hA' : ∀ᶠ a : ℝ in 𝓝[>] 0, (∑ s, ‖A a s‖) ≤ A₀/a := by
    filter_upwards [hsmall,self_mem_nhdsWithin] with a ha1 ha
    exact hA a ha ha1
  exact ParityCompleteLimit.total_to_trial k b R T γ C M A₀ hR hk hT hTR hγ (abs_nonneg _) hM hA₀ S U q j A
    (hg.mono (fun a ha => ha.1)) (hg.mono (fun a ha => ha.2.1)) hq'
    (hg.mono (fun a ha => ha.2.2.1)) (hg.mono (fun a ha => ha.2.2.2.1))
    (hg.mono (fun a ha => ha.2.2.2.2)) hA'

end OQ14.FiniteSpherePlaneLimit
#print axioms OQ14.FiniteSpherePlaneLimit.actual_inverse_limit
