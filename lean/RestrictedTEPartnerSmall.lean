import RestrictedTEPartnerBalls
import SmallParityInclusions

/-! Explicit smallness of the parity perturbation of the doubled (partner-ball) device for small balls:
the hypothesis `ParityReactionVolume.perturbationBound d 1 (q^n) < 1` of
`SourcePairedParityClosure.paired_shell_solutions_tendsto_parity_of_small`, with gain `b/a`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEPartnerSmall
open MeasureTheory Metric Set
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For all sufficiently small `a`, the parity perturbation of the doubled device with gain `b/a` is below `1/2`. -/
theorem partner_perturbation_small (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0<ρ) (hχ : 0≤χ) (hb : 0<b)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) :
    ∃ δ0 : ℝ, 0<δ0 ∧ ∀ (a : ℝ) (ha : 0<a) (ha1 : a≤1), a<δ0 →
      ParityReactionVolume.perturbationBound
        (RestrictedTEPartnerBalls.partnerData p ρ χ R hρ hχ hi a ha ha1) 1 (b/a)<1/2 := by
  let V : ℝ := (Fintype.card (ι ⊕ ι) : ℝ)*ρ^3*(Real.pi*4/3)
  obtain ⟨δ, hδ, hh⟩ := SmallParityInclusions.smallness_radius χ V 1 R b
  refine ⟨δ, hδ, fun a ha ha1 hlt => ?_⟩
  have hr : ∀ j : ι ⊕ ι, RestrictedTEPartnerBalls.partnerRadius (fun _ : ι => ρ*a) j=ρ*a := fun j => by
    rcases j <;> rfl
  have hv : volume.real (RestrictedTEPartnerBalls.partnerData p ρ χ R hρ hχ hi a ha ha1).carrier≤V*a^3 := by
    show volume.real (⋃ j, ball (RestrictedTEPartnerBalls.partnerCentre (p a) j)
      (RestrictedTEPartnerBalls.partnerRadius (fun _ : ι => ρ*a) j))≤_
    refine (DynamicSupportVolume.finite_ball_volume _ _ (fun j => by
      rw [hr j]
      exact mul_nonneg hρ.le ha.le)).trans_eq ?_
    simp only [hr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold V
    ring
  exact (SmallParityInclusions.scaled_perturbation_bound
    (RestrictedTEPartnerBalls.partnerData p ρ χ R hρ hχ hi a ha ha1) 1 b a χ V ha hb.ne' hχ le_rfl hv).trans_lt
    (hh a (by rwa [abs_of_pos ha]))

end OQ14.RestrictedTEPartnerSmall
#print axioms OQ14.RestrictedTEPartnerSmall.partner_perturbation_small
