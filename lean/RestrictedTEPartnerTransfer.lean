import RestrictedTEPartnerSmallness
import RestrictedTEEvenDatum
import SourcePairedParityClosure

/-! Closure of the finite paired-shell effective solutions onto the doubled parity device.

Parameter matching.  Fix `q > 1`, the physical device data `p ρ χ R hρ hχ hi` of the doubled (partner-ball)
device, an enclosing radius `b ≥ R` of the closure, and a finite restricted TE coefficient vector `A`.  For
`n : ℕ` take the device at scale `a_n = (q^n)⁻¹` (`RestrictedTEPartnerSmallness.scale`, so `a_n ≤ 1`,
`a_n → 0`): the coefficient `deviceCoeff n = partnerCoefficient (p a_n) (fun _ => ρ a_n) χ hχ`, its support data
`deviceData n = partnerData p ρ χ R hρ hχ hi a_n _ _` (carrier in the ball of radius `R ≤ b`, independent of `n`)
and the datum `f_n = RestrictedTEMaterial.datum (deviceCoeff n) (deviceData n) A`.  The parity gain of the closure
is `q^n = 1 / a_n` (`RestrictedTEPartnerSmallness.scale_gain`), which is the gain `b_device / a` of
`RestrictedTEPartnerSmall.partner_perturbation_small` with `b_device = 1` and `a = a_n`.  The closure radius `b`
(enclosing the carrier) and the device gain constant `b_device = 1` are different parameters. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEPartnerTransfer
open Filter Topology OQ14.ShellInclusionReaction OQ14.SourcePairedInclusion OQ14.SourcePairedReduction
open OQ14.RestrictedTEPartnerSmallness
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For large `n` the parity perturbation of the doubled device at scale `a_n = (q^n)⁻¹` with gain `q^n` is below
`1/2`. -/
theorem partner_parity_small (p : ℝ → ι → Space) (ρ χ R : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop,
      ParityReactionVolume.perturbationBound (deviceData p ρ χ R hρ hχ hi q hq n) 1 (q^n) < 1/2 := by
  obtain ⟨δ0, hδ0, h⟩ := RestrictedTEPartnerSmall.partner_perturbation_small p ρ χ R 1 hρ hχ one_pos hi
  filter_upwards [(scale_tendsto hq).eventually (gt_mem_nhds hδ0)] with n hn
  have h1 := h (scale q n) (scale_pos hq n) (scale_le_one hq.le n) hn
  rw [scale_gain n] at h1
  exact h1

/-- Closure onto the doubled parity device: for every fixed `q > 1`, every enclosing radius `b ≥ R` and every finite
restricted TE coefficient vector `A`, for all large `n` the effective inclusion solutions of the actual paired
shells (shell index `r → ∞`) with the doubled device at scale `a_n = (q^n)⁻¹` converge in vector L2 to the explicit
parity material solution with gain `q^n` of the half-turn fixed datum. -/
theorem partner_shell_solutions_tendsto (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hb : 0 < b) (hRb : R ≤ b) (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R) (q : ℝ) (hq : 1 < q)
    (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    ∀ᶠ n : ℕ in atTop,
      Tendsto (fun r : ℕ => Ring.inverse (DynamicVolume.volumeBlock (deviceCoeff p ρ χ hχ q n) 1 b -
          reaction (shell q hq.le n r) (deviceCoeff p ρ χ hχ q n) 1
            (data q hq.le n r).X)
          (RestrictedTEMaterial.datum (deviceCoeff p ρ χ hχ q n) (deviceData p ρ χ R hρ hχ hi q hq n) A))
        atTop
        (𝓝 (ParityMaterialField.solution (deviceData p ρ χ R hρ hχ hi q hq n) 1 (q^n)
          (RestrictedTEMaterial.datum (deviceCoeff p ρ χ hχ q n) (deviceData p ρ χ R hρ hχ hi q hq n) A))) := by
  filter_upwards [partner_limitEffective_isUnit p ρ χ R b hρ hχ hb hRb hi q hq,
    partner_parity_small p ρ χ R hρ hχ hi q hq] with n hL hpar
  have hin : ∀ l, ‖p (scale q n) l‖+ρ*scale q n ≤ R := fun l =>
    (add_le_add_left (mul_le_of_le_one_right hρ.le (scale_le_one hq.le n)) _).trans
      (hi (scale q n) (scale_pos hq n) (scale_le_one hq.le n) l)
  exact SourcePairedParityClosure.paired_shell_solutions_tendsto_parity q hq.le n
    (deviceCoeff p ρ χ hχ q n) (deviceData p ρ χ R hρ hχ hi q hq n) b hb
    (fun x hx => (RestrictedTEPartnerBalls.partner_carrier_norm (p (scale q n)) (fun _ : ι => ρ*scale q n)
      χ hχ R hin x hx).trans hRb)
    (RestrictedTEPartnerBalls.partner_symmetric (p (scale q n)) (fun _ : ι => ρ*scale q n) χ hχ)
    hL
    (ParityReactionVolume.explicitBlock_isUnit _ 1 (q^n) (hpar.trans (by norm_num)))
    (RestrictedTEMaterial.datum (deviceCoeff p ρ χ hχ q n) (deviceData p ρ χ R hρ hχ hi q hq n) A)
    (RestrictedTEEvenDatum.partner_datum_fixed (p (scale q n)) (fun _ : ι => ρ*scale q n) χ hχ R hin A)

end OQ14.RestrictedTEPartnerTransfer
#print axioms OQ14.RestrictedTEPartnerTransfer.partner_parity_small
#print axioms OQ14.RestrictedTEPartnerTransfer.partner_shell_solutions_tendsto
