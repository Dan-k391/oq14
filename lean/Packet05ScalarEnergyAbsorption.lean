import Packet05ScalarTransmissionFlux

/-! Absorption of the three terms in the localized scalar elliptic energy
identity; the hypotheses are the explicit pre-absorption estimate. -/
noncomputable section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace OQ14.Packet05ScalarEnergyAbsorption

theorem absorb_scalar_cutoff_energy (lambda Lambda a b d : ℝ)
    (hl : 0 < lambda)
    (h : lambda*a^2 ≤ 2*Lambda*a*b + d*a + 2*d*b) :
    (lambda/2)*a^2 ≤ (4*Lambda^2/lambda+1)*b^2 + (1/lambda+1)*d^2 := by
  have h1 : 2*Lambda*a*b ≤ (lambda/4)*a^2 + (4*Lambda^2/lambda)*b^2 := by
    calc
      2*Lambda*a*b ≤ ((lambda*a)^2 + (4*Lambda*b)^2) / (4*lambda) := by
        apply (le_div_iff₀ (by positivity : 0 < 4*lambda)).2
        nlinarith [sq_nonneg (lambda*a - 4*Lambda*b)]
      _ = (lambda/4)*a^2 + (4*Lambda^2/lambda)*b^2 := by
        field_simp
        <;> ring
  have h2 : d*a ≤ (lambda/4)*a^2 + d^2/lambda := by
    calc
      d*a ≤ ((lambda*a)^2 + (2*d)^2) / (4*lambda) := by
        apply (le_div_iff₀ (by positivity : 0 < 4*lambda)).2
        nlinarith [sq_nonneg (lambda*a - 2*d)]
      _ = (lambda/4)*a^2 + d^2/lambda := by
        field_simp
        <;> ring
  have h3 : 2*d*b ≤ d^2+b^2 := by nlinarith [sq_nonneg (d-b)]
  ring_nf at h h1 h2 h3 ⊢
  linarith

end OQ14.Packet05ScalarEnergyAbsorption
#print axioms OQ14.Packet05ScalarEnergyAbsorption.absorb_scalar_cutoff_energy
