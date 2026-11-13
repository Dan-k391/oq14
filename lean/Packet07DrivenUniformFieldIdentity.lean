import Packet07DrivenUniformFields
import Packet07IncidentScalarEquation

/-! The named driven scalar and correction recover the literal total field. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenUniformFieldIdentity
open MeasureTheory Metric Set Maxwell WeakCurl WeakPoynting DivCurlCompact ConicalGradientGraph Packet07DrivenUniformFields
abbrev Space := Maxwell.Space

theorem actual_field_identity {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k : ℝ) (hk0 : k ≠ 0)
    (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing) (j : ℕ) :
    ∀ l, ∀ᵐ x ∂volume, x ∈ ball (0 : Space) (Packet07DrivenUniformAtlas.outer g).rIn →
      gradient (Packet07DrivenUniformAtlas.outer g) (potential g k input j) l x +
      Packet06ScalarGaussLocalization.correction (Packet07DrivenUniformAtlas.outer g)
        (correction g k input j) (correction_continuous g k input j) l x = g.electric k j input x l := by
  have hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (g.rounded j) g.enclosing :=
    hk.trans (MaterialVolumeLimit.commonRadius_le (g.rounded j) d g.enclosing le_rfl)
  have h := Packet07IncidentScalarEquation.actual_incident_scalar_equation (g.rounded j) k g.enclosing hk0
    g.enclosing_nonnegative hfreq (FiniteAngularHerglotz.incident k input) (support g j) (Packet07DrivenUniformAtlas.outer g)
  obtain ⟨hW,_,_,_,hE,_⟩ := h
  exact hE
end OQ14.Packet07DrivenUniformFieldIdentity
#print axioms OQ14.Packet07DrivenUniformFieldIdentity.actual_field_identity
