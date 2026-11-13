import Packet07CorridorEventually

/-! Radial monotonicity of the actual smooth corner function. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.Packet07RadialMonotone
open Set

theorem radial_strictAnti (n : ℕ) (m a z r : ℝ)
    (hm : 0 < m) (hs : 0 < z-m*r)
    (ht : 0 < a^2-r^2-z^2) :
    StrictAntiOn (ConicalJunctionRadial.radialDef n m a z) (Icc 0 r) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 r)
  · apply Continuous.continuousOn
    unfold ConicalJunctionRadial.radialDef ConicalSmoothJunction.cornerDef ConicalSmoothJunction.correction
    have hc : Continuous Real.smoothTransition := (Real.smoothTransition.contDiff : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition).continuous
    fun_prop
  · intro x hx
    have hx' : x ∈ Icc 0 r := interior_subset hx
    have hxm : m*x ≤ m*r := mul_le_mul_of_nonneg_left hx'.2 hm.le
    have hx2 : x^2 ≤ r^2 := pow_le_pow_left₀ hx'.1 hx'.2 2
    apply ConicalJunctionRadial.radial_deriv_negative n m a z x hm hx'.1 <;> nlinarith

/-- An admissible radial junction remains admissible when its radius decreases. -/
theorem radial_positive_inward (n : ℕ) (m a z r q : ℝ)
    (hm : 0 < m) (hq : 0 ≤ q) (hqr : q ≤ r)
    (hs : 0 < z-m*r) (ht : 0 < a^2-r^2-z^2)
    (hcorner : 0 < ConicalJunctionRadial.radialDef n m a z r) :
    0 < ConicalJunctionRadial.radialDef n m a z q := by
  by_cases h : q = r
  · simpa [h] using hcorner
  · have hlt : q < r := lt_of_le_of_ne hqr h
    have ha := radial_strictAnti n m a z r hm hs ht
    have h0 : 0 ≤ r := le_trans hq hqr
    have hle := ha ⟨hq,hqr⟩ ⟨h0,le_rfl⟩ hlt
    exact lt_trans hcorner hle
/-- At fixed height outside the smoothed tip, reducing transverse radius
    preserves membership in the actual rounded inclusion. -/
theorem inclusion_inward (n : ℕ) (m a z : ℝ)
    (u v : ConicalSmoothCapGraph.Plane) (hm : 0 < m)
    (hz : 0 ≤ z) (hv : 2*ConicalTipRounding.radius n ≤ ‖v‖)
    (hvu : ‖v‖ ≤ ‖u‖)
    (hu : (u,z) ∈ ConicalSmoothJunction.inclusion n m a) :
    (v,z) ∈ ConicalSmoothJunction.inclusion n m a := by
  have he : 0 < ConicalTipRounding.radius n := ConicalTipRounding.radius_positive n
  have hcu := ConicalSmoothCapGraph.cap_matches n m hm u (by linarith)
  have hcv := ConicalSmoothCapGraph.cap_matches n m hm v hv
  have hs : 0 < z-m*‖u‖ := by
    simpa [ConicalSmoothJunction.coneMargin, hcu, abs_of_nonneg hz] using hu.1
  have ht : 0 < a^2-‖u‖^2-z^2 := hu.2.1
  have hcorner : 0 < ConicalJunctionRadial.radialDef n m a z ‖u‖ := by
    have hh := hu.2.2
    simp only [ConicalSmoothJunction.coneMargin, ConicalSmoothJunction.ballMargin,
      Prod.fst, Prod.snd, hcu, abs_of_nonneg hz] at hh
    unfold ConicalJunctionRadial.radialDef ConicalSmoothJunction.cornerDef
    linarith
  have hc := radial_positive_inward n m a z ‖u‖ ‖v‖ hm (norm_nonneg v) hvu hs ht hcorner
  have hmv : m*‖v‖ ≤ m*‖u‖ := mul_le_mul_of_nonneg_left hvu hm.le
  have hv2 : ‖v‖^2 ≤ ‖u‖^2 := pow_le_pow_left₀ (norm_nonneg v) hvu 2
  have hsv : 0 < z-m*‖v‖ := by linarith
  have htv : 0 < a^2-‖v‖^2-z^2 := by linarith
  refine ⟨?_,?_,?_⟩
  · simpa [ConicalSmoothJunction.coneMargin, hcv, abs_of_nonneg hz] using hsv
  · exact htv
  · unfold ConicalJunctionRadial.radialDef ConicalSmoothJunction.cornerDef at hc
    simp only [ConicalSmoothJunction.coneMargin, ConicalSmoothJunction.ballMargin,
      Prod.fst, Prod.snd, hcv, abs_of_nonneg hz]
    linarith
end OQ14.Packet07RadialMonotone
#print axioms OQ14.Packet07RadialMonotone.radial_strictAnti
#print axioms OQ14.Packet07RadialMonotone.radial_positive_inward
#print axioms OQ14.Packet07RadialMonotone.inclusion_inward
