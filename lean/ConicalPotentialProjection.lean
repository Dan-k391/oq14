import ConicalPotentialGraph
import ConicalTangentialDivergence

/-! Actual radial and tangential projection dualities for the constructed Maxwell potential. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ConicalPotentialProjection
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalPotentialGraph
  OQ14.ConicalRadialDivergence OQ14.ConicalTangentialDivergence
open scoped Topology

abbrev Space := Maxwell.Space

private theorem test_zero_outer (p : Data) (ζ : ℝ → ℝ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) p.cutoff.rIn) (x : Space) (hx : x ∉ ball (0 : Space) p.cutoff.rIn) :
    ζ ‖x‖=0 ∧ deriv ζ ‖x‖=0 := by
  have hn : ‖x‖ ∉ tsupport ζ := by
    intro h
    exact hx (by simpa only [mem_ball,dist_zero_right] using (hs h).2)
  refine ⟨image_eq_zero_of_nmem_tsupport hn,?_⟩
  by_contra h
  exact hn (support_deriv_subset h)

private theorem gradient_pair (p : Data) (k : ℝ) (i : Fin 3) (f : Space → ℂ)
    (hz : ∀ x ∉ ball (0 : Space) p.cutoff.rIn, f x=0) :
    (∫ x : Space, gradient p k i x*f x)=
      ∫ x : Space, (ConicalSpatialMaxwell.electric p k x i-ConicalPotentialSplit.correction p k x i)*f x := by
  apply integral_congr_ae
  filter_upwards [gradient_ae p k i] with x hx
  rw [hx]
  by_cases hi : x ∈ ball (0 : Space) p.cutoff.rIn
  · have hb := bump_inner p x hi
    rw [hb.1,hb.2 i,one_mul,zero_mul,add_zero]
  · rw [hz x hi,mul_zero,mul_zero]

private theorem value_pair (p : Data) (k : ℝ) (f : Space → ℂ)
    (hz : ∀ x ∉ ball (0 : Space) p.cutoff.rIn, f x=0) :
    (∫ x : Space, value p k x*f x)=∫ x : Space, ConicalPotentialSplit.potential p k x*f x := by
  apply integral_congr_ae
  filter_upwards [value_ae p k] with x hx
  rw [hx]
  by_cases hi : x ∈ ball (0 : Space) p.cutoff.rIn
  · rw [(bump_inner p x hi).1,one_mul]
  · rw [hz x hi,mul_zero,mul_zero]

theorem actual_radial_potential_pairing (p : Data) (k : ℝ)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) p.cutoff.rIn) :
    (∑ i : Fin 3, ∫ x : Space,
      (ConicalSpatialMaxwell.electric p k x i-ConicalPotentialSplit.correction p k x i)*
        (radialField ζ p.eigenvalue p.contrast p.threshold x i : ℂ))+
      (∫ x : Space, ConicalPotentialSplit.potential p k x*
        (radialDivergence ζ p.eigenvalue p.contrast p.threshold x : ℂ))=0 := by
  have h := radial_gradient_pairing p.eigenvalue p.contrast p.threshold p.eigenvalue_bounds
    p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc (fun h => (hs h).1.false)
    (value p k) (gradient p k) (hasWeakPartial p k)
  have hF (i : Fin 3) : (∫ x : Space, gradient p k i x*(radialField ζ p.eigenvalue p.contrast p.threshold x i : ℂ))=
      ∫ x : Space, (ConicalSpatialMaxwell.electric p k x i-ConicalPotentialSplit.correction p k x i)*
        (radialField ζ p.eigenvalue p.contrast p.threshold x i : ℂ) := by
    apply gradient_pair
    intro x hx
    simp only [radialField,(test_zero_outer p ζ hs x hx).1,zero_mul,mul_zero,Complex.ofReal_zero]
  have hD : (∫ x : Space, value p k x*(radialDivergence ζ p.eigenvalue p.contrast p.threshold x : ℂ))=
      ∫ x : Space, ConicalPotentialSplit.potential p k x*(radialDivergence ζ p.eigenvalue p.contrast p.threshold x : ℂ) := by
    apply value_pair
    intro x hx
    have hz := test_zero_outer p ζ hs x hx
    simp only [radialDivergence,hz.1,hz.2,mul_zero,zero_add,Complex.ofReal_zero]
  simpa only [hF,hD] using h

theorem actual_tangent_potential_pairing (p : Data) (k : ℝ)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) p.cutoff.rIn) :
    (∑ i : Fin 3, ∫ x : Space,
      (ConicalSpatialMaxwell.electric p k x i-ConicalPotentialSplit.correction p k x i)*
        (tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ))+
      (∫ x : Space, ConicalPotentialSplit.potential p k x*
        (tangentDivergence ζ p.eigenvalue p.contrast p.threshold x : ℂ))=0 := by
  have h := tangent_gradient_pairing p.eigenvalue p.contrast p.threshold p.eigenvalue_bounds
    p.contrast_nonnegative p.threshold_pos p.threshold_lt_one p.angular_root ζ hζ hc (fun h => (hs h).1.false)
    (value p k) (gradient p k) (hasWeakPartial p k)
  have hF (i : Fin 3) : (∫ x : Space, gradient p k i x*(tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ))=
      ∫ x : Space, (ConicalSpatialMaxwell.electric p k x i-ConicalPotentialSplit.correction p k x i)*
        (tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ) := by
    apply gradient_pair
    intro x hx
    simp only [tangentField,(test_zero_outer p ζ hs x hx).1,zero_mul,Complex.ofReal_zero]
  have hD : (∫ x : Space, value p k x*(tangentDivergence ζ p.eigenvalue p.contrast p.threshold x : ℂ))=
      ∫ x : Space, ConicalPotentialSplit.potential p k x*(tangentDivergence ζ p.eigenvalue p.contrast p.threshold x : ℂ) := by
    apply value_pair
    intro x hx
    simp only [tangentDivergence,(test_zero_outer p ζ hs x hx).1,mul_zero,zero_mul,Complex.ofReal_zero]
  simpa only [hF,hD] using h

end OQ14.ConicalPotentialProjection

#print axioms OQ14.ConicalPotentialProjection.actual_radial_potential_pairing
#print axioms OQ14.ConicalPotentialProjection.actual_tangent_potential_pairing
