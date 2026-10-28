import ConicalCommonResponse
import ConicalLocalPairing
import ConicalIntrinsicCoefficient

/-! Bounds needed to retain the common-material singular coefficient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalCommonRetention
open MeasureTheory Set Metric Filter OQ14.NewtonL2
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev VectorL2 := VectorFourier.VectorL2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

def staticSource (i : ι) : VectorL2 :=
  ConicalCommonBaseline.materialSource p a center B hB hcontrast ha hsep i - ConicalCommonBaseline.forcing p a center i

omit [DecidableEq ι] in
theorem source_tendsto (i : ι) (R T : ℝ) (hR : 0 ≤ R) (hRT : 0 ≤ R + T) :
    Tendsto (ConicalCommonResponse.totalSource p a center B hB hcontrast ha hsep i R T)
      (𝓝 0) (𝓝 (staticSource p a center B hB hcontrast ha hsep i)) := by
  have h := ((StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)).continuous.tendsto _).comp
    (ConicalCommonDynamic.solution_tendsto p a center B hB hcontrast ha hsep i R T hR hRT)
  simpa only [ConicalCommonResponse.totalSource, staticSource, ConicalCommonBaseline.materialSource] using h.sub tendsto_const_nhds

omit [DecidableEq ι] in
theorem source_eventually_bound (i : ι) (R T : ℝ) (hR : 0 ≤ R) (hRT : 0 ≤ R + T) :
    ∀ᶠ k : ℝ in 𝓝 0, ‖ConicalCommonResponse.totalSource p a center B hB hcontrast ha hsep i R T k‖ ≤
      ‖staticSource p a center B hB hcontrast ha hsep i‖ + 1 := by
  have ht := source_tendsto p a center B hB hcontrast ha hsep i R T hR hRT
  filter_upwards [ht.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))] with k hk
  have hd : ‖ConicalCommonResponse.totalSource p a center B hB hcontrast ha hsep i R T k -
      staticSource p a center B hB hcontrast ha hsep i‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hk
  have hn := norm_add_le (ConicalCommonResponse.totalSource p a center B hB hcontrast ha hsep i R T k -
      staticSource p a center B hB hcontrast ha hsep i) (staticSource p a center B hB hcontrast ha hsep i)
  rw [sub_add_cancel] at hn
  linarith

omit [DecidableEq ι] in
theorem correction_bound (i l : ι) (R T k b : ℝ)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T)
    (j : Fin 3) (x : Space) (hx : x ∈ closedBall (0 : Space) b) :
    ‖ConicalCommonResponse.centeredCorrection p a center B hB hcontrast ha hsep i l R T k x j‖ ≤
      k^2 * ‖ConicalCommonResponse.totalSource p a center B hB hcontrast ha hsep i R T k‖ *
        ‖ScalarPotentialBound.cutoff 0 ((max b 0 + ‖center l‖) + T)‖ := by
  have hxnorm : ‖x‖ ≤ b := by simpa using hx
  have hx' : x + center l ∈ closedBall (0 : Space) (max b 0 + ‖center l‖) := by
    simp only [mem_closedBall, dist_zero_right]
    exact (norm_add_le x (center l)).trans (add_le_add_right (hxnorm.trans (le_max_left _ _)) _)
  have h := ScalarPotentialBound.scaled_response_bound k (max b 0 + ‖center l‖) T
    (ConicalCommonResponse.source p a center B hB hcontrast ha hsep i R T k j)
    (physicalCoordinate (ConicalCommonResponse.totalSource p a center B hB hcontrast ha hsep i R T k) j)
    (ConicalCommonResponse.source_ae p a center B hB hcontrast ha hsep i R T k j)
    (ConicalCommonResponse.source_zero_outer p a center B hB hcontrast ha hsep i R T k T hT j)
    (x + center l) hx'
  have hn := DynamicConvolution.component_norm j (ConicalCommonResponse.totalSource p a center B hB hcontrast ha hsep i R T k)
  exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (sq_nonneg k)) (norm_nonneg _))

omit [DecidableEq ι] in
theorem correction_eventually_bound (i l : ι) (R T b : ℝ) (hR : 0 ≤ R) (hRT : 0 ≤ R + T)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T) :
    ∀ᶠ k : ℝ in 𝓝 0, ∀ (j : Fin 3) (x : Space), x ∈ closedBall (0 : Space) b →
      ‖ConicalCommonResponse.centeredCorrection p a center B hB hcontrast ha hsep i l R T k x j‖ ≤
        k^2 * ((‖staticSource p a center B hB hcontrast ha hsep i‖ + 1) *
          ‖ScalarPotentialBound.cutoff 0 ((max b 0 + ‖center l‖) + T)‖) := by
  filter_upwards [source_eventually_bound p a center B hB hcontrast ha hsep i R T hR hRT] with k hk j x hx
  exact (correction_bound p a center B hB hcontrast ha hsep i l R T k b hT j x hx).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (sq_nonneg k)) (norm_nonneg _)).trans_eq (by ring))

end OQ14.ConicalCommonRetention
#print axioms OQ14.ConicalCommonRetention.source_tendsto
#print axioms OQ14.ConicalCommonRetention.source_eventually_bound
#print axioms OQ14.ConicalCommonRetention.correction_bound
#print axioms OQ14.ConicalCommonRetention.correction_eventually_bound
