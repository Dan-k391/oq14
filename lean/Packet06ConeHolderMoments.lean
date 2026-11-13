import Packet06ConeHolderParticular
import ConicalProjectionData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeHolderMoments
open MeasureTheory Set Metric OQ14.Maxwell OQ14.AngularPower OQ14.ConicalProjectionData
  OQ14.ConicalMomentWeights OQ14.PolarMomentTesting

theorem moment_holder (p : ConicalStaticVolume.Data) (a R M α C : ℝ) (s : System p a)
    (hM : 0 ≤ M) (hα : 0 < α) (_hC : 0 ≤ C)
    (hW : ∀ i x, x ∈ closedBall (0 : Maxwell.Space) R → ‖s.correction i x‖ ≤ M*‖x‖^α)
    (hr : ∀ i n, ‖radial p.eigenvalue p.contrast p.threshold i n‖ ≤ C)
    (ht : ∀ i n, ‖tangent p.eigenvalue p.contrast p.threshold i n‖ ≤ C)
    (r : ℝ) (hri : r ∈ Icc (0 : ℝ) R) :
    ‖radialCorrection s r‖ ≤ (3*C*(angularMeasure univ).toReal*M)*r^α ∧
      ‖tangentCorrection s r‖ ≤ (3*C*(angularMeasure univ).toReal*M)*r^α := by
  have hm : 0 ≤ M*r^α := mul_nonneg hM (Real.rpow_nonneg hri.1 _)
  have hb (σ : Fin 3 → Sphere → ℂ) (hσ : ∀ i n, ‖σ i n‖ ≤ C) :
      ‖∑ i : Fin 3, moment (s.correction i) (σ i) r‖ ≤
        (3*C*(angularMeasure univ).toReal*M)*r^α := by
    calc
      _ ≤ ∑ i : Fin 3, ‖moment (s.correction i) (σ i) r‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, (M*r^α)*C*(angularMeasure univ).toReal := by
        apply Finset.sum_le_sum
        intro i _
        apply correction_moment_norm_le s r (M*r^α) hm _ i (σ i) C (hσ i) r hri.1 le_rfl
        intro j x hx
        have hxr : ‖x‖ ≤ r := by simpa using hx
        have hxR : x ∈ closedBall (0 : Maxwell.Space) R := by simpa using hxr.trans hri.2
        exact le_trans (hW j x hxR) (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg x) hxr hα.le) hM)
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  exact ⟨hb _ hr,hb _ ht⟩
#print axioms OQ14.Packet06ConeHolderMoments.moment_holder
end OQ14.Packet06ConeHolderMoments
