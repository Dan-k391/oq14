import Packet06ConeZeroBound
import ConicalIntrinsicCoefficient
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeZeroProjection
open Set Metric MeasureTheory OQ14.Maxwell OQ14.AngularPower OQ14.ConicalProjectionData

theorem zero_coefficient_bound (t D α : ℝ) (ht : 0 < t) (ht1 : t < 1) (hD : 0 ≤ D) (hα : 0 < α) :
    ∃ C ≥ (0 : ℝ), ∀ (p : ConicalStaticVolume.Data) (_hpt : p.threshold = t)
      (_hpd : p.contrast ≤ D) (hν : p.exponent < 1) (_hhalf : (1/2 : ℝ) ≤ p.exponent)
      (b : ℝ) (hb : 0 < b) (hbi : b < p.cutoff.rIn) (M : ℝ) (s : System p b), 0 ≤ M →
      (∀ i x, x ∈ closedBall (0 : Maxwell.Space) b → ‖s.correction i x-s.correction i 0‖ ≤ M*‖x‖^α) →
      ConicalIntrinsicCoefficient.coefficient s hb hbi hν = 0 →
      ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) b),
        ‖ConicalIntrinsicCoefficient.totalProjected s r‖ ≤ C*M*r^(1+α) := by
  obtain ⟨C,hC,hbound⟩ := Packet06ConeZeroBound.correction_remainder t D α ht ht1 hD hα
  refine ⟨C,hC,?_⟩
  intro p hpt hpd hν hhalf b hb hbi M s hM hW hz
  have he := ConicalIntrinsicCoefficient.total_expansion s hb hbi hν
  filter_upwards [he,ae_restrict_mem measurableSet_Ioo] with r hr hri
  rw [hr,hz]
  simp only [zero_mul,zero_add]
  exact hbound p hpt hpd hν hhalf b b M s hM hW r ⟨hri.1,hri.2.le⟩
#print axioms OQ14.Packet06ConeZeroProjection.zero_coefficient_bound
end OQ14.Packet06ConeZeroProjection
