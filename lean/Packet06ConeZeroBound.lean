import Packet06ConeMomentCancellation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeZeroBound
open Set Metric MeasureTheory OQ14.Maxwell OQ14.AngularPower OQ14.ConicalProjectionData

theorem correction_remainder (t D α : ℝ) (ht : 0 < t) (ht1 : t < 1) (hD : 0 ≤ D) (hα : 0 < α) :
    ∃ C ≥ (0 : ℝ), ∀ (p : ConicalStaticVolume.Data) (_hpt : p.threshold = t)
      (_hpd : p.contrast ≤ D) (_hν : p.exponent < 1) (_hhalf : (1/2 : ℝ) ≤ p.exponent)
      (a R M : ℝ) (s : System p a), 0 ≤ M →
      (∀ i x, x ∈ closedBall (0 : Maxwell.Space) R → ‖s.correction i x-s.correction i 0‖ ≤ M*‖x‖^α) →
      ∀ r ∈ Ioc (0 : ℝ) R,
      ‖ConicalRadialParticular.particular p.exponent (radialCorrection s) (tangentCorrection s) r +
        (r : ℂ)/(p.eigenvalue : ℂ)*tangentCorrection s r‖ ≤ C*M*r^(1+α) := by
  obtain ⟨K,hK,hweights⟩ := Packet06ConeUniformWeights.uniform_weights t D ht ht1 hD
  let Q : ℝ := 3*K*(angularMeasure univ).toReal
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨(3/α+3)*Q, mul_nonneg (by positivity) hQ, ?_⟩
  intro p hpt hpd hν hhalf a R M s hM hW r hr
  have hbound := hweights p.eigenvalue p.eigenvalue_bounds p.contrast ⟨p.contrast_nonnegative,hpd⟩
  have hrw : ∀ i n, ‖ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold i n‖ ≤ K := by
    intro i n
    simpa [hpt] using (hbound i n).1
  have htw : ∀ i n, ‖ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i n‖ ≤ K := by
    intro i n
    simpa [hpt] using (hbound i n).2
  have hm v (hv : v ∈ Icc (0 : ℝ) R) := Packet06ConeMomentCancellation.moment_difference_holder
    p a R M α K s hM hα hK hW hrw htw v hv
  have hforce v (hv : v ∈ Ioo (0 : ℝ) r) :
      ‖radialCorrection s v-radialCorrection s 0‖ ≤ (Q*M)*v^α ∧
      ‖tangentCorrection s v-((p.exponent*(p.exponent+1) : ℝ) : ℂ)*radialCorrection s 0‖ ≤ (Q*M)*v^α := by
    have h := hm v ⟨hv.1.le,hv.2.le.trans hr.2⟩
    rw [Packet06ConeMomentCancellation.correction_origin_identity] at h
    simpa only [Q,mul_assoc,p.separation] using h
  have hend := hm r ⟨hr.1.le,hr.2⟩
  rw [Packet06ConeMomentCancellation.correction_origin_identity] at hend
  have h := Packet06ConeRenormalized.zero_mode_projection_bound p.exponent α ⟨p.exponent_pos,hν⟩ hhalf hα
    (radialCorrection s) (tangentCorrection s) (radialCorrection_continuous s).continuousOn
    (tangentCorrection_continuous s).continuousOn (radialCorrection s 0) r (Q*M) hr.1 (mul_nonneg hQ hM) hforce
    (by simpa only [Q,mul_assoc,p.separation] using hend.2)
  simpa only [p.separation, mul_assoc] using h
#print axioms OQ14.Packet06ConeZeroBound.correction_remainder
end OQ14.Packet06ConeZeroBound
