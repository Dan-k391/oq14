import Packet06ConeUniformWeights
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeUniformParticular
open Set Metric MeasureTheory OQ14.Maxwell OQ14.AngularPower OQ14.ConicalProjectionData

theorem estimate (t D α : ℝ) (ht : 0 < t) (ht1 : t < 1) (hD : 0 ≤ D) (hα : 0 < α) :
    ∃ C ≥ (0 : ℝ), ∀ (p : ConicalStaticVolume.Data) (_hpt : p.threshold = t)
      (_hpd : p.contrast ≤ D) (_hν : p.exponent < 1) (a R M : ℝ) (s : System p a),
      0 ≤ M → (∀ i x, x ∈ closedBall (0 : Maxwell.Space) R → ‖s.correction i x‖ ≤ M*‖x‖^α) →
      ∀ r ∈ Ioc (0 : ℝ) R,
      ‖ConicalRadialParticular.particular p.exponent (radialCorrection s) (tangentCorrection s) r‖ ≤
        C*M*r^(1+α) := by
  obtain ⟨K,hK,hweights⟩ := Packet06ConeUniformWeights.uniform_weights t D ht ht1 hD
  let Q : ℝ := 3*K*(angularMeasure univ).toReal
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨(3/α+1)*Q, mul_nonneg (by positivity) hQ, ?_⟩
  intro p hpt hpd hν a R M s hM hW r hr
  have hm := Packet06ConeHolderMoments.moment_holder p a R M α K s hM hα hK hW
  have hbound := hweights p.eigenvalue p.eigenvalue_bounds p.contrast ⟨p.contrast_nonnegative,hpd⟩
  have hrw : ∀ i n, ‖ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold i n‖ ≤ K := by
    intro i n
    simpa [hpt] using (hbound i n).1
  have htw : ∀ i n, ‖ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i n‖ ≤ K := by
    intro i n
    simpa [hpt] using (hbound i n).2
  have hforce (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) r) :
      ‖radialCorrection s v‖ ≤ (Q*M)*v^α ∧ ‖tangentCorrection s v‖ ≤ (Q*M)*v^α := by
    have h := hm hrw htw v ⟨hv.1.le,hv.2.le.trans hr.2⟩
    simpa only [Q,mul_assoc] using h
  have h := Packet06ConeHolderParticular.particular_holder_bound p.exponent α ⟨p.exponent_pos,hν⟩ hα
    (radialCorrection s) (tangentCorrection s) (radialCorrection_continuous s).continuousOn
    (tangentCorrection_continuous s).continuousOn r (Q*M) hr.1 (mul_nonneg hQ hM) hforce
  convert h using 1
  ring
#print axioms OQ14.Packet06ConeUniformParticular.estimate
end OQ14.Packet06ConeUniformParticular
