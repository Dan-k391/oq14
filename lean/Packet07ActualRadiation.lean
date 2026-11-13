import Packet07AffineRadiation

/-! The centered outgoing representatives are the actual selected volume
    responses, with their correct a.e. electric-field identification. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07ActualRadiation
open Filter MeasureTheory
open scoped Topology

theorem actual_affine_exterior (c : StaticCoefficient.Coefficient)
    (u : VectorFourier.VectorL2) (R k s : ℝ) (hR : 0 ≤ R) (hs : 0 < s)
    (a : Maxwell.Space)
    (hc : ∀ x : Maxwell.Space, x ∉ Metric.closedBall 0 R →
      c.value (VectorFourier.coordinateMap x) = 0) :
    (∀ᵐ x : Maxwell.Space ∂volume, R < ‖s • (x-a)‖ →
      Packet07AffineMaxwell.affineField s a (MaterialField.scattered c k u) x =
      Packet07AffineMaxwell.affineField s a (ExteriorContinuity.electric k (DynamicVolume.source c u)) x) ∧
    (∀ n : Maxwell.Space, ‖n‖ = 1 →
      Tendsto (fun r : ℝ => MaxwellFarField.factor (s*k) r •
        Packet07AffineMaxwell.affineField s a (ExteriorContinuity.electric k (DynamicVolume.source c u)) (a+r • n))
        atTop (nhds (MaxwellFarField.electricAmplitude k (DynamicVolume.source c u) n))) ∧
    (∀ n : Maxwell.Space, ‖n‖ = 1 →
      Tendsto (fun r : ℝ => MaxwellFarField.factor (s*k) r •
        Packet07AffineMaxwell.affineField s a (MagneticResponse.magnetic k (DynamicVolume.source c u)) (a+r • n))
        atTop (nhds (MaxwellFarField.magneticAmplitude k (DynamicVolume.source c u) n))) := by
  have hi : ∀ j, Integrable (DynamicVolume.source c u j) := DynamicVolume.source_integrable c u R hc
  have hz : ∀ j y, y ∉ Metric.closedBall (0 : Maxwell.Space) R → DynamicVolume.source c u j y = 0 :=
    DynamicVolume.source_zero c u R hc
  have hae := ExteriorContinuity.electric_ae_exterior k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) hi (StaticNewton.material_source_ae c u) R hz
  have hd := (DilationL2.smul_qmp_space s hs.ne').ae hae
  have ht := (measurePreserving_add_right (volume : Measure Maxwell.Space) (-a)).quasiMeasurePreserving.ae hd
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [ht] with x hx hxr
    have he := hx hxr
    change FrequencyScalingMaxwell.scaleField s (MaterialField.scattered c k u) (x-a) =
      FrequencyScalingMaxwell.scaleField s (ExteriorContinuity.electric k (DynamicVolume.source c u)) (x-a)
    unfold FrequencyScalingMaxwell.scaleField MaterialField.scattered
    rw [show s • (x-a) = s • (x + -a) by simp [sub_eq_add_neg]]
    rw [he]
  · intro n hn
    exact Packet07AffineRadiation.centered_electric_outgoing s k hs a n R hR _ hi hz hn
  · intro n hn
    exact Packet07AffineRadiation.centered_magnetic_outgoing s k hs a n R hR _ hi hz hn

end OQ14.Packet07ActualRadiation
#print axioms OQ14.Packet07ActualRadiation.actual_affine_exterior
