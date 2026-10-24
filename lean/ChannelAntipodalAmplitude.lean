import ChannelUnitThroughput

/-! The outgoing Hankel amplitude of the incident finite TE field is the antipodal reflection of the incoming one:
`a_out (n) = - a_in (-n)`.  Consequently the outgoing amplitude of the complete field is
`n ↦ - a_in (-n) + F n`, the antipodal-reflected incident amplitude plus the far amplitude of the scattered field,
and the unit throughput of `ChannelUnitThroughput` reads `int |a_in (-n) - F n|^2 = int |a_in n|^2`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ChannelAntipodalAmplitude
open Filter MeasureTheory Topology OQ14.Maxwell OQ14.ChannelScaledFields OQ14.ChannelFarFluxExpansion
  OQ14.ChannelUnitThroughput
abbrev Idx := SymmetricHarmonicJets.Index

/-- The antipodal point of a unit direction. -/
def negSphere (n : OQ14.AngularPower.Sphere) : OQ14.AngularPower.Sphere :=
  ⟨-(n : Space), by simp [Metric.mem_sphere, dist_zero_right]⟩

theorem tau_neg (q : Idx) (n : OQ14.AngularPower.Sphere) :
    tau q (negSphere n) = ((-1 : ℂ) ^ q.val.1) • tau q n := by
  have h := HarmonicRadiationGeometry.angularToroidal_smul (RestrictedTEIncoming.polynomial q) q.val.1
    (poly_homogeneous q) (-1) (n : Space)
  rw [neg_one_smul] at h
  unfold tau negSphere
  simpa using h

/-- The outgoing Hankel amplitude of the incident field is minus the antipodal reflection of the incoming one. -/
theorem aE_false_antipodal (A : Idx →₀ ℂ) (n : OQ14.AngularPower.Sphere) :
    aE A false n = -aE A true (negSphere n) := by
  unfold aE
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [tau_neg, smul_smul, ← neg_smul]
  congr 1
  unfold RegularTEIncoming.coefficient
  simp only [Bool.false_eq_true, if_false, if_true]
  have h : (-Complex.I) ^ (q.val.1 + 1) = -((Complex.I) ^ (q.val.1 + 1) * (-1) ^ q.val.1) := by
    rw [neg_pow, pow_succ (-1 : ℂ)]
    ring
  rw [h]
  ring

theorem outAmplitude_antipodal (A : Idx →₀ ℂ) (ρ : Fin 3 → Space → ℂ) (n : OQ14.AngularPower.Sphere) :
    outAmplitude A ρ n = -RestrictedTEAmplitude.amplitude A (negSphere n) + Fsc ρ n := by
  unfold outAmplitude
  rw [aE_false_antipodal, aE_true_eq]

/-- Unit throughput with the antipodal form of the outgoing amplitude. -/
theorem unit_throughput_antipodal (A : Idx →₀ ℂ) (R : ℝ) (hR : 0 ≤ R) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0)
    (ε : Space → ℝ) (hε : Measurable ε) (M : ℝ) (hb : ∀ x, ‖ε x‖ ≤ M) (E H : Field)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (Metric.closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (Metric.closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell 1 ε E H)
    (hEx : ∀ x, R < ‖x‖ → E x = RestrictedTEIncoming.incomingElectric A x +
      RestrictedTEIncoming.outgoingElectric A x + ExteriorContinuity.electric 1 ρ x)
    (hHx : ∀ x, R < ‖x‖ → H x = RestrictedTEIncoming.incomingMagnetic A x +
      RestrictedTEIncoming.outgoingMagnetic A x + MagneticResponse.magnetic 1 ρ x) :
    (∫ n, energy (-RestrictedTEAmplitude.amplitude A (negSphere n) + Fsc ρ n)
        ∂OQ14.AngularPower.angularMeasure) / 2 = ‖RestrictedTEInput.input A‖ ^ 2 := by
  have h := unit_throughput_input_norm A R hR ρ hρ hc ε hε M hb E H hE hH hMax hEx hHx
  simpa only [outAmplitude_antipodal] using h

end OQ14.ChannelAntipodalAmplitude
#print axioms OQ14.ChannelAntipodalAmplitude.tau_neg
#print axioms OQ14.ChannelAntipodalAmplitude.aE_false_antipodal
#print axioms OQ14.ChannelAntipodalAmplitude.outAmplitude_antipodal
#print axioms OQ14.ChannelAntipodalAmplitude.unit_throughput_antipodal
