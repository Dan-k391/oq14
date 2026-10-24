import ChannelFarFluxExpansion
import ChannelCesaroThroughput
import LosslessSphereFluxConstancy
import RestrictedTEInput
import RestrictedTEMaterial

/-! Unit throughput of the complete lossless field.

Let `A` be a finite restricted TE coefficient vector with incident field `E_in + E_out` (incoming and outgoing
Hankel parts), let `rho` be a compactly supported integrable source with scattered field
`ExteriorContinuity.electric 1 rho`, and let `(E, H)` be a weak Maxwell pair with real bounded permittivity
(`TestMaxwell 1 eps E H`) equal to the sum of incident and scattered fields outside the ball of radius `R`.
The sphere flux vanishes for almost every radius (`LosslessSphereFluxConstancy.flux_ae_zero`), while the far
expansion (`ChannelFarFluxExpansion.far_flux_expansion`) is `g r + Re (exp (-2 i r) c r)` with `g -> G`,
`c -> C`.  The Cesaro lemma gives `G = 0`, i.e. the total outgoing energy equals the incoming energy. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ChannelUnitThroughput
open Filter MeasureTheory Topology OQ14.Maxwell OQ14.ChannelScaledFields OQ14.ChannelFarFluxExpansion
abbrev Idx := SymmetricHarmonicJets.Index

/-- The outgoing amplitude of the complete field: the outgoing Hankel amplitude of the incident field plus the far
amplitude of the scattered field. -/
def outAmplitude (A : Idx →₀ ℂ) (ρ : Fin 3 → Space → ℂ) (n : OQ14.AngularPower.Sphere) : Vector :=
  aE A false n + Fsc ρ n

theorem aE_true_eq (A : Idx →₀ ℂ) : aE A true = RestrictedTEAmplitude.amplitude A := by
  funext n
  ext j
  simp only [aE, RestrictedTEAmplitude.amplitude, FiniteTEIncomingPower.amplitude,
    FiniteTEIncomingPower.amplitudeCoefficient, FiniteTEIncomingPower.angular, tau, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, ContinuousMap.coe_mk]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Unit throughput as an energy identity: the outgoing energy of the complete field equals the incoming energy
of the incident field. -/
theorem unit_throughput_energy (A : Idx →₀ ℂ) (R : ℝ) (hR : 0 ≤ R) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0)
    (ε : Space → ℝ) (hε : Measurable ε) (M : ℝ) (hb : ∀ x, ‖ε x‖ ≤ M) (E H : Field)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (Metric.closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (Metric.closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell 1 ε E H)
    (hEx : ∀ x, R < ‖x‖ → E x = RestrictedTEIncoming.incomingElectric A x +
      RestrictedTEIncoming.outgoingElectric A x + ExteriorContinuity.electric 1 ρ x)
    (hHx : ∀ x, R < ‖x‖ → H x = RestrictedTEIncoming.incomingMagnetic A x +
      RestrictedTEIncoming.outgoingMagnetic A x + MagneticResponse.magnetic 1 ρ x) :
    (∫ n, energy (outAmplitude A ρ n) ∂OQ14.AngularPower.angularMeasure) =
      ∫ n, energy (RestrictedTEAmplitude.amplitude A n) ∂OQ14.AngularPower.angularMeasure := by
  obtain ⟨R1, g, c, G, C, hR1, hexp, hg, hcC, hG⟩ := far_flux_expansion A R hR ρ hρ hc E H hEx hHx
  have hR10 : (0 : ℝ) ≤ R1 := hR.trans hR1
  have hae : ∀ᵐ r ∂(volume.restrict (Set.Ioi R1)), OQ14.RadialFlux.flux E H r = 0 :=
    ae_restrict_of_ae_restrict_of_subset (Set.Ioi_subset_Ioi hR10)
      (LosslessSphereFluxConstancy.flux_ae_zero 1 ε hε M hb E H hE hH hMax)
  have h0 := ChannelCesaroThroughput.cesaro_constant_limit (OQ14.RadialFlux.flux E H) g (fun _ => 0) c 0 G C 1 R1
    one_ne_zero hae (fun r hr => by rw [hexp r hr, add_zero]) hg hcC tendsto_const_nhds
  rw [← h0] at hG
  have hG' : (∫ n, energy (aE A false n + Fsc ρ n) ∂OQ14.AngularPower.angularMeasure) -
      ∫ n, energy (aE A true n) ∂OQ14.AngularPower.angularMeasure = 0 := by linarith
  rw [aE_true_eq] at hG'
  exact sub_eq_zero.mp hG'

/-- Unit throughput in the physical normalization: half the outgoing energy of the complete field is the physical
incoming power of the incident field. -/
theorem unit_throughput_physical (A : Idx →₀ ℂ) (R : ℝ) (hR : 0 ≤ R) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0)
    (ε : Space → ℝ) (hε : Measurable ε) (M : ℝ) (hb : ∀ x, ‖ε x‖ ≤ M) (E H : Field)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (Metric.closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (Metric.closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell 1 ε E H)
    (hEx : ∀ x, R < ‖x‖ → E x = RestrictedTEIncoming.incomingElectric A x +
      RestrictedTEIncoming.outgoingElectric A x + ExteriorContinuity.electric 1 ρ x)
    (hHx : ∀ x, R < ‖x‖ → H x = RestrictedTEIncoming.incomingMagnetic A x +
      RestrictedTEIncoming.outgoingMagnetic A x + MagneticResponse.magnetic 1 ρ x) :
    (∫ n, energy (outAmplitude A ρ n) ∂OQ14.AngularPower.angularMeasure) / 2 =
      RestrictedTEIncoming.physicalPower A := by
  rw [unit_throughput_energy A R hR ρ hρ hc ε hε M hb E H hE hH hMax hEx hHx]
  rfl

/-- Unit throughput in terms of the actual input norm. -/
theorem unit_throughput_input_norm (A : Idx →₀ ℂ) (R : ℝ) (hR : 0 ≤ R) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0)
    (ε : Space → ℝ) (hε : Measurable ε) (M : ℝ) (hb : ∀ x, ‖ε x‖ ≤ M) (E H : Field)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (Metric.closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (Metric.closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell 1 ε E H)
    (hEx : ∀ x, R < ‖x‖ → E x = RestrictedTEIncoming.incomingElectric A x +
      RestrictedTEIncoming.outgoingElectric A x + ExteriorContinuity.electric 1 ρ x)
    (hHx : ∀ x, R < ‖x‖ → H x = RestrictedTEIncoming.incomingMagnetic A x +
      RestrictedTEIncoming.outgoingMagnetic A x + MagneticResponse.magnetic 1 ρ x) :
    (∫ n, energy (outAmplitude A ρ n) ∂OQ14.AngularPower.angularMeasure) / 2 =
      ‖RestrictedTEInput.input A‖ ^ 2 := by
  rw [RestrictedTEInput.input_norm_sq]
  exact unit_throughput_physical A R hR ρ hρ hc ε hε M hb E H hE hH hMax hEx hHx

/-! ### Consistency check: the hypotheses are jointly satisfiable (no scatterer)

For the zero source and the global incident field `RestrictedTEPlaneLocal.electric A`, `magnetic A` (a global weak
solution with `eps = 1`, `RestrictedTEMaterial.testMaxwell`) every hypothesis of `unit_throughput_energy` holds,
and the conclusion is the identity `int |a_out|^2 = int |a_in|^2` for the incident finite TE field. -/

theorem scattered_electric_zero (x : Space) : ExteriorContinuity.electric 1 (fun _ _ => (0 : ℂ)) x = 0 := by
  ext i
  simp [ExteriorContinuity.electric, KernelConvolution.response]

theorem scattered_magnetic_zero (x : Space) : MagneticResponse.magnetic 1 (fun _ _ => (0 : ℂ)) x = 0 := by
  ext i
  simp [MagneticResponse.magnetic, KernelConvolution.response]

theorem scattered_amplitude_zero (n : Space) : MaxwellFarField.electricAmplitude 1 (fun _ _ => (0 : ℂ)) n = 0 := by
  ext i
  simp [MaxwellFarField.electricAmplitude, MaxwellFarField.potentialAmplitude, ScalarFarField.amplitude]

theorem magnetic_memLp (A : Idx →₀ ℂ) (R : ℝ) (i : Fin 3) :
    MemLp (fun x => RestrictedTEPlaneLocal.magnetic A x i) 2 (volume.restrict (Metric.closedBall 0 R)) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Space) R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall (0 : Space) R).measure_lt_top⟩
  have hc := (RestrictedTEMaterial.magnetic_smooth A i).continuous
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Space) R).exists_bound_of_continuousOn hc.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable.restrict B
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  exact hB x hx

theorem vacuum_unit_throughput (A : Idx →₀ ℂ) :
    (∫ n, energy (aE A false n) ∂OQ14.AngularPower.angularMeasure) =
      ∫ n, energy (RestrictedTEAmplitude.amplitude A n) ∂OQ14.AngularPower.angularMeasure := by
  have h := unit_throughput_energy A 0 le_rfl (fun _ _ => (0 : ℂ)) (fun _ => integrable_zero _ _ _)
    (fun _ _ _ => rfl) (fun _ => 1) measurable_const 1 (fun _ => by simp)
    (RestrictedTEPlaneLocal.electric A) (RestrictedTEPlaneLocal.magnetic A)
    (fun T i => RestrictedTEMaterial.electric_memLp A T i) (fun T i => magnetic_memLp A T i)
    (RestrictedTEMaterial.testMaxwell A)
    (fun x hx => by
      have hx0 : x ≠ 0 := norm_pos_iff.mp hx
      rw [scattered_electric_zero, add_zero, add_comm]
      exact RestrictedTEIncoming.electric_split A x hx0)
    (fun x hx => by
      have hx0 : x ≠ 0 := norm_pos_iff.mp hx
      rw [scattered_magnetic_zero, add_zero, add_comm]
      exact RestrictedTEIncoming.magnetic_split A x hx0)
  simpa [outAmplitude, Fsc, scattered_amplitude_zero] using h

end OQ14.ChannelUnitThroughput
#print axioms OQ14.ChannelUnitThroughput.aE_true_eq
#print axioms OQ14.ChannelUnitThroughput.unit_throughput_energy
#print axioms OQ14.ChannelUnitThroughput.unit_throughput_physical
#print axioms OQ14.ChannelUnitThroughput.unit_throughput_input_norm
#print axioms OQ14.ChannelUnitThroughput.scattered_electric_zero
#print axioms OQ14.ChannelUnitThroughput.scattered_magnetic_zero
#print axioms OQ14.ChannelUnitThroughput.scattered_amplitude_zero
#print axioms OQ14.ChannelUnitThroughput.magnetic_memLp
#print axioms OQ14.ChannelUnitThroughput.vacuum_unit_throughput
