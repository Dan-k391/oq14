import Packet07PlanarConeGeometry
import FullChannelWeakLimit
import FrequencyScalingPower

/-! Power-preserving frequency dilation for the actual finite harmonic illumination. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07FrequencyScaling
open Filter MeasureTheory Maxwell FrequencyScalingMaxwell
open scoped Topology
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem value_dilation (s k : ℝ) (x : Maxwell.Space) (i : Fin 3)
    (F : ComplexVectorSphere.Ambient) :
    HerglotzAngularL2.value (s*k) x i F = HerglotzAngularL2.value k (s • x) i F := by
  have hp : TransversePlaneFields.plane (-(s*k)) x i = TransversePlaneFields.plane (-k) (s • x) i := by
    ext n j
    simp only [TransversePlaneFields.plane, ContinuousMap.coe_mk, PiLp.smul_apply, smul_eq_mul]
    congr 1
    unfold SphereReactionKernel.wave
    congr 1
    simp only [inner_smul_right, RCLike.conj_to_real, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  have hf : TransversePlaneFields.field (-(s*k)) x i = TransversePlaneFields.field (-k) (s • x) i := by
    unfold TransversePlaneFields.field
    rw [hp]
  unfold HerglotzAngularL2.value
  rw [hf]

theorem finiteAmplitude_smul (z : ℂ) (c : Input) :
    HerglotzAngularL2.finiteAmplitude (z • c) = z • HerglotzAngularL2.finiteAmplitude c := by
  change Finsupp.linearCombination ℂ ComplexTransverseExpansion.vector (z • c) =
    z • Finsupp.linearCombination ℂ ComplexTransverseExpansion.vector c
  exact map_smul _ _ _

/-- The physically normalized incident electric field scales by s under k ↦ s k. -/
theorem finite_electric_dilation (s k : ℝ) (c : Input) (x : Maxwell.Space) (i : Fin 3) :
    (FiniteAngularHerglotz.incident (s*k) ((s : ℂ) • c)).E x i =
      scaleField s (FiniteAngularHerglotz.incident k c).E x i := by
  rw [FiniteAngularHerglotz.electric_value, finiteAmplitude_smul, map_smul, value_dilation]
  change (s : ℂ) * HerglotzAngularL2.value k (s • x) i (HerglotzAngularL2.finiteAmplitude c) =
    (s : ℂ) * (FiniteAngularHerglotz.incident k c).E (s • x) i
  rw [FiniteAngularHerglotz.electric_value]

/-- The magnetic illumination obeys the same physical dilation. -/
theorem finite_magnetic_dilation (s k : ℝ) (c : Input) (x : Maxwell.Space) (i : Fin 3) :
    (FiniteAngularHerglotz.incident (s*k) ((s : ℂ) • c)).H x i =
      scaleField s (FiniteAngularHerglotz.incident k c).H x i := by
  rw [← FullChannelWeakLimit.finite_magnetic_value]
  change FullChannelMagnetic.magnetic (s*k) (HerglotzAngularL2.finiteAmplitude ((s : ℂ) • c)) x i =
    (s : ℂ) * (FiniteAngularHerglotz.incident k c).H (s • x) i
  rw [← FullChannelWeakLimit.finite_magnetic_value]
  unfold FullChannelMagnetic.magnetic
  rw [finiteAmplitude_smul, FullChannelMagnetic.rotation_smul]
  have he : -((s : ℂ) • FullChannelMagnetic.rotation (HerglotzAngularL2.finiteAmplitude c)) =
      (s : ℂ) • (-FullChannelMagnetic.rotation (HerglotzAngularL2.finiteAmplitude c)) := by simp
  rw [he, map_smul, value_dilation]
  rfl

/-- If the original illumination has unit incoming power, its frequency-dilated
    finite harmonic illumination has the same unit incoming power. -/
theorem finite_unit_power_dilation (s k : ℝ) (hs : 0 < s) (hk : 0 < k) (c : Input)
    (hpower : Tendsto (FiniteMixedScaledFlux.inwardPowerK k c) atTop (𝓝 1)) :
    Tendsto (FiniteMixedScaledFlux.inwardPowerK (s*k) ((s : ℂ) • c)) atTop (𝓝 1) := by
  have h0 := FiniteMixedScaledFlux.inwardPowerK_limit_E k hk c
  have he : FiniteMixedScaledFlux.E c / k^2 = 1 := tendsto_nhds_unique h0 hpower
  have hs0 : s ≠ 0 := hs.ne'
  have hk0 : k ≠ 0 := hk.ne'
  have h := FiniteMixedScaledFlux.inwardPowerK_limit_E (s*k) (mul_pos hs hk) ((s : ℂ) • c)
  rw [FiniteMixedScaledFlux.E_smul] at h
  have hval : s^2 * FiniteMixedScaledFlux.E c / (s*k)^2 = 1 := by
    field_simp at he ⊢
    nlinarith
  rwa [hval] at h

end OQ14.Packet07FrequencyScaling
#print axioms OQ14.Packet07FrequencyScaling.value_dilation
#print axioms OQ14.Packet07FrequencyScaling.finiteAmplitude_smul
#print axioms OQ14.Packet07FrequencyScaling.finite_electric_dilation
#print axioms OQ14.Packet07FrequencyScaling.finite_magnetic_dilation
#print axioms OQ14.Packet07FrequencyScaling.finite_unit_power_dilation
