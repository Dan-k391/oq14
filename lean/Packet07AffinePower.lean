import Packet07AffineMaxwell

/-! Exact incoming-power normalization after translating and dilating a finite input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07AffinePower
open Filter MeasureTheory Maxwell FrequencyScalingMaxwell
open scoped Topology
abbrev Sphere := SphereReactionKernel.Sphere
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

/-- Incoming physical flux through a sphere centered at the translated device. -/
def centeredInwardPower (s k : ℝ) (a : Maxwell.Space) (c : Input) (r : ℝ) : ℝ :=
  -r^2 * ∫ n : Sphere, FarFieldPower.radialPower (n : Maxwell.Space)
    (Packet07AffineMaxwell.affineField s a (FiniteMixedScaledFlux.electricPartK k c) (a + r • (n : Maxwell.Space)))
    (Packet07AffineMaxwell.affineField s a (FiniteMixedScaledFlux.magneticPartK k c) (a + r • (n : Maxwell.Space)))
    ∂SphereReactionKernel.surface

/-- Centered incoming flux is exactly the original incoming flux at the scaled radius. -/
theorem centered_power_eq (s k : ℝ) (a : Maxwell.Space) (c : Input) (r : ℝ) :
    centeredInwardPower s k a c r = FiniteMixedScaledFlux.inwardPowerK k c (s*r) := by
  unfold centeredInwardPower FiniteMixedScaledFlux.inwardPowerK
  have he : (∫ n : Sphere, FarFieldPower.radialPower (n : Maxwell.Space)
      (Packet07AffineMaxwell.affineField s a (FiniteMixedScaledFlux.electricPartK k c) (a+r • (n : Maxwell.Space)))
      (Packet07AffineMaxwell.affineField s a (FiniteMixedScaledFlux.magneticPartK k c) (a+r • (n : Maxwell.Space)))
        ∂SphereReactionKernel.surface) =
      s^2 * ∫ n : Sphere, FarFieldPower.radialPower (n : Maxwell.Space)
        (FiniteMixedScaledFlux.electricPartK k c ((s*r) • (n : Maxwell.Space)))
        (FiniteMixedScaledFlux.magneticPartK k c ((s*r) • (n : Maxwell.Space))) ∂SphereReactionKernel.surface := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with n
    simp only [Packet07AffineMaxwell.affineField, add_sub_cancel_left, scaleField,
      smul_smul, FrequencyScalingPower.radialPower_smul]
  rw [he]
  ring

/-- Power normalization is unchanged by affine placement of the physical device;
    the enclosing spheres are centered at the translated device. -/
theorem centered_unit_power (s k : ℝ) (hs : 0 < s) (a : Maxwell.Space) (c : Input)
    (hpower : Tendsto (FiniteMixedScaledFlux.inwardPowerK k c) atTop (𝓝 1)) :
    Tendsto (centeredInwardPower s k a c) atTop (𝓝 1) := by
  have h := hpower.comp (tendsto_id.const_mul_atTop hs)
  exact h.congr (fun r => (centered_power_eq s k a c r).symm)

end OQ14.Packet07AffinePower
#print axioms OQ14.Packet07AffinePower.centered_power_eq
#print axioms OQ14.Packet07AffinePower.centered_unit_power
