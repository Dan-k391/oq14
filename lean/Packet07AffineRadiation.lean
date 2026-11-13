import Packet07AffineComponents
import MaxwellFarField

/-! Outgoing compact-source radiation under arbitrary frequency dilation,
    evaluated on spheres centered at the translated device. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07AffineRadiation
open Filter MeasureTheory
open scoped Topology

theorem factor_dilation (s k r : ℝ) :
    MaxwellFarField.factor (s*k) r * (s : ℂ) = MaxwellFarField.factor k (s*r) := by
  unfold MaxwellFarField.factor
  have h : -Complex.I * ((s*k : ℝ) : ℂ) * (r : ℂ) =
      -Complex.I * (k : ℂ) * ((s*r : ℝ) : ℂ) := by push_cast; ring
  rw [h]
  push_cast
  ring

theorem centered_far_dilation (s k : ℝ) (hs : 0 < s) (a n : Maxwell.Space)
    (F : Maxwell.Field) (A : Maxwell.Vector)
    (hF : Tendsto (fun r : ℝ => MaxwellFarField.factor k r • F (r • n)) atTop (nhds A)) :
    Tendsto (fun r : ℝ => MaxwellFarField.factor (s*k) r •
      Packet07AffineMaxwell.affineField s a F (a+r • n)) atTop (nhds A) := by
  have h := hF.comp (tendsto_id.const_mul_atTop hs)
  refine h.congr (fun r => ?_)
  change MaxwellFarField.factor k (s*r) • F ((s*r) • n) =
    MaxwellFarField.factor (s*k) r • ((s : ℂ) • F (s • (a+r • n-a)))
  have hx : a + r • n - a = r • n := by abel
  rw [hx, smul_smul, smul_smul, factor_dilation]

theorem centered_electric_outgoing (s k : ℝ) (hs : 0 < s) (a n : Maxwell.Space)
    (R : ℝ) (hR : 0 ≤ R) (ρ : Fin 3 → Maxwell.Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => MaxwellFarField.factor (s*k) r •
      Packet07AffineMaxwell.affineField s a (ExteriorContinuity.electric k ρ) (a+r • n))
      atTop (nhds (MaxwellFarField.electricAmplitude k ρ n)) :=
  centered_far_dilation s k hs a n _ _ (MaxwellFarField.electric_far_vector_limit k R hR ρ hρ hc n hn)

theorem centered_magnetic_outgoing (s k : ℝ) (hs : 0 < s) (a n : Maxwell.Space)
    (R : ℝ) (hR : 0 ≤ R) (ρ : Fin 3 → Maxwell.Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => MaxwellFarField.factor (s*k) r •
      Packet07AffineMaxwell.affineField s a (MagneticResponse.magnetic k ρ) (a+r • n))
      atTop (nhds (MaxwellFarField.magneticAmplitude k ρ n)) :=
  centered_far_dilation s k hs a n _ _ (MaxwellFarField.magnetic_far_vector_limit k R hR ρ hρ hc n hn)

end OQ14.Packet07AffineRadiation
#print axioms OQ14.Packet07AffineRadiation.factor_dilation
#print axioms OQ14.Packet07AffineRadiation.centered_far_dilation
#print axioms OQ14.Packet07AffineRadiation.centered_electric_outgoing
#print axioms OQ14.Packet07AffineRadiation.centered_magnetic_outgoing
