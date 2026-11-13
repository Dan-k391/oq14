import Packet07ActualRadiation
import Packet07PlanarSetup

noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07SelectedRadiation
open Filter MeasureTheory
open scoped Topology
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

def actualUnknown {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k : ℝ) (n : ℕ) (input : Input) :=
  ConicalMaterialRunge.solutionOperator (g.rounded n) k g.enclosing
    (ConicalEntireGauge.restricted g.enclosing (FiniteAngularHerglotz.incident k input))

theorem selected_outgoing {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k s : ℝ) (hs : 0 < s)
    (a : Maxwell.Space) (n : ℕ) (input : Input) :
    let ρ := DynamicVolume.source (g.rounded n) (actualUnknown g k n input)
    (∀ᵐ x : Maxwell.Space ∂volume, g.enclosing < ‖s • (x-a)‖ →
      ∀ i, Packet07AffineMaxwell.affineField s a (g.electric k n input) x i =
        Packet07AffineMaxwell.affineField s a (FiniteAngularHerglotz.incident k input).E x i +
        Packet07AffineMaxwell.affineField s a (ExteriorContinuity.electric k ρ) x i) ∧
    (∀ x i, Packet07AffineMaxwell.affineField s a (g.magnetic k n input) x i =
      Packet07AffineMaxwell.affineField s a (FiniteAngularHerglotz.incident k input).H x i +
      Packet07AffineMaxwell.affineField s a (MagneticResponse.magnetic k ρ) x i) ∧
    (∀ n : Maxwell.Space, ‖n‖ = 1 →
      Tendsto (fun r : ℝ => MaxwellFarField.factor (s*k) r •
        Packet07AffineMaxwell.affineField s a (ExteriorContinuity.electric k ρ) (a+r • n))
        atTop (nhds (MaxwellFarField.electricAmplitude k ρ n))) ∧
    (∀ n : Maxwell.Space, ‖n‖ = 1 →
      Tendsto (fun r : ℝ => MaxwellFarField.factor (s*k) r •
        Packet07AffineMaxwell.affineField s a (MagneticResponse.magnetic k ρ) (a+r • n))
        atTop (nhds (MaxwellFarField.magneticAmplitude k ρ n))) := by
  have hc : ∀ x : Maxwell.Space, x ∉ Metric.closedBall 0 g.enclosing →
      (g.rounded n).value (VectorFourier.coordinateMap x) = 0 :=
    ConicalCommonBinaryPeaks.support g.dataFamily g.radii g.centers d g.contrast_pos.le
      g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.outer_enclosed n
  have hr := Packet07ActualRadiation.actual_affine_exterior (g.rounded n) (actualUnknown g k n input)
    g.enclosing k s g.enclosing_nonnegative hs a hc
  refine ⟨?_, ?_, hr.2.1, hr.2.2⟩
  · filter_upwards [hr.1] with x hx hdist i
    have he := congrFun (hx hdist) i
    change (s : ℂ) * g.electric k n input (s • (x-a)) i =
      (s : ℂ) * (FiniteAngularHerglotz.incident k input).E (s • (x-a)) i +
      (s : ℂ) * ExteriorContinuity.electric k (DynamicVolume.source (g.rounded n) (actualUnknown g k n input)) (s • (x-a)) i
    change (s : ℂ) * MaterialField.scattered (g.rounded n) k (actualUnknown g k n input) (s • (x-a)) i =
      (s : ℂ) * ExteriorContinuity.electric k (DynamicVolume.source (g.rounded n) (actualUnknown g k n input)) (s • (x-a)) i at he
    change (s : ℂ) * ((FiniteAngularHerglotz.incident k input).E (s • (x-a)) i +
      MaterialField.scattered (g.rounded n) k (actualUnknown g k n input) (s • (x-a)) i) = _
    rw [mul_add, he]
  · intro x i
    change (s : ℂ) * ((FiniteAngularHerglotz.incident k input).H (s • (x-a)) i +
      MagneticResponse.magnetic k (DynamicVolume.source (g.rounded n) (actualUnknown g k n input)) (s • (x-a)) i) =
      (s : ℂ) * (FiniteAngularHerglotz.incident k input).H (s • (x-a)) i +
      (s : ℂ) * MagneticResponse.magnetic k (DynamicVolume.source (g.rounded n) (actualUnknown g k n input)) (s • (x-a)) i
    ring

end OQ14.Packet07SelectedRadiation
#print axioms OQ14.Packet07SelectedRadiation.selected_outgoing
