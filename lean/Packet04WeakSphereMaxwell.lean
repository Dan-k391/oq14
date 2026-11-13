import ComplexSphereMaxwell
import ComplexMagneticHelmholtz

/-! Actual first-order Maxwell equations on balls crossing the sphere interface.
The dielectric remains inside the integral, so no classical interface trace is
assumed and no constant-material equation is substituted at the boundary. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04WeakSphereMaxwell
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.ExteriorHelmholtz
open OQ14.RegionalMaxwellHelmholtz OQ14.ComplexSphereMaxwell
open OQ14.ModalWeightedMode

def permittivity (n : ℝ) (hn : 1 < n) (x : Space) : ℂ :=
  1 + ((coefficient n hn).value (VectorFourier.coordinateMap x) : ℂ)

theorem permittivity_value (n : ℝ) (hn : 1 < n) (x : Space) :
    permittivity n hn x = if ‖x‖ < 1 then (n : ℂ)^2 else 1 := by
  unfold permittivity
  rw [coefficient_value]
  split_ifs <;> push_cast <;> ring

theorem actual_maxwell (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (hT : 1 ≤ T)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u = 0)
    (i : Fin 3) (f : Test (ball (0 : Space) T)) :
    (curlPair (fieldPair (electric n hn z T u)) i f =
      I*z * fieldPair (magnetic n hn z u) i f) ∧
    (curlPair (fieldPair (magnetic n hn z u)) i f =
      -(I*z) * ∫ x, permittivity n hn x * electric n hn z T u x i * f.val x) := by
  let s := CompactSmoothSchwartz.ofCompact f.val f.property.1 f.property.2.1
  let g : DynamicSource.Test := ⟨s, f.property.2.1⟩
  have hg : tsupport (g.val : Space → ℂ) ⊆ closedBall 0 T :=
    f.property.2.2.trans ball_subset_closedBall
  have h := ComplexMagneticMaxwell.actual_maxwell (coefficient n hn) 1 T (by linarith) u
    (coefficient_support n hn) i g hg z
  have hs := ComplexSphereInterface.displacement_pair_actual n hn z T hT u hker i g
  simp only [ComplexInterfaceWeak.displacementPair, ComplexInterfaceWeak.pair,
    ComplexResponseTests.testPair_integral] at hs
  simp only [DynamicSource.testPartial, GradientProjection.pderivative_apply, s, g,
    CompactSmoothSchwartz.ofCompact_apply] at h hs
  constructor
  · exact h.1
  · change _ = -(I*z) * _
    dsimp only [curlPair, fieldPair, testPartial, magnetic]
    dsimp only [electric, permittivity]
    rw [← hs]
    exact h.2

theorem electric_local (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ)
    (u : VectorFourier.VectorL2) (i : Fin 3) :
    LocallyIntegrable (fun x => electric n hn z T u x i) :=
  ComplexExteriorHelmholtz.actual_locallyIntegrable n hn z T u i

end OQ14.Packet04WeakSphereMaxwell
#print axioms OQ14.Packet04WeakSphereMaxwell.permittivity_value
#print axioms OQ14.Packet04WeakSphereMaxwell.actual_maxwell
#print axioms OQ14.Packet04WeakSphereMaxwell.electric_local
