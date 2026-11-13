import Packet06GreenPhysical
import ComplexMagneticMaxwell

/-! Actual first-order physical Maxwell equations from a volume-kernel vector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06KernelMaxwell
open MeasureTheory Metric DynamicSource
open ComplexResponseTests (testPair testPair_integral)
open StaticCoefficient (Coefficient)
open WeakCurl (next previous)
open scoped SchwartzMap
abbrev V := VectorFourier.VectorL2

theorem source_testPair (c : Coefficient) (u : V) (i : Fin 3) (f : Test) :
    (∫ x : Maxwell.Space, DynamicVolume.source c u i x*f.val x) =
      testPair i f.val (StaticCoefficient.sqrtMultiplier c u) := by
  rw [testPair_integral]
  apply integral_congr_ae
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c u)
  filter_upwards [hs] with x hx
  rw [hx]
  rfl

theorem kernel_displacement (c : Coefficient) (z : ℂ) (S T : ℝ) (hST : S ≤ T) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (i : Fin 3) (f : Test) :
    (∫ x : Maxwell.Space, ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) i*f.val x) +
      (∫ x : Maxwell.Space, DynamicVolume.source c u i x*f.val x) =
      ∫ x : Maxwell.Space, (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*
        ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) i*f.val x := by
  have hw : StaticCoefficient.sqrtMultiplier c (Packet06LocalPencil.response c z S T u) = u := by
    simpa only [sub_zero] using Packet06GreenSource.solved_weighted_response c z S T hST u 0 hc hu
  rw [source_testPair,←testPair_integral,←Packet06GreenPhysical.dielectric_test_integral]
  change testPair i f.val (Packet06LocalPencil.response c z S T u)+
    testPair i f.val (StaticCoefficient.sqrtMultiplier c u) =
      testPair i f.val (Packet06LocalPencil.response c z S T u+
        StaticCoefficient.sqrtMultiplier c (StaticCoefficient.sqrtMultiplier c (Packet06LocalPencil.response c z S T u)))
  rw [hw,map_add]

theorem actual_first_order (c : Coefficient) (z : ℂ) (S T : ℝ)
    (hST : S ≤ T) (hplus : 0 ≤ T+S) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Maxwell.Space → ℂ) ⊆ closedBall 0 T) :
    ((∫ x : Maxwell.Space, ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) (next i) * (testPartial (previous i) f).val x) -
      (∫ x : Maxwell.Space, ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) (previous i) * (testPartial (next i) f).val x) =
        Complex.I*z * (∫ x : Maxwell.Space, ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x i * f.val x)) ∧
    ((∫ x : Maxwell.Space, ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x (next i) * (testPartial (previous i) f).val x) -
      (∫ x : Maxwell.Space, ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x (previous i) * (testPartial (next i) f).val x) =
        -(Complex.I*z) * (∫ x : Maxwell.Space, (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*
          ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) i*f.val x)) := by
  obtain ⟨he,hh⟩ := ComplexMagneticMaxwell.actual_maxwell c S T hplus u hc i f hf z
  rw [kernel_displacement c z S T hST u hc hu i f] at hh
  exact ⟨he,hh⟩

end OQ14.Packet06KernelMaxwell
#print axioms OQ14.Packet06KernelMaxwell.source_testPair
#print axioms OQ14.Packet06KernelMaxwell.kernel_displacement
#print axioms OQ14.Packet06KernelMaxwell.actual_first_order
