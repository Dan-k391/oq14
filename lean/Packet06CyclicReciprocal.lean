import Packet06CyclicComplex
import Packet06PhysicalNormalization

/-! Exact physical reciprocal normalization under cyclic material rotation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06CyclicReciprocal
open Metric Packet06CyclicL2 Packet06CyclicMaterial Packet06PhysicalNormalization

theorem reciprocalNorm_rotation (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : VectorFourier.VectorL2) :
    reciprocalNorm (coefficient c) R z (action u) = reciprocalNorm c R z u := by
  rw [reciprocalNorm_eq_crossing _ _ hR, reciprocalNorm_eq_crossing c R hR,
    Packet06CyclicComplex.derivative_conjugacy c R hR hc, vectorPair_invariant]

theorem kernel_rotation (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : VectorFourier.VectorL2)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z R u = 0) :
    ComplexConvolutionAnalytic.volumeBlock (coefficient c) z R (action u) = 0 := by
  have h := congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 => L u)
    (Packet06CyclicComplex.complex_conjugacy c R hR hc z)
  change ComplexConvolutionAnalytic.volumeBlock (coefficient c) z R (action u) =
    action (ComplexConvolutionAnalytic.volumeBlock c z R u) at h
  rw [hu, map_zero] at h
  exact h

end OQ14.Packet06CyclicReciprocal
#print axioms OQ14.Packet06CyclicReciprocal.reciprocalNorm_rotation
#print axioms OQ14.Packet06CyclicReciprocal.kernel_rotation
