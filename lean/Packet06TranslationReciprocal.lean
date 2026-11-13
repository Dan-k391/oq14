import Packet06TranslationComplex
import Packet06PhysicalNormalization

/-! Exact physical reciprocal normalization under actual rigid translation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06TranslationReciprocal
open Metric Maxwell Packet06TranslationL2 Packet06TranslationMaterial Packet06PhysicalNormalization

theorem reciprocalNorm_translation (a : Space) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : VectorFourier.VectorL2) :
    reciprocalNorm (coefficient a c) (R+‖a‖) z (action a u) = reciprocalNorm c R z u := by
  rw [reciprocalNorm_eq_crossing _ _ (by positivity), reciprocalNorm_eq_crossing c R hR,
    Packet06TranslationComplex.derivative_conjugacy a c R hR hc, vectorPair_invariant]

theorem kernel_translation (a : Space) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : VectorFourier.VectorL2)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z R u = 0) :
    ComplexConvolutionAnalytic.volumeBlock (coefficient a c) z (R+‖a‖) (action a u) = 0 := by
  have h := congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 => L u)
    (Packet06TranslationComplex.complex_conjugacy a c R hR hc z)
  change ComplexConvolutionAnalytic.volumeBlock (coefficient a c) z (R+‖a‖) (action a u) =
    action a (ComplexConvolutionAnalytic.volumeBlock c z R u) at h
  rw [hu, map_zero] at h
  exact h

end OQ14.Packet06TranslationReciprocal
#print axioms OQ14.Packet06TranslationReciprocal.reciprocalNorm_translation
#print axioms OQ14.Packet06TranslationReciprocal.kernel_translation
