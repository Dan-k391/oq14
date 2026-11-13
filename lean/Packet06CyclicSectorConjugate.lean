import Packet06GenericSectorConjugate
import Packet06PlacedPole

/-! The actual complex pencil under one and two cyclic rotations, expressed
in any pre-existing transported-sector coordinates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06CyclicSectorConjugate
open Metric Maxwell Packet06PlacedKernel Packet06PlacedEquivalence Packet06GenericSectorConjugate
abbrev V := VectorFourier.VectorL2

def cy : V ≃L[ℂ] V := placed 1 (by norm_num) 0

theorem one_support (c : StaticCoefficient.Coefficient) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0) :
    ∀ x : Space, x ∉ closedBall 0 R → (placedCoefficient 1 0 c).value (VectorFourier.coordinateMap x)=0 := by
  simpa using Packet06PlacedPole.coefficient_support c R hc 1 (by norm_num) 0

theorem cyclic_intertwines (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : V) :
    ComplexConvolutionAnalytic.pencil (placedCoefficient 1 0 c) z R (cy u) =
      cy (ComplexConvolutionAnalytic.pencil c z R u) := by
  simpa only [cy,Complex.ofReal_one,one_mul,div_one,norm_zero,add_zero] using
    Packet06PlacedConjugacy.pencil_intertwines c R hR hc 1 (by norm_num) 0 z u

theorem cyclic_pencil_conjugate (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) :
    conjugate cy (ComplexConvolutionAnalytic.pencil (placedCoefficient 1 0 c) z R) =
      ComplexConvolutionAnalytic.pencil c z R :=
  conjugate_eq cy _ _ (cyclic_intertwines c R hR hc z)

theorem twice_sector_conjugate (e : V ≃L[ℂ] V) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) :
    Packet06SectorFamily.compression (conjugate e (conjugate cy (conjugate cy
      (ComplexConvolutionAnalytic.pencil (placedCoefficient 1 0 (placedCoefficient 1 0 c)) z R)))) =
    Packet06SectorFamily.compression (conjugate e (ComplexConvolutionAnalytic.pencil c z R)) := by
  rw [cyclic_pencil_conjugate (placedCoefficient 1 0 c) R hR (one_support c R hc) z,
    cyclic_pencil_conjugate c R hR hc z]
end OQ14.Packet06CyclicSectorConjugate
#print axioms OQ14.Packet06CyclicSectorConjugate.one_support
#print axioms OQ14.Packet06CyclicSectorConjugate.cyclic_intertwines
#print axioms OQ14.Packet06CyclicSectorConjugate.cyclic_pencil_conjugate
#print axioms OQ14.Packet06CyclicSectorConjugate.twice_sector_conjugate
