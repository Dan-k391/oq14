import Packet06AxialPencilTransport
import Packet06PlacedSector

/-! Generic coordinate invariance of a sector-compressed actual pencil under
an arbitrary full-space intertwining equivalence. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06GenericSectorConjugate
open Packet06SectorOperator (Sector)
abbrev V := VectorFourier.VectorL2

def conjugate (e : V ≃L[ℂ] V) (A : V →L[ℂ] V) : V →L[ℂ] V :=
  e.symm.toContinuousLinearMap.comp (A.comp e.toContinuousLinearMap)

theorem conjugate_eq (e : V ≃L[ℂ] V) (A B : V →L[ℂ] V)
    (h : ∀ x, A (e x) = e (B x)) : conjugate e A = B := by
  apply ContinuousLinearMap.ext
  intro x
  change e.symm (A (e x)) = B x
  rw [h,e.symm_apply_apply]

theorem sector_conjugate_eq (e : V ≃L[ℂ] V) (A B : V →L[ℂ] V)
    (h : ∀ x, A (e x) = e (B x)) :
    Packet06SectorFamily.compression (conjugate e A) = Packet06SectorFamily.compression B := by
  rw [conjugate_eq e A B h]

theorem axial_pencil_conjugate (θ : ℝ) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ Metric.closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) :
    conjugate (Packet06AxialEquivalence.equivalence θ)
      (ComplexConvolutionAnalytic.pencil (Packet06AxialMaterialTransport.coefficient θ c) z R) =
      ComplexConvolutionAnalytic.pencil c z R := by
  apply conjugate_eq
  intro u
  exact Packet06AxialPencilTransport.pencil_intertwines θ c R hR hc z u

theorem nested_sector_conjugate (e f : V ≃L[ℂ] V) (A B : V →L[ℂ] V)
    (h : ∀ x, A (e x) = e (B x)) :
    Packet06SectorFamily.compression (conjugate f (conjugate e A)) =
      Packet06SectorFamily.compression (conjugate f B) := by
  rw [conjugate_eq e A B h]

end OQ14.Packet06GenericSectorConjugate
#print axioms OQ14.Packet06GenericSectorConjugate.conjugate_eq
#print axioms OQ14.Packet06GenericSectorConjugate.sector_conjugate_eq
#print axioms OQ14.Packet06GenericSectorConjugate.axial_pencil_conjugate
#print axioms OQ14.Packet06GenericSectorConjugate.nested_sector_conjugate
