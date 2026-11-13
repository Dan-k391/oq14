import Packet06PlacedConjugacy
import Packet06MaterialSector

/-! Actual placed-material pencil in coordinates on the transported electric sector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
namespace OQ14.Packet06PlacedSector
open Metric Maxwell Packet06PlacedKernel Packet06PlacedEquivalence
open Packet06SectorOperator (Sector)

def pencil (c : StaticCoefficient.Coefficient) (R s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) :
    Sector →L[ℂ] Sector :=
  Packet06SectorFamily.compression ((placed s hs a).symm.toContinuousLinearMap.comp
    ((ComplexConvolutionAnalytic.pencil (placedCoefficient s a c) z (R/s+‖a‖)).comp
      (placed s hs a).toContinuousLinearMap))

theorem pencil_scaled (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) :
    pencil c R s hs a ((s : ℂ)*z)=Packet06MaterialSector.pencil c R z := by
  have he : (placed s hs a).symm.toContinuousLinearMap.comp
      ((ComplexConvolutionAnalytic.pencil (placedCoefficient s a c) ((s : ℂ)*z)
        (R/s+‖a‖)).comp (placed s hs a).toContinuousLinearMap) =
        ComplexConvolutionAnalytic.pencil c z R := by
    apply ContinuousLinearMap.ext
    intro u
    change (placed s hs a).symm
      (ComplexConvolutionAnalytic.pencil (placedCoefficient s a c) ((s : ℂ)*z)
        (R/s+‖a‖) (placed s hs a u)) = _
    rw [Packet06PlacedConjugacy.pencil_intertwines c R hR hc s hs a z u,
      ContinuousLinearEquiv.symm_apply_apply]
  rw [pencil,he]
  rfl

theorem pencil_formula (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) :
    pencil c R s hs a z=Packet06MaterialSector.pencil c R (z/(s : ℂ)) := by
  have h := pencil_scaled c R hR hc s hs a (z/(s : ℂ))
  have he : (s : ℂ)*(z/(s : ℂ))=z := by
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    field_simp
  rwa [he] at h

theorem pencil_actual (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) (u : Sector) :
    placed s hs a (pencil c R s hs a z u : V) =
      ComplexConvolutionAnalytic.pencil (placedCoefficient s a c) z (R/s+‖a‖)
        (placed s hs a (u : V)) := by
  rw [pencil_formula c R hR hc s hs a z,
    Packet06MaterialSector.pencil_actual c ha hm R hR hc (z/(s : ℂ)) u]
  have h := Packet06PlacedConjugacy.pencil_intertwines c R hR hc s hs a (z/(s : ℂ)) (u : V)
  have he : (s : ℂ)*(z/(s : ℂ))=z := by
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    field_simp
  rw [he] at h
  exact h.symm

end OQ14.Packet06PlacedSector
#print axioms OQ14.Packet06PlacedSector.pencil_scaled
#print axioms OQ14.Packet06PlacedSector.pencil_formula
#print axioms OQ14.Packet06PlacedSector.pencil_actual
