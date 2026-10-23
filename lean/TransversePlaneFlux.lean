import MaxwellPlaneTail

/-! Exact transverse plane cancellation with radial magnetic error control. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.TransversePlaneFlux
open Maxwell MaxwellRadiation GreenKernel ScalarRadiation
open scoped ComplexConjugate
abbrev Space := FourierL2.Space

def tangentPart (x : Space) (H : Vector) : Vector :=
  crossProduct (crossProduct (direction x) H) (direction x)

theorem radial_error (x : Space) (hx : x≠0) (H : Vector) (i : Fin 3) :
    H i-tangentPart x H i=dot (direction x) H*direction x i := by
  rw [tangentPart,cross_cross_same,direction_dot x hx,one_mul]
  ring

theorem radial_error_bound (x : Space) (hx : x≠0) (H : Vector) (D : ℝ) (hD : 0≤D)
    (hd : ‖dot (direction x) H‖≤D) (i : Fin 3) : ‖H i-tangentPart x H i‖≤D := by
  rw [radial_error x hx H i,norm_mul]
  exact (mul_le_mul hd (unitCoordinate_norm_le i x) (norm_nonneg _) hD).trans_eq (mul_one D)

theorem leading_zero (k : ℝ) (S : Fin 3 → Space → ℂ) (x : Space) (hx : x≠0)
    (hp : x 2=0) (H : Vector) :
    crossProduct (leadingElectric k S x) (conjugate (tangentPart x H)) 2=0 := by
  change leadingElectric k S x 0*conj (tangentPart x H 1)-
    leadingElectric k S x 1*conj (tangentPart x H 0)=0
  rw [← leading_radiation_identity k S x hx 0,← leading_radiation_identity k S x hx 1]
  simp [tangentPart,cross_apply,direction,unitCoordinate,hp]
  ring

end OQ14.TransversePlaneFlux
#print axioms OQ14.TransversePlaneFlux.radial_error
#print axioms OQ14.TransversePlaneFlux.radial_error_bound
#print axioms OQ14.TransversePlaneFlux.leading_zero
