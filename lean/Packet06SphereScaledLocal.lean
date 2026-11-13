import Packet06SphereLocalField

/-! The normalized sphere response retains its actual interior representative. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06SphereScaledLocal
open MeasureTheory Metric Packet06SectorOperator

theorem response_inner_scaled_ae (n : ℝ) (hn : 1 < n) (z a : ℂ) (hz : z ≠ 0)
    (hdet : ModalAlgebra.tmDet 1 (n : ℂ) z=0) (T : ℝ) (hT : 1 ≤ T) (i : Fin 3) :
    (fun x : Maxwell.Space => Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn)
      z 1 T (a • (numerator n hn z : VectorL2)) (VectorFourier.coordinateMap x) i)
      =ᵐ[volume.restrict (ball 0 1)] fun x => Packet06SphereLocalField.inner n z a x i := by
  let F := Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z 1 T (numerator n hn z)
  have ha := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul a F)
  have hf := Packet06SphereLocalField.response_inner_ae n hn z hz hdet T hT i
  simp only [map_smul]
  filter_upwards [ae_restrict_of_ae ha,hf] with x hx he
  change (a • F) (VectorFourier.coordinateMap x) i=_
  rw [hx]
  change a*F (VectorFourier.coordinateMap x) i=_
  rw [he]
  simp only [Packet06SphereLocalField.inner,one_mul]
  ring

end OQ14.Packet06SphereScaledLocal
#print axioms OQ14.Packet06SphereScaledLocal.response_inner_scaled_ae
