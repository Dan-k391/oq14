import RestrictedTEDatumLinear

/-! Actual material L2 sources are complex-linear as almost-everywhere density representatives. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.MaterialSourceLinear
open MeasureTheory
abbrev Space := FourierL2.Space
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

theorem add (c : Coefficient) (u v : VectorL2) (j : Fin 3) :
    DynamicVolume.source c (u+v) j =ᵐ[volume]
      fun y : Space => DynamicVolume.source c u j y+DynamicVolume.source c v j y := by
  have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_add u v)
  filter_upwards [h] with y hy
  simp only [DynamicVolume.source,hy,PiLp.add_apply]
  ring

theorem smul (c : Coefficient) (z : ℂ) (u : VectorL2) (j : Fin 3) :
    DynamicVolume.source c (z • u) j =ᵐ[volume]
      fun y : Space => z*DynamicVolume.source c u j y := by
  have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul z u)
  filter_upwards [h] with y hy
  simp only [DynamicVolume.source,hy,PiLp.smul_apply,smul_eq_mul]
  ring

end OQ14.MaterialSourceLinear
#print axioms OQ14.MaterialSourceLinear.add
#print axioms OQ14.MaterialSourceLinear.smul
