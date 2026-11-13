import Packet06TranslationNewtonPairing

/-! L² translation agrees with literal translation of Schwartz sources. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06TranslationSchwartz
open MeasureTheory Maxwell Packet06TranslationL2
open scoped SchwartzMap

theorem action_schwartz (a : Space) (f : Fin 3 → 𝓢(Space, ℂ)) :
    action a (VectorFourier.schwartzVector f) =
      VectorFourier.schwartzVector (fun i => NewtonConvolution.translate (-a) (f i)) := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have hf := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (VectorFourier.schwartzVector_ae f i)
  have hf' := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving.ae hf
  have hg := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (VectorFourier.schwartzVector_ae (fun i => NewtonConvolution.translate (-a) (f i)) i)
  filter_upwards [action_ae a (VectorFourier.schwartzVector f) i,hf',hg] with x ha hf hg
  rw [ha]
  have hf'' : VectorFourier.schwartzVector f (VectorFourier.coordinateMap (x-a)) i = f i (x-a) := by
    simpa only [sub_eq_add_neg, MeasurableEquiv.symm_apply_apply] using hf
  have hg' : VectorFourier.schwartzVector (fun i => NewtonConvolution.translate (-a) (f i))
      (VectorFourier.coordinateMap x) i = f i (x-a) := by
    simpa only [MeasurableEquiv.symm_apply_apply, NewtonConvolution.translate_apply, sub_eq_add_neg] using hg
  rw [hf'',hg']

end OQ14.Packet06TranslationSchwartz
#print axioms OQ14.Packet06TranslationSchwartz.action_schwartz
