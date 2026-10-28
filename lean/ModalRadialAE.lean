import ModalRadialLift
import PolarMomentAE
noncomputable section
set_option autoImplicit false
namespace OQ14.ModalRadialAE
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower OQ14.PolarIntegration
open scoped Topology

theorem radial_ae {P : ℝ → Prop} (h : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), P r) :
    ∀ᵐ x : Space ∂volume, P ‖x‖ := by
  have hsub : ∀ᵐ r : Radius ∂(volume.comap ((↑) : Radius → ℝ)), P r :=
    (ae_restrict_iff_subtype measurableSet_Ioi).mp h
  have hd : Measurable (fun r : Radius => ENNReal.ofReal ((r : ℝ)^2)) :=
    ENNReal.measurable_ofReal.comp (measurable_subtype_coe.pow_const 2)
  have hrad : ∀ᵐ r : Radius ∂radialMeasure, P r := by
    apply (ae_withDensity_iff hd).mpr
    filter_upwards [hsub] with r hr
    exact fun _ => hr
  have hprod : ∀ᵐ p : Sphere × Radius ∂angularMeasure.prod radialMeasure, P p.2 := by
    exact Measure.quasiMeasurePreserving_snd.ae hrad
  have hp := polar_measurePreserving.quasiMeasurePreserving.ae hprod
  have hp' : ∀ᵐ x : Punctured ∂(volume.comap ((↑) : Punctured → Space)), P ‖(x : Space)‖ := by
    simpa only [homeomorphUnitSphereProd_apply_snd_coe] using hp
  have hrest : ∀ᵐ x : Space ∂volume.restrict ({0}ᶜ : Set Space), P ‖x‖ :=
    (ae_restrict_iff_subtype (measurableSet_singleton (0 : Space)).compl).mpr hp'
  simpa only [restrict_compl_singleton] using hrest

#print axioms OQ14.ModalRadialAE.radial_ae
end OQ14.ModalRadialAE


