import Packet07DrivenUniformAffineHotspotGeometry
import Packet07ScaleMeasure
import Packet07AffineMaxwell

/-! Almost-everywhere driven fields and their phase traces transport literally. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenUniformAffineAE
open MeasureTheory Set Metric Maxwell Packet07DrivenUniformAffineGeometry Packet07DrivenUniformAffinePhase
abbrev Space := Maxwell.Space

theorem map_qmp (s : ℝ) (hs : 0 < s) (a : Space) :
    Measure.QuasiMeasurePreserving (Packet07AffineGeometry.map s a) volume volume := by
  exact (DilationL2.smul_qmp_space s hs.ne').comp
    ((measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving)

theorem component_image_ae (s : ℝ) (hs : 0 < s) (a : Space) (E : Field)
    (K : Set Space) (hK : MeasurableSet K) (R : Fin 3 → Space → ℂ) (i : Fin 3)
    (hE : (fun x => E x i) =ᵐ[volume.restrict K] R i) :
    (fun x => Packet07AffineMaxwell.affineField s a E x i) =ᵐ[volume.restrict (placement s hs a '' K)]
      transport s hs a R i := by
  have hh := (ae_restrict_iff' hK).mp hE
  have ht := (map_qmp s hs a).ae hh
  have hset : placement s hs a '' K = Packet07AffineGeometry.map s a ⁻¹' K := by
    exact (placement s hs a).image_eq_preimage K
  rw [hset]
  apply (ae_restrict_iff' ((Packet07AffineGeometry.map_continuous s a).measurable hK)).mpr
  filter_upwards [ht] with x hx hxK
  have he := hx hxK
  change (s : ℂ)*E (s • (x-a)) i = (s : ℂ)*R i (s • (x-a))
  change E (s • (x-a)) i = R i (s • (x-a)) at he
  rw [he]
end OQ14.Packet07DrivenUniformAffineAE
#print axioms OQ14.Packet07DrivenUniformAffineAE.map_qmp
#print axioms OQ14.Packet07DrivenUniformAffineAE.component_image_ae
