import Packet07DrivenFrameMaxwell
import Packet07SelectedRadiation
import MagneticLocal

/-! The literal driven volume solution satisfies the local hypotheses for frame transport. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenActualGood
open MeasureTheory Metric Maxwell MaterialMaxwell Packet07DrivenFrameMaxwell
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem actual_good {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k : ℝ) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing) (j : ℕ) :
    Good (k : ℂ) (dielectric (g.rounded j)) (g.electric k j input) (g.magnetic k j input) := by
  let c := g.rounded j
  let I := FiniteAngularHerglotz.incident k input
  let u := Packet07SelectedRadiation.actualUnknown g k j input
  let f := ConicalBallExtension.weighted c g.enclosing (ConicalEntireGauge.restricted g.enclosing I)
  have hc := ConicalCommonBinaryPeaks.support g.dataFamily g.radii g.centers d g.contrast_pos.le
    g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.outer_enclosed j
  have hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius c g.enclosing :=
    hk.trans (MaterialVolumeLimit.commonRadius_le c d g.enclosing le_rfl)
  have hsol : DynamicVolume.volumeBlock c k g.enclosing u=f :=
    ConicalMaterialRunge.solution_equation c k g.enclosing g.enclosing_nonnegative hfreq _
  have hincident := ConicalMaterialRunge.weighted_actual c g.enclosing _ I.E hc
    (ConicalEntireGauge.restricted_ae g.enclosing I)
  have hE : ∀ i, LocallyIntegrable (fun x => g.electric k j input x i) := by
    intro i
    exact (I.smoothE i).continuous.locallyIntegrable.add
      (MaterialField.scattered_locallyIntegrable c k g.enclosing u hc i)
  have hH : ∀ i, LocallyIntegrable (fun x => g.magnetic k j input x i) := by
    intro i
    exact (I.smoothH i).continuous.locallyIntegrable.add
      (MagneticLocal.magnetic_locallyIntegrable k g.enclosing (StaticCoefficient.sqrtMultiplier c u)
        (DynamicVolume.source c u) (DynamicVolume.source_integrable c u g.enclosing hc)
        (DynamicVolume.source_zero c u g.enclosing hc) (StaticNewton.material_source_ae c u) i)
  have hεE : ∀ i, LocallyIntegrable (fun x => (dielectric c x : ℂ)*g.electric k j input x i) := by
    intro i
    have hh := (hE i).add ((DynamicVolume.source_integrable c u g.enclosing hc i).locallyIntegrable)
    apply locallyIntegrable_iff.mpr
    intro K hK
    apply (hh.integrableOn_isCompact hK).congr
    filter_upwards [ae_restrict_of_ae (MaterialField.material_relation c k g.enclosing u f I.E hc hincident hsol i)] with x hx
    change g.electric k j input x i+DynamicVolume.source c u i x = (dielectric c x : ℂ)*g.electric k j input x i
    rw [hx]
    have he : MaterialField.total c k u I.E x i = g.electric k j input x i := rfl
    rw [he]
    simp only [dielectric,Complex.ofReal_add,Complex.ofReal_one]
    ring
  have hM := ConicalCommonBinaryPeaks.rounded_maxwell g.dataFamily g.radii g.centers d g.contrast_pos.le
    g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing k g.enclosing_nonnegative hk g.outer_enclosed j I
  exact ⟨hE,hH,hεE,hM⟩
end OQ14.Packet07DrivenActualGood
#print axioms OQ14.Packet07DrivenActualGood.actual_good
