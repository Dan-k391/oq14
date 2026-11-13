import Packet05ChartCorrectionContinuous

/-! The charted L² gradient-plus-correction field agrees with the actual
physical electric field after the signed permutation and graph shear. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedTactic false
namespace OQ14.Packet05ChartElectricIdentity
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05ChartBasis OQ14.Packet05ChartLinearEquiv OQ14.Packet05ChartConstitutive
  OQ14.Packet05GraphChartMap OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphVolume
  OQ14.Packet05GraphPullback
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def orientedElectric (up : Bool) (i : Fin 3) (g : Plane → ℝ) (E : Field)
    (x : Maxwell.Space) (j : Fin 3) : ℂ :=
  (chartSign up j : ℂ) * E (inverseOriented up i (graphMap (liftedHeight g) x)) (Equiv.swap i 2 j)

theorem chart_electric_ae (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (Ω T : Set Maxwell.Space) (hT : IsOpen T) (G Q : L2Vector) (E : Field)
    (hmap : ∀ x ∈ T, inverseOriented up i (graphMap (liftedHeight g) x) ∈ Ω)
    (hE : ∀ j, ∀ᵐ y ∂volume, y ∈ Ω → G j y+Q j y=E y j) (j : Fin 3) :
    (fun x => pullback g hg.continuous (OQ14.Packet05ChartWeakDivergence.chartVector up i G j) x +
      pullback g hg.continuous (OQ14.Packet05ChartWeakDivergence.chartVector up i Q j) x)
      =ᵐ[volume.restrict T] fun x => orientedElectric up i g E x j := by
  have he := (oriented_inverse_measure_preserving up i).quasiMeasurePreserving.ae (hE (Equiv.swap i 2 j))
  have he' := (graph_map_volume_preserving g hg.continuous).quasiMeasurePreserving.ae he
  have hg' := (graph_map_volume_preserving g hg.continuous).quasiMeasurePreserving.ae (chartVector_ae up i j G)
  have hq' := (graph_map_volume_preserving g hg.continuous).quasiMeasurePreserving.ae (chartVector_ae up i j Q)
  apply (ae_restrict_iff' hT.measurableSet).mpr
  filter_upwards [he',hg',hq',pullback_ae g hg.continuous (OQ14.Packet05ChartWeakDivergence.chartVector up i G j),
    pullback_ae g hg.continuous (OQ14.Packet05ChartWeakDivergence.chartVector up i Q j)] with x he hg' hq' hg'' hq'' hx
  rw [hg'',hq'',hg',hq']
  change (chartSign up j : ℂ) * G (Equiv.swap i 2 j) (inverseOriented up i (graphMap (liftedHeight g) x)) +
    (chartSign up j : ℂ) * Q (Equiv.swap i 2 j) (inverseOriented up i (graphMap (liftedHeight g) x)) = _
  rw [← mul_add, he (hmap x hx)]
  rfl

end OQ14.Packet05ChartElectricIdentity
#print axioms OQ14.Packet05ChartElectricIdentity.chart_electric_ae
