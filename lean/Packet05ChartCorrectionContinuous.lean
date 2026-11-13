import Packet05GraphPhaseReconstruction
import Packet05ChartConstitutive

/-! The actual continuous physical correction remains a continuous explicit
representative after signed Cartesian and graph transformations. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ChartCorrectionContinuous
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.ConicalGradientGraph
  OQ14.Packet05ChartBasis OQ14.Packet05ChartLinearEquiv OQ14.Packet05ChartConstitutive
  OQ14.Packet05GraphChartMap OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphSmooth
  OQ14.Packet05GraphVolume OQ14.Packet05GraphPullback
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def chartCorrection (up : Bool) (i : Fin 3) (g : Plane → ℝ)
    (χ : ContDiffBump (0 : Maxwell.Space)) (W : Field) (j : Fin 3) (x : Maxwell.Space) : ℂ :=
  let y := inverseOriented up i (graphMap (liftedHeight g) x)
  (chartSign up j : ℂ) * bump χ y * W y (Equiv.swap i 2 j)

theorem chartCorrection_continuous (up : Bool) (i : Fin 3) (g : Plane → ℝ)
    (hg : ContDiff ℝ 2 g) (χ : ContDiffBump (0 : Maxwell.Space)) (W : Field)
    (hW : ∀ j, Continuous (fun x => W x j)) (j : Fin 3) :
    Continuous (chartCorrection up i g χ W j) := by
  have hm : Continuous (fun x => inverseOriented up i (graphMap (liftedHeight g) x)) :=
    ((orientedHomeomorph up i).symm.continuous).comp (graphMap_contDiff g hg).continuous
  have hb : Continuous (bump χ) := Complex.continuous_ofReal.comp χ.continuous
  exact (continuous_const.mul (hb.comp hm)).mul ((hW _).comp hm)

theorem chartCorrection_ae (up : Bool) (i : Fin 3) (g : Plane → ℝ)
    (hg : ContDiff ℝ 2 g) (χ : ContDiffBump (0 : Maxwell.Space)) (W : Field)
    (hW : ∀ j, Continuous (fun x => W x j)) (j : Fin 3) :
    (fun x => pullback g hg.continuous
      (OQ14.Packet05ChartWeakDivergence.chartVector up i (Packet06ScalarGaussLocalization.correction χ W hW) j) x)
      =ᵐ[volume] chartCorrection up i g χ W j := by
  have hc := chartVector_ae up i j (Packet06ScalarGaussLocalization.correction χ W hW)
  have hc' := (graph_map_volume_preserving g hg.continuous).quasiMeasurePreserving.ae hc
  have hphys := Packet06ScalarGaussLocalization.correction_ae χ W hW (Equiv.swap i 2 j)
  have hphys' := (OQ14.Packet05ChartLinearEquiv.oriented_inverse_measure_preserving up i).quasiMeasurePreserving.ae hphys
  have hphys'' := (graph_map_volume_preserving g hg.continuous).quasiMeasurePreserving.ae hphys'
  filter_upwards [pullback_ae g hg.continuous
    (OQ14.Packet05ChartWeakDivergence.chartVector up i (Packet06ScalarGaussLocalization.correction χ W hW) j),
    hc',hphys''] with x ha hb hc
  rw [ha,hb,hc]
  simp [chartCorrection,mul_assoc]

end OQ14.Packet05ChartCorrectionContinuous
#print axioms OQ14.Packet05ChartCorrectionContinuous.chartCorrection_continuous
#print axioms OQ14.Packet05ChartCorrectionContinuous.chartCorrection_ae
