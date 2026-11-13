import Packet05NormalFluxContinuity
import Packet05RegionalScalarLocalization

/-! A localized scalar gradient agrees with its uncut gradient on a plateau. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05LocalizedGradientPlateau
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.DivCurlCompact OQ14.Packet05RegionalScalarLocalization
  OQ14.Packet05ScalarPrincipalLocalization OQ14.Packet05ScalarCutoffTesting
open scoped Topology

theorem localized_gradient_plateau (W : Set Space) (hW : IsOpen W)
    (κ : RealTest Set.univ) (hκ : ∀ x ∈ W, κ.function x = 1)
    (v : L2Scalar) (G : L2Vector) (j : Fin 3) :
    ∀ᵐ x ∂volume, x ∈ W → localizedGradient κ v G j x = G j x := by
  filter_upwards [cutVector_ae κ G j,
    scaleL2_ae (fun x => dcoord κ.complexTest.function x j)
      (partial_continuous κ.complexTest.regular j)
      (κ.complexTest.compact.fderiv_apply ℝ (basis j)) v,
    Lp.coeFn_add (cutVector κ G j) (cutoffCorrection κ v j)] with x ha hb hc hx
  have heq : κ.complexTest.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    simp [RealTest.complexTest,hκ y hy]
  have hz : dcoord κ.complexTest.function x j = 0 := by
    simp [dcoord,heq.fderiv_eq]
  change (cutVector κ G j + cutoffCorrection κ v j : L2Scalar) x = _
  rw [hc]
  simp only [Pi.add_apply]
  change cutVector κ G j x + scaleL2 (fun x => dcoord κ.complexTest.function x j)
    (partial_continuous κ.complexTest.regular j) (κ.complexTest.compact.fderiv_apply ℝ (basis j)) v x = _
  rw [ha,hb,hκ x hx,hz]
  simp

end OQ14.Packet05LocalizedGradientPlateau
#print axioms OQ14.Packet05LocalizedGradientPlateau.localized_gradient_plateau
