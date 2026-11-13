import Packet05DifferentiatedNormalFluxH1
import Packet05CurlSourceH1

/-! Nested cutoffs preserve the actual weak derivative on a plateau. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05CutoffPlateauDerivative
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05CurlSourceH1
open scoped Topology

theorem cutoff_derivative_plateau (W : Set Space) (hW : IsOpen W) (η χ : Test)
    (hη : ∀ x ∈ W, η.function x = 1) (hχ : tsupport χ.function ⊆ W)
    (u Du : L2Scalar) (i : Fin 3) :
    scaleL2 χ.function χ.regular.continuous χ.compact (cutoffProductDerivative η u Du i) =
      scaleL2 χ.function χ.regular.continuous χ.compact Du := by
  apply Lp.ext
  filter_upwards [scaleL2_ae χ.function χ.regular.continuous χ.compact (cutoffProductDerivative η u Du i),
    scaleL2_ae χ.function χ.regular.continuous χ.compact Du,
    Lp.coeFn_add (scaleL2 η.function η.regular.continuous η.compact Du)
      (scaleL2 (fun x => dcoord η.function x i) (partial_continuous η.regular i)
        (η.compact.fderiv_apply ℝ (basis i)) u),
    scaleL2_ae η.function η.regular.continuous η.compact Du,
    scaleL2_ae (fun x => dcoord η.function x i) (partial_continuous η.regular i)
      (η.compact.fderiv_apply ℝ (basis i)) u] with x ha hb hc hd he
  rw [ha,hb]
  by_cases hx : x ∈ W
  · have heq : η.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
      filter_upwards [hW.mem_nhds hx] with y hy
      exact hη y hy
    have hz : dcoord η.function x i = 0 := by
      simp [dcoord, heq.fderiv_eq]
    change χ.function x * (scaleL2 η.function η.regular.continuous η.compact Du +
      scaleL2 (fun x => dcoord η.function x i) (partial_continuous η.regular i)
        (η.compact.fderiv_apply ℝ (basis i)) u : L2Scalar) x = _
    rw [hc]
    simp only [Pi.add_apply]
    rw [hd,he,hη x hx,hz]
    simp
  · have hn : x ∉ tsupport χ.function := fun h => hx (hχ h)
    have hz : χ.function x = 0 := image_eq_zero_of_nmem_tsupport hn
    simp [hz]

end OQ14.Packet05CutoffPlateauDerivative
#print axioms OQ14.Packet05CutoffPlateauDerivative.cutoff_derivative_plateau
