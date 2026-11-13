import Packet05ChartConstitutive
import Packet05ModeCorrectionH2

/-! The exact correction representative in the actual mode scalar adapter
has H² in each component, and remains H² in any signed Cartesian chart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ModeCorrectionAdapter
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.ConicalGradientGraph OQ14.Packet05ModeCorrectionH2
  OQ14.Packet05GraphPiolaH2 OQ14.Packet05ChartH2 OQ14.Packet05ChartWeakDivergence

def bumpTest (χ : ContDiffBump (0 : Maxwell.Space)) : Test where
  function := bump χ
  regular := Complex.ofRealCLM.contDiff.comp (χ.contDiff : ContDiff ℝ 1 (χ : Maxwell.Space → ℝ))
  compact := χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

theorem bumpTest_c2 (χ : ContDiffBump (0 : Maxwell.Space)) : ContDiff ℝ 2 (bumpTest χ).function :=
  Complex.ofRealCLM.contDiff.comp (χ.contDiff : ContDiff ℝ 2 (χ : Maxwell.Space → ℝ))

theorem bumpTest_support (χ : ContDiffBump (0 : Maxwell.Space)) :
    tsupport (bumpTest χ).function ⊆ ball (0 : Maxwell.Space) (χ.rOut+1) := by
  have he : Function.support (bumpTest χ).function = Function.support (χ : Maxwell.Space → ℝ) := by
    ext x
    change ((χ x : ℝ) : ℂ) ≠ 0 ↔ χ x ≠ 0
    exact not_congr Complex.ofReal_eq_zero
  rw [tsupport,he]
  change tsupport (χ : Maxwell.Space → ℝ) ⊆ _
  rw [χ.tsupport_eq]
  exact closedBall_subset_ball (by linarith)

theorem actual_correction_h2 (c : StaticCoefficient.Coefficient) (z : ℂ)
    (S : ℝ) (u : VectorFourier.VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (χ : ContDiffBump (0 : Maxwell.Space)) :
    let W := Packet06ComplexPotential.correction z (DynamicVolume.source c u)
    let hW := Packet06ComplexPotential.correction_continuous z S (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
    ∀ j, HasH2 (Packet06ScalarGaussLocalization.correction χ W hW j) := by
  dsimp only
  intro j
  obtain ⟨U,G,H,hG,hH,hU⟩ := mode_correction_compact_h2 c z S (χ.rOut+1) u hc
    (bumpTest χ) (bumpTest_c2 χ) (bumpTest_support χ) j
  have heq : U = Packet06ScalarGaussLocalization.correction χ
      (Packet06ComplexPotential.correction z (DynamicVolume.source c u))
      (Packet06ComplexPotential.correction_continuous z S (StaticCoefficient.sqrtMultiplier c u)
        (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)) j := by
    apply Lp.ext
    filter_upwards [hU, Packet06ScalarGaussLocalization.correction_ae χ
      (Packet06ComplexPotential.correction z (DynamicVolume.source c u))
      (Packet06ComplexPotential.correction_continuous z S (StaticCoefficient.sqrtMultiplier c u)
        (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)) j] with x ha hb
    simpa [bumpTest] using ha.trans hb.symm
  rw [← heq]
  exact ⟨G,H,hG,hH⟩

end OQ14.Packet05ModeCorrectionAdapter
#print axioms OQ14.Packet05ModeCorrectionAdapter.bumpTest_c2
#print axioms OQ14.Packet05ModeCorrectionAdapter.bumpTest_support
#print axioms OQ14.Packet05ModeCorrectionAdapter.actual_correction_h2
