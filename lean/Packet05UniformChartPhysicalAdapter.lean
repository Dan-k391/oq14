import Packet05QuantitativePhysicalBranches
import Packet05NormalFluxUniformCeiling
import Packet05LocalizedChartScalarAdapter
import Packet05NestedTangentialUniform
import Packet05LocalizedNormalFluxBound
import Packet05QuantitativeChartBranches
import Packet05QuantitativePhysicalChart
import Packet05QuantitativeGraphReconstruction
import Packet05ChartElectricIdentity

/-! Continuous graph-phase branches agree with the actual physical electric
field under the signed chart, not merely with an abstract scalar expression. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05UniformChartPhysicalAdapter
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation OQ14.DivCurlCompact
  OQ14.Packet05ChartBasis OQ14.Packet05ChartWeakDivergence OQ14.Packet05ChartElectricIdentity
  OQ14.Packet05ChartCorrectionContinuous OQ14.Packet05GraphPhaseReconstruction
  OQ14.Packet05GraphPullback OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeakDivergence OQ14.Packet05ScalarDielectricFlux OQ14.Packet05FlatWeight
  OQ14.Packet05GraphChartMap OQ14.Packet05PhysicalGraphChart
  OQ14.Packet05NormalFluxOriginalBound OQ14.Packet05MatrixWeakDerivative OQ14.MaxwellCutoffCommutator
  OQ14.Packet05RegionalDivergence OQ14.Packet05PlateauGraphFlux
  OQ14.Packet05RegionalPartial OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05RegionalScalarLocalization
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem uniform_chart_physical_adapter (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (G Q : L2Vector) (B : Fin 3 → ℝ) (hB : ∀ j x, ‖slopeC g j x‖ ≤ B j)
    (A : Fin 3 → Fin 3 → Test) (d : ℝ) (hd : 0 ≤ d) (T : Set Maxwell.Space) (hT : IsOpen T)
    (ε : ℂ) (hε : ε ≠ 0) (hweight : ∀ x ∈ T, weight d x = ε)
    (hmetric : ∀ x ∈ T, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (χ : ContDiffBump (0 : Maxwell.Space)) (W : Field) (hW : ∀ j, Continuous (fun x => W x j))
    (Qeq : Q = chartVector up i (Packet06ScalarGaussLocalization.correction χ W hW))
    (E : Field) (Gphys Qphys : L2Vector) (hG : G = chartVector up i Gphys)
    (hQphys : Qphys = Packet06ScalarGaussLocalization.correction χ W hW)
    (Ω : Set Maxwell.Space)
    (hmap : ∀ x ∈ T, inverseOriented up i (graphMap (liftedHeight g) x) ∈ Ω)
    (hE : ∀ j, ∀ᵐ y ∂volume, y ∈ Ω → Gphys j y+Qphys j y=E y j)
    (Vgrad Wgrad : Set Maxwell.Space) (hVgrad : IsOpen Vgrad) (hWgrad : IsOpen Wgrad)
    (u : L2Scalar) (hC : ∀ j, HasWeakPartial u (pulledGradient g hg G B hB j) j)
    (D0 D1 H00 H01 H10 H11 : L2Vector)
    (hD0 : ∀ j, HasPartialOn Vgrad (pulledGradient g hg G B hB j) (D0 j) 0)
    (hD1 : ∀ j, HasPartialOn Vgrad (pulledGradient g hg G B hB j) (D1 j) 1)
    (κ ζ : RealTest univ) (hκV : tsupport κ.function ⊆ Vgrad) (hκT : ∀ x ∈ T, κ.function x = 1)
    (hζW : ∀ x ∈ Wgrad, ζ.function x = 1)
    (hH00 : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (pulledGradient g hg G B hB 0) D0 j)) (H00 j) 0)
    (hH01 : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (pulledGradient g hg G B hB 0) D0 j)) (H01 j) 1)
    (hH10 : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (pulledGradient g hg G B hB 1) D1 j)) (H10 j) 0)
    (hH11 : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (pulledGradient g hg G B hB 1) D1 j)) (H11 j) 1)
    (θ : Test) (hθW : tsupport θ.function ⊆ Wgrad) (hθT : ∀ x ∈ T, θ.function x = 1)
    (hθ2 : ContDiff ℝ 2 θ.function) (α β γ αk βk L P Qb : ℝ)
    (hα : ∀ x, ‖θ.function x‖ ≤ α) (hβ : ∀ j x, ‖dcoord θ.function x j‖ ≤ β)
    (hγ : ∀ j k x, ‖dcoord (derivativeCutoff θ hθ2 j).function x k‖ ≤ γ)
    (hαk : ∀ x, ‖κ.complexTest.function x‖ ≤ αk) (hβk : ∀ j x, ‖dcoord κ.complexTest.function x j‖ ≤ βk)
    (hL0 : ‖pulledGradient g hg G B hB 0‖ ≤ L) (hL1 : ‖pulledGradient g hg G B hB 1‖ ≤ L)
    (hP0 : ∀ j, ‖D0 j‖ ≤ P) (hP1 : ∀ j, ‖D1 j‖ ≤ P)
    (hQ00 : ∀ j, ‖H00 j‖ ≤ Qb) (hQ01 : ∀ j, ‖H01 j‖ ≤ Qb)
    (hQ10 : ∀ j, ‖H10 j‖ ≤ Qb) (hQ11 : ∀ j, ‖H11 j‖ ≤ Qb)
    (θlocal : Test)
    (C1 F1 : Fin 3 → L2Vector) (C2 F2 : Fin 3 → Fin 3 → L2Vector)
    (Vreg Wreg : Set Maxwell.Space) (hWreg : IsOpen Wreg) (hWV : Wreg ⊆ Vreg)
    (hθlocal : ∀ x ∈ Vreg, θlocal.function x = 1)
    (hdiv : HasDivergenceOn Vreg (fun j => flux A (pulledGradient g hg G B hB) d hd j -
      (-mulWeight d hd (transformedFlux g hg Q B hB j))) 0)
    (hC1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (cutVector θlocal (pulledGradient g hg G B hB) j) (C1 i j) i)
    (hF1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (cutVector θlocal (fun j => -mulWeight d hd (transformedFlux g hg Q B hB j)) j) (F1 i j) i)
    (hC2 : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (C1 i j) (C2 i t j) t)
    (hF2 : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (η ξ : Test) (hηV : tsupport η.function ⊆ Vreg) (hηW : ∀ x ∈ Wreg, η.function x = 1)
    (hξW : tsupport ξ.function ⊆ Wreg) (hξ2 : ContDiff ℝ 2 ξ.function)
    (hTW : T ⊆ Wreg) (hξT : ∀ x ∈ T, ξ.function x = 1)
    (aa bb cc rr ss pp qq tt : ℝ)
    (ha : ∀ i j x, ‖(A i j).function x‖ ≤ aa)
    (hb : ∀ i j k x, ‖dcoord (A i j).function x k‖ ≤ bb)
    (hc : ∀ i j k l x, ‖dcoord (derivativeMatrix A hA2 k i j).function x l‖ ≤ cc)
    (hr : ∀ x, ‖η.function x‖ ≤ rr) (hs : ∀ i x, ‖dcoord η.function x i‖ ≤ ss)
    (hp : ∀ x, ‖ξ.function x‖ ≤ pp) (hq : ∀ i x, ‖dcoord ξ.function x i‖ ≤ qq)
    (ht : ∀ i j x, ‖dcoord (derivativeCutoff ξ hξ2 i).function x j‖ ≤ tt)
    (M K W0 Larr : ℝ) (hM : 0 ≤ M) (hK : ‖ε⁻¹‖ ≤ K)
    (hab : ∀ x ∈ T, |Packet05GraphSlope.slope g 0 x| ≤ M ∧ |Packet05GraphSlope.slope g 1 x| ≤ M)
    (hW0 : ∀ x ∈ T, ‖chartCorrection up i g χ W 0 x‖ ≤ W0 ∧
      ‖chartCorrection up i g χ W 1 x‖ ≤ W0 ∧ ‖chartCorrection up i g χ W 2 x‖ ≤ W0)
    (hLarrC : ∀ j, ‖cutVector θlocal (pulledGradient g hg G B hB) j‖ ≤ Larr)
    (hLarrF : ∀ j, ‖cutVector θlocal (fun j => -mulWeight d hd (transformedFlux g hg Q B hB j)) j‖ ≤ Larr)
    (hLarrC1 : ∀ j k, ‖C1 j k‖ ≤ Larr) (hLarrF1 : ∀ j k, ‖F1 j k‖ ≤ Larr)
    (hLarrC2 : ∀ j k l, ‖C2 j k l‖ ≤ Larr) (hLarrF2 : ∀ j k l, ‖F2 j k l‖ ≤ Larr)
    (haa : 0 ≤ aa) (hbb : 0 ≤ bb) (hcc : 0 ≤ cc) (hrr : 0 ≤ rr) (hss : 0 ≤ ss)
    (hpp : 0 ≤ pp) (hqq : 0 ≤ qq) (htt : 0 ≤ tt) :
    let X := max W0 (max (Packet05ExplicitAnisotropicBound.universalConstant *
      ((α+3*β+6*γ)*αk*L+(α+2*β)*3*(αk*P+βk*L)+6*(α*Qb+β*(αk*P+βk*L))))
      (Packet05NormalFluxUniformCeiling.coefficient d aa bb cc rr ss pp qq tt * Larr))
    ∃ reps : Fin 3 → Maxwell.Space → ℂ, (∀ j, Continuous (reps j)) ∧
      (∀ j, (fun x => E x j) =ᵐ[volume.restrict (Packet05PhysicalChartBranches.physicalFlatMap up i g ⁻¹' T)] reps j) ∧
      ∀ j x, x ∈ Packet05PhysicalChartBranches.physicalFlatMap up i g ⁻¹' T →
        ‖reps j x‖ ≤ (2+(1+M)*(K+4*M+1))*X := by
  dsimp only
  let X := max W0 (max (Packet05ExplicitAnisotropicBound.universalConstant *
      ((α+3*β+6*γ)*αk*L+(α+2*β)*3*(αk*P+βk*L)+6*(α*Qb+β*(αk*P+βk*L))))
      (Packet05NormalFluxUniformCeiling.coefficient d aa bb cc rr ss pp qq tt * Larr))
  have hW0X : W0 ≤ X := le_max_left _ _
  have htbound : Packet05ExplicitAnisotropicBound.universalConstant *
      ((α+3*β+6*γ)*αk*L+(α+2*β)*3*(αk*P+βk*L)+6*(α*Qb+β*(αk*P+βk*L))) ≤ X :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hfluxX : Packet05NormalFluxUniformCeiling.coefficient d aa bb cc rr ss pp qq tt * Larr ≤ X := by
    dsimp [X]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hfluxbound := (Packet05NormalFluxUniformCeiling.uniform_flux_ceiling
    (cutVector θlocal (pulledGradient g hg G B hB))
    (cutVector θlocal (fun j => -mulWeight d hd (transformedFlux g hg Q B hB j)))
    C1 F1 C2 F2 d aa bb cc rr ss pp qq tt Larr hd haa hbb hcc hrr hss hpp hqq htt
    hLarrC hLarrF hLarrC1 hLarrF1 hLarrC2 hLarrF2).trans hfluxX
  obtain ⟨f0,hf0,h0,hf0bound⟩ := Packet05NestedTangentialUniform.nested_tangential_uniform
    Vgrad Wgrad T hVgrad hWgrad hT u (pulledGradient g hg G B hB) hC 0 D0 H00 H01 hD0
    κ ζ hκV hκT hζW hH00 hH01 θ hθW hθT hθ2 α β γ αk βk L P Qb
    hα hβ hγ hαk hβk hL0 hP0 hQ00 hQ01
  obtain ⟨f1,hf1,h1,hf1bound⟩ := Packet05NestedTangentialUniform.nested_tangential_uniform
    Vgrad Wgrad T hVgrad hWgrad hT u (pulledGradient g hg G B hB) hC 1 D1 H10 H11 hD1
    κ ζ hκV hκT hζW hH10 hH11 θ hθW hθT hθ2 α β γ αk βk L P Qb
    hα hβ hγ hαk hβk hL1 hP1 hQ10 hQ11
  apply Packet05LocalizedChartScalarAdapter.localized_chart_scalar_adapter
    up i g hg G Q B hB A d hd T hT ε hε hweight hmetric χ W hW Qeq E Gphys Qphys hG hQphys Ω hmap hE
    f0 f1 hf0 hf1 h0 h1 θlocal C1 F1 C2 F2 Vreg Wreg hWreg hWV hθlocal hdiv hC1 hF1 hC2 hF2 hA2 hA3
    η ξ hηV hηW hξW hξ2 hTW hξT aa bb cc rr ss pp qq tt ha hb hc hr hs hp hq ht M K X hM hK hab
  · intro x hx
    obtain ⟨h2,h3,h4⟩ := hW0 x hx
    exact ⟨(hf0bound x).trans htbound,(hf1bound x).trans htbound,
      h2.trans hW0X,h3.trans hW0X,h4.trans hW0X⟩
  · exact hfluxbound

end OQ14.Packet05UniformChartPhysicalAdapter
#print axioms OQ14.Packet05UniformChartPhysicalAdapter.uniform_chart_physical_adapter
