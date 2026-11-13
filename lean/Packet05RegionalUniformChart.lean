import Packet05QuantitativePhysicalBranches
import Packet05UniformChartPhysicalAdapter
import Packet05PairedArrayCeiling
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
namespace OQ14.Packet05RegionalUniformChart
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation OQ14.DivCurlCompact
  OQ14.Packet05ChartBasis OQ14.Packet05ChartWeakDivergence OQ14.Packet05ChartElectricIdentity
  OQ14.Packet05ChartCorrectionContinuous OQ14.Packet05GraphPhaseReconstruction
  OQ14.Packet05GraphPullback OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeakDivergence OQ14.Packet05ScalarDielectricFlux OQ14.Packet05FlatWeight
  OQ14.Packet05GraphChartMap OQ14.Packet05PhysicalGraphChart
  OQ14.Packet05NormalFluxOriginalBound OQ14.Packet05MatrixWeakDerivative OQ14.MaxwellCutoffCommutator
  OQ14.Packet05RegionalDivergence OQ14.Packet05PlateauGraphFlux
  OQ14.Packet05QuantitativeLocalArrays OQ14.Packet05PairedArrayCeiling
  OQ14.Packet05RegionalPartial OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05RegionalScalarLocalization
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem regional_uniform_chart (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
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
    (DC DF : Fin 3 → L2Vector) (HC HF : Fin 3 → Fin 3 → L2Vector)
    (Vlocal : Set Maxwell.Space) (hθlocal2 : ContDiff ℝ 2 θlocal.function) (hθlocalV : tsupport θlocal.function ⊆ Vlocal)
    (hDC : ∀ j, j ≠ 2 → ∀ k, HasPartialOn Vlocal (pulledGradient g hg G B hB k) (DC j k) j)
    (hDF : ∀ j, j ≠ 2 → ∀ k, HasPartialOn Vlocal (-mulWeight d hd (transformedFlux g hg Q B hB k)) (DF j k) j)
    (hHC : ∀ j, j ≠ 2 → ∀ t, t ≠ 2 → ∀ k, HasPartialOn Vlocal (DC j k) (HC j t k) t)
    (hHF : ∀ j, j ≠ 2 → ∀ t, t ≠ 2 → ∀ k, HasPartialOn Vlocal (DF j k) (HF j t k) t)
    (Aθ Bθ Cθ C0 C1b C2b F0 F1b F2b : ℝ)
    (hAθ : ∀ x, ‖θlocal.function x‖ ≤ Aθ) (hBθ : ∀ j x, ‖dcoord θlocal.function x j‖ ≤ Bθ)
    (hCθ : ∀ j k x, ‖dcoord (derivativeCutoff θlocal hθlocal2 j).function x k‖ ≤ Cθ)
    (hC0b : ∀ j, ‖pulledGradient g hg G B hB j‖ ≤ C0) (hC1b : ∀ j k, ‖DC j k‖ ≤ C1b)
    (hC2b : ∀ j k l, ‖HC j k l‖ ≤ C2b)
    (hF0b : ∀ j, ‖(-mulWeight d hd (transformedFlux g hg Q B hB j) : L2Scalar)‖ ≤ F0)
    (hF1b : ∀ j k, ‖DF j k‖ ≤ F1b) (hF2b : ∀ j k l, ‖HF j k l‖ ≤ F2b)
    (Vreg Wreg : Set Maxwell.Space) (hWreg : IsOpen Wreg) (hWV : Wreg ⊆ Vreg)
    (hθlocal : ∀ x ∈ Vreg, θlocal.function x = 1)
    (hdiv : HasDivergenceOn Vreg (fun j => flux A (pulledGradient g hg G B hB) d hd j -
      (-mulWeight d hd (transformedFlux g hg Q B hB j))) 0)
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
    (M K W0 : ℝ) (hM : 0 ≤ M) (hK : ‖ε⁻¹‖ ≤ K)
    (hab : ∀ x ∈ T, |Packet05GraphSlope.slope g 0 x| ≤ M ∧ |Packet05GraphSlope.slope g 1 x| ≤ M)
    (hW0 : ∀ x ∈ T, ‖chartCorrection up i g χ W 0 x‖ ≤ W0 ∧
      ‖chartCorrection up i g χ W 1 x‖ ≤ W0 ∧ ‖chartCorrection up i g χ W 2 x‖ ≤ W0)
    (haa : 0 ≤ aa) (hbb : 0 ≤ bb) (hcc : 0 ≤ cc) (hrr : 0 ≤ rr) (hss : 0 ≤ ss)
    (hpp : 0 ≤ pp) (hqq : 0 ≤ qq) (htt : 0 ≤ tt) :
    let Larr := max (Packet05AssembledArrayCeiling.ceiling Aθ Bθ Cθ C0 C1b C2b)
      (Packet05AssembledArrayCeiling.ceiling Aθ Bθ Cθ F0 F1b F2b)
    let X := max W0 (max (Packet05ExplicitAnisotropicBound.universalConstant *
      ((α+3*β+6*γ)*αk*L+(α+2*β)*3*(αk*P+βk*L)+6*(α*Qb+β*(αk*P+βk*L))))
      (Packet05NormalFluxUniformCeiling.coefficient d aa bb cc rr ss pp qq tt * Larr))
    ∃ reps : Fin 3 → Maxwell.Space → ℂ, (∀ j, Continuous (reps j)) ∧
      (∀ j, (fun x => E x j) =ᵐ[volume.restrict (Packet05PhysicalChartBranches.physicalFlatMap up i g ⁻¹' T)] reps j) ∧
      ∀ j x, x ∈ Packet05PhysicalChartBranches.physicalFlatMap up i g ⁻¹' T →
        ‖reps j x‖ ≤ (2+(1+M)*(K+4*M+1))*X := by
  dsimp only
  let C := pulledGradient g hg G B hB
  let F : L2Vector := fun j => -mulWeight d hd (transformedFlux g hg Q B hB j)
  let C1 := first θlocal C DC
  let F1 := first θlocal F DF
  let C2 := second θlocal hθlocal2 C DC HC
  let F2 := second θlocal hθlocal2 F DF HF
  let Larr := max (Packet05AssembledArrayCeiling.ceiling Aθ Bθ Cθ C0 C1b C2b)
      (Packet05AssembledArrayCeiling.ceiling Aθ Bθ Cθ F0 F1b F2b)
  obtain ⟨hC1,hC2⟩ := local_arrays Vlocal θlocal hθlocal2 hθlocalV C DC HC hDC hHC
  obtain ⟨hF1,hF2⟩ := local_arrays Vlocal θlocal hθlocal2 hθlocalV F DF HF hDF hHF
  obtain ⟨hLC,hLF,hLC1,hLF1,hLC2,hLF2⟩ := paired_ceiling θlocal hθlocal2 C F DC DF HC HF
    Aθ Bθ Cθ C0 C1b C2b F0 F1b F2b hAθ hBθ hCθ hC0b hC1b hC2b hF0b hF1b hF2b
  exact Packet05UniformChartPhysicalAdapter.uniform_chart_physical_adapter
    up i g hg G Q B hB A d hd T hT ε hε hweight hmetric χ W hW Qeq E Gphys Qphys hG hQphys Ω hmap hE
    Vgrad Wgrad hVgrad hWgrad u hC D0 D1 H00 H01 H10 H11 hD0 hD1 κ ζ hκV hκT hζW hH00 hH01 hH10 hH11
    θ hθW hθT hθ2 α β γ αk βk L P Qb hα hβ hγ hαk hβk hL0 hL1 hP0 hP1 hQ00 hQ01 hQ10 hQ11
    θlocal C1 F1 C2 F2 Vreg Wreg hWreg hWV hθlocal hdiv hC1 hF1 hC2 hF2 hA2 hA3
    η ξ hηV hηW hξW hξ2 hTW hξT aa bb cc rr ss pp qq tt ha hb hc hr hs hp hq ht
    M K W0 Larr hM hK hab hW0 hLC hLF hLC1 hLF1 hLC2 hLF2 haa hbb hcc hrr hss hpp hqq htt

end OQ14.Packet05RegionalUniformChart
#print axioms OQ14.Packet05RegionalUniformChart.regional_uniform_chart
