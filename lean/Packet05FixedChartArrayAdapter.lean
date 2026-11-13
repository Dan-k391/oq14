import Packet05FixedChartScalarAdapter
import Packet05TangentialPlateauBound
import Packet05QuantitativePhysicalBranches
import Packet05NormalFluxPlateauBound
import Packet05QuantitativeChartBranches
import Packet05QuantitativePhysicalChart
import Packet05QuantitativeGraphReconstruction
import Packet05ChartElectricIdentity

/-! Continuous graph-phase branches agree with the actual physical electric
field under the signed chart, not merely with an abstract scalar expression. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05FixedChartArrayAdapter
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation OQ14.DivCurlCompact
  OQ14.Packet05ChartBasis OQ14.Packet05ChartWeakDivergence OQ14.Packet05ChartElectricIdentity
  OQ14.Packet05ChartCorrectionContinuous OQ14.Packet05GraphPhaseReconstruction
  OQ14.Packet05GraphPullback OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeakDivergence OQ14.Packet05ScalarDielectricFlux OQ14.Packet05FlatWeight
  OQ14.Packet05GraphChartMap OQ14.Packet05PhysicalGraphChart
  OQ14.Packet05NormalFluxOriginalBound OQ14.Packet05MatrixWeakDerivative OQ14.MaxwellCutoffCommutator
  OQ14.Packet05RegionalDivergence
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem fixed_chart_array_adapter (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
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
    (κ : RealTest Set.univ) (θ : Test) (hκT : ∀ x ∈ T, κ.function x = 1)
    (hθT : ∀ x ∈ T, θ.function x = 1) (hθ2 : ContDiff ℝ 2 θ.function)
    (D0 D1 : Fin 3 → L2Scalar) (H0 H1 : Fin 3 → Fin 3 → L2Scalar)
    (hD0 : ∀ j, HasWeakPartial (Packet05ScalarCutoffTransfer.cutScalar κ (pulledGradient g hg G B hB 0)) (D0 j) j)
    (hD1 : ∀ j, HasWeakPartial (Packet05ScalarCutoffTransfer.cutScalar κ (pulledGradient g hg G B hB 1)) (D1 j) j)
    (hH0 : ∀ j, j ≠ 2 → ∀ k, HasWeakPartial (scaleL2 θ.function θ.regular.continuous θ.compact (D0 j)) (H0 j k) k)
    (hH1 : ∀ j, j ≠ 2 → ∀ k, HasWeakPartial (scaleL2 θ.function θ.regular.continuous θ.compact (D1 j)) (H1 j k) k)
    (α β γ : ℝ) (hα : ∀ x, ‖θ.function x‖ ≤ α) (hβ : ∀ j x, ‖dcoord θ.function x j‖ ≤ β)
    (hγ : ∀ j k x, ‖dcoord (derivativeCutoff θ hθ2 j).function x k‖ ≤ γ)
    (C1 F1 : Fin 3 → L2Vector) (C2 F2 : Fin 3 → Fin 3 → L2Vector)
    (Vreg Wreg : Set Maxwell.Space) (hWreg : IsOpen Wreg) (hWV : Wreg ⊆ Vreg)
    (hdiv : HasDivergenceOn Vreg (fun j => flux A (pulledGradient g hg G B hB) d hd j -
      (-mulWeight d hd (transformedFlux g hg Q B hB j))) 0)
    (hC1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (pulledGradient g hg G B hB j) (C1 i j) i)
    (hF1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (-mulWeight d hd (transformedFlux g hg Q B hB j)) (F1 i j) i)
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
    (M K X : ℝ) (hM : 0 ≤ M) (hK : ‖ε⁻¹‖ ≤ K)
    (hab : ∀ x ∈ T, |Packet05GraphSlope.slope g 0 x| ≤ M ∧ |Packet05GraphSlope.slope g 1 x| ≤ M)
    (hdata : ∀ x ∈ T, ‖chartCorrection up i g χ W 0 x‖ ≤ X ∧
      ‖chartCorrection up i g χ W 1 x‖ ≤ X ∧ ‖chartCorrection up i g χ W 2 x‖ ≤ X)
    (ht0bound : Packet05ExplicitAnisotropicBound.universalConstant *
      ((α+3*β+6*γ)*‖Packet05ScalarCutoffTransfer.cutScalar κ (pulledGradient g hg G B hB 0)‖ +
        (α+2*β)*(∑ j : Fin 3, ‖D0 j‖) + ∑ j : Fin 2, ∑ k : Fin 3, ‖H0 j.castSucc k‖) ≤ X)
    (ht1bound : Packet05ExplicitAnisotropicBound.universalConstant *
      ((α+3*β+6*γ)*‖Packet05ScalarCutoffTransfer.cutScalar κ (pulledGradient g hg G B hB 1)‖ +
        (α+2*β)*(∑ j : Fin 3, ‖D1 j‖) + ∑ j : Fin 2, ∑ k : Fin 3, ‖H1 j.castSucc k‖) ≤ X)
    (hfluxbound : Packet05ExplicitAnisotropicBound.universalConstant *
      ((pp+3*qq+6*tt)*rr*((1+d)*aa*Packet05NormalFluxDataBounds.size (pulledGradient g hg G B hB)+
        ‖(-mulWeight d hd (transformedFlux g hg Q B hB 2) : L2Scalar)‖) +
       (pp+2*qq)*3*firstBound (pulledGradient g hg G B hB)
         (fun j => -mulWeight d hd (transformedFlux g hg Q B hB j)) C1 F1 d aa bb rr ss +
       ∑ k : Fin 2, ∑ _j : Fin 3, secondBound (pulledGradient g hg G B hB) C1 F1 C2 F2 d aa bb cc pp qq k.castSucc) ≤ X) :
    ∃ reps : Fin 3 → Maxwell.Space → ℂ, (∀ j, Continuous (reps j)) ∧
      (∀ j, (fun x => E x j) =ᵐ[volume.restrict (Packet05PhysicalChartBranches.physicalFlatMap up i g ⁻¹' T)] reps j) ∧
      ∀ j x, x ∈ Packet05PhysicalChartBranches.physicalFlatMap up i g ⁻¹' T →
        ‖reps j x‖ ≤ (2+(1+M)*(K+4*M+1))*X := by
  obtain ⟨f0,hf0,h0,hf0bound⟩ := Packet05TangentialPlateauBound.tangential_plateau_original_bound
    T hT κ θ hκT hθT (pulledGradient g hg G B hB 0) D0 hD0 hθ2 H0 hH0 α β γ hα hβ hγ
  obtain ⟨f1,hf1,h1,hf1bound⟩ := Packet05TangentialPlateauBound.tangential_plateau_original_bound
    T hT κ θ hκT hθT (pulledGradient g hg G B hB 1) D1 hD1 hθ2 H1 hH1 α β γ hα hβ hγ
  apply Packet05FixedChartScalarAdapter.fixed_chart_scalar_adapter
    up i g hg G Q B hB A d hd T hT ε hε hweight hmetric χ W hW Qeq E Gphys Qphys hG hQphys Ω hmap hE
    f0 f1 hf0 hf1 h0 h1 C1 F1 C2 F2 Vreg Wreg hWreg hWV hdiv hC1 hF1 hC2 hF2 hA2 hA3
    η ξ hηV hηW hξW hξ2 hTW hξT aa bb cc rr ss pp qq tt ha hb hc hr hs hp hq ht M K X hM hK hab
  · intro x hx
    obtain ⟨h2,h3,h4⟩ := hdata x hx
    exact ⟨(hf0bound x).trans ht0bound,(hf1bound x).trans ht1bound,h2,h3,h4⟩
  · exact hfluxbound

end OQ14.Packet05FixedChartArrayAdapter
#print axioms OQ14.Packet05FixedChartArrayAdapter.fixed_chart_array_adapter
