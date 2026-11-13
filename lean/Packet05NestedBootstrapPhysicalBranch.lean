import Packet05BootstrapPhysicalBranches
import Packet05NestedTangentialUniform
import Packet05RegionalNormalFluxUniform

/-! Uniform physical branch from the actual bootstrapped scalar problem:
all three transmission representatives are constructed and transferred
back to the uncut physical field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 7000000
namespace OQ14.Packet05NestedBootstrapPhysicalBranch
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalPartial Packet05RegionalDivergence Packet05ScalarCutoffTransfer Packet05RegionalScalarLocalization
  Packet05ChartBasis Packet05ChartWeakDivergence Packet05ChartElectricIdentity Packet05ChartCorrectionContinuous
  Packet05GraphPullback Packet05GraphH1Pullback Packet05GraphSlopeMultiplier Packet05GraphWeakDivergence
  Packet05ScalarDielectricFlux Packet05FlatWeight Packet05GraphChartMap Packet05PhysicalGraphChart
  MaxwellCutoffCommutator Packet05MatrixWeakDerivative
abbrev Plane := ConicalSmoothJunction.Plane

theorem nested_bootstrap_physical_branch (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (GphysChart Qchart : L2Vector) (Bs : Fin 3 → ℝ) (hBs : ∀ j x, ‖slopeC g j x‖ ≤ Bs j)
    (A : Fin 3 → Fin 3 → Test) (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function) (d : ℝ) (hd : 0 ≤ d)
    (T : Set Space) (hT : IsOpen T) (ε : ℂ) (hε : ε ≠ 0) (hweight : ∀ x ∈ T, weight d x = ε)
    (hmetric : ∀ x ∈ T, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x) (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (χ : ContDiffBump (0 : Space)) (W : Field) (hW : ∀ j, Continuous (fun x => W x j))
    (Qeq : Qchart = chartVector up i (Packet06ScalarGaussLocalization.correction χ W hW))
    (E : Field) (Gphysical Qphysical : L2Vector) (hG : GphysChart = chartVector up i Gphysical)
    (hQphysical : Qphysical = Packet06ScalarGaussLocalization.correction χ W hW)
    (Ω : Set Space) (hmap : ∀ x ∈ T, inverseOriented up i (graphMap (liftedHeight g) x) ∈ Ω)
    (hE : ∀ j, ∀ᵐ y ∂volume, y ∈ Ω → Gphysical j y+Qphysical j y=E y j)
    (κboot : RealTest univ) (hκboot : ∀ x ∈ T, κboot.function x = 1) (u : L2Scalar)
    (hbootGrad : ∀ j, HasWeakPartial (cutScalar κboot u)
      (localizedGradient κboot u (pulledGradient g hg GphysChart Bs hBs) j) j)
    (Vgrad Vlocal Vreg Wreg : Set Space) (hVgrad : IsOpen Vgrad) (hVlocal : IsOpen Vlocal) (hVlocalSub : Vlocal ⊆ Vgrad) (hWreg : IsOpen Wreg) (hWV : Wreg ⊆ Vreg)
    (hdiv : HasDivergenceOn Vreg (fun j => flux A (localizedGradient κboot u (pulledGradient g hg GphysChart Bs hBs)) d hd j-
      localizedForcing κboot A u (fun j => -mulWeight d hd (transformedFlux g hg Qchart Bs hBs j)) d hd j) 0)
    (D0 D1 H00 H01 H10 H11 : L2Vector)
    (hD0 : ∀ j, HasPartialOn Vgrad (localizedGradient κboot u (pulledGradient g hg GphysChart Bs hBs) j) (D0 j) 0)
    (hD1 : ∀ j, HasPartialOn Vgrad (localizedGradient κboot u (pulledGradient g hg GphysChart Bs hBs) j) (D1 j) 1)
    (hH00 : ∀ j, HasPartialOn Vlocal (D0 j) (H00 j) 0) (hH01 : ∀ j, HasPartialOn Vlocal (D0 j) (H01 j) 1)
    (hH10 : ∀ j, HasPartialOn Vlocal (D1 j) (H10 j) 0) (hH11 : ∀ j, HasPartialOn Vlocal (D1 j) (H11 j) 1)
    (κ ζ : RealTest univ) (hκV : tsupport κ.function ⊆ Vgrad) (hκT : ∀ x ∈ T, κ.function x = 1)
    (hζV : ∀ x ∈ Vlocal, ζ.function x = 1)
    (hH00w : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (localizedGradient κboot u (pulledGradient g hg GphysChart Bs hBs) 0) D0 j)) (H00 j) 0)
    (hH01w : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (localizedGradient κboot u (pulledGradient g hg GphysChart Bs hBs) 0) D0 j)) (H01 j) 1)
    (hH10w : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (localizedGradient κboot u (pulledGradient g hg GphysChart Bs hBs) 1) D1 j)) (H10 j) 0)
    (hH11w : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (localizedGradient κboot u (pulledGradient g hg GphysChart Bs hBs) 1) D1 j)) (H11 j) 1)
    (R1 : Fin 3 → L2Vector) (R2 : Fin 3 → Fin 3 → L2Vector)
    (hR1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (localizedForcing κboot A u (fun j => -mulWeight d hd (transformedFlux g hg Qchart Bs hBs j)) d hd j) (R1 i j) i)
    (hR2 : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (R1 i j) (R2 i t j) t)
    (K P Q : ℝ) (hK : 0 ≤ K) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hGn : ∀ j, ‖localizedGradient κboot u (pulledGradient g hg GphysChart Bs hBs) j‖ ≤ K)
    (hRn : ∀ j, ‖localizedForcing κboot A u (fun j => -mulWeight d hd (transformedFlux g hg Qchart Bs hBs j)) d hd j‖ ≤ K)
    (hD0n : ∀ j, ‖D0 j‖ ≤ P) (hD1n : ∀ j, ‖D1 j‖ ≤ P)
    (hH00n : ∀ j, ‖H00 j‖ ≤ Q) (hH01n : ∀ j, ‖H01 j‖ ≤ Q)
    (hH10n : ∀ j, ‖H10 j‖ ≤ Q) (hH11n : ∀ j, ‖H11 j‖ ≤ Q)
    (hR1n : ∀ i, i ≠ 2 → ∀ j, ‖R1 i j‖ ≤ K)
    (hR2n : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, ‖R2 i t j‖ ≤ K)
    (θ : Test) (hθV : tsupport θ.function ⊆ Vlocal) (hθT : ∀ x ∈ T, θ.function x = 1)
    (hθ2 : ContDiff ℝ 2 θ.function) (α β γ αk βk : ℝ)
    (hα : ∀ x, ‖θ.function x‖ ≤ α) (hβ : ∀ j x, ‖dcoord θ.function x j‖ ≤ β)
    (hγ : ∀ j k x, ‖dcoord (derivativeCutoff θ hθ2 j).function x k‖ ≤ γ)
    (hαk : ∀ x, ‖κ.complexTest.function x‖ ≤ αk) (hβk : ∀ j x, ‖dcoord κ.complexTest.function x j‖ ≤ βk)
    (θlocal : Test) (hθlocal2 : ContDiff ℝ 2 θlocal.function) (hθlocalV : tsupport θlocal.function ⊆ Vlocal)
    (hθlocalR : ∀ x ∈ Vreg, θlocal.function x = 1) (aθ bθ cθ : ℝ)
    (haθ : ∀ x, ‖θlocal.function x‖ ≤ aθ) (hbθ : ∀ j x, ‖dcoord θlocal.function x j‖ ≤ bθ)
    (hcθ : ∀ j k x, ‖dcoord (derivativeCutoff θlocal hθlocal2 j).function x k‖ ≤ cθ)
    (lam ξ : Test) (hlamR : tsupport lam.function ⊆ Vreg) (hlamW : ∀ x ∈ Wreg, lam.function x = 1)
    (hξW : tsupport ξ.function ⊆ Wreg) (hξ2 : ContDiff ℝ 2 ξ.function) (hξT : ∀ x ∈ T, ξ.function x = 1)
    (hTW : T ⊆ Wreg) (a b c r s p q t : ℝ)
    (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a) (hb : ∀ j k l x, ‖dcoord (A j k).function x l‖ ≤ b)
    (hc : ∀ j k l m x, ‖dcoord (derivativeMatrix A hA2 l j k).function x m‖ ≤ c)
    (hr : ∀ x, ‖lam.function x‖ ≤ r) (hs : ∀ j x, ‖dcoord lam.function x j‖ ≤ s)
    (hp : ∀ x, ‖ξ.function x‖ ≤ p) (hq : ∀ j x, ‖dcoord ξ.function x j‖ ≤ q)
    (ht : ∀ j k x, ‖dcoord (derivativeCutoff ξ hξ2 j).function x k‖ ≤ t)
    (M Einv W0 : ℝ) (hM : 0 ≤ M) (hEinv : ‖ε⁻¹‖ ≤ Einv)
    (hab : ∀ x ∈ T, |Packet05GraphSlope.slope g 0 x| ≤ M ∧ |Packet05GraphSlope.slope g 1 x| ≤ M)
    (hW0 : ∀ x ∈ T, ∀ j, ‖chartCorrection up i g χ W j x‖ ≤ W0) :
    let Larr := max (Packet05AssembledArrayCeiling.ceiling aθ bθ cθ K P Q)
      (Packet05AssembledArrayCeiling.ceiling aθ bθ cθ K K K)
    let Tang := Packet05ExplicitAnisotropicBound.universalConstant *
      ((α+3*β+6*γ)*αk*K+(α+2*β)*3*(αk*P+βk*K)+6*(α*Q+β*(αk*P+βk*K)))
    let X := max W0 (max Tang (Packet05NormalFluxUniformCeiling.coefficient d a b c r s p q t * Larr))
    ∃ reps : Fin 3 → Space → ℂ, (∀ j, Continuous (reps j)) ∧
      (∀ j, (fun x => E x j) =ᵐ[volume.restrict (Packet05PhysicalChartBranches.physicalFlatMap up i g ⁻¹' T)] reps j) ∧
      ∀ j x, x ∈ Packet05PhysicalChartBranches.physicalFlatMap up i g ⁻¹' T →
        ‖reps j x‖ ≤ (2+(1+M)*(Einv+4*M+1))*X := by
  dsimp only
  let C := pulledGradient g hg GphysChart Bs hBs
  let F : L2Vector := fun j => -mulWeight d hd (transformedFlux g hg Qchart Bs hBs j)
  let Cb := localizedGradient κboot u C
  let Fb := localizedForcing κboot A u F d hd
  obtain ⟨f0,hf0,h0,h0n⟩ := Packet05NestedTangentialUniform.nested_tangential_uniform
    Vgrad Vlocal T hVgrad hVlocal hT (cutScalar κboot u) Cb hbootGrad 0 D0 H00 H01 hD0
    κ ζ hκV hκT hζV hH00w hH01w θ hθV hθT hθ2 α β γ αk βk K P Q
    hα hβ hγ hαk hβk (hGn 0) hD0n hH00n hH01n
  obtain ⟨f1,hf1,h1,h1n⟩ := Packet05NestedTangentialUniform.nested_tangential_uniform
    Vgrad Vlocal T hVgrad hVlocal hT (cutScalar κboot u) Cb hbootGrad 1 D1 H10 H11 hD1
    κ ζ hκV hκT hζV hH10w hH11w θ hθV hθT hθ2 α β γ αk βk K P Q
    hα hβ hγ hαk hβk (hGn 1) hD1n hH10n hH11n
  obtain ⟨fn,hfn,hn,hnn⟩ := Packet05RegionalNormalFluxUniform.regional_normal_flux_uniform
    Vlocal Vreg Wreg T hWreg hWV hT hTW A hA2 hA3 Cb Fb d hd hdiv D0 D1 H00 H01 H10 H11
    (fun j φ hφ => hD0 j φ (hφ.trans hVlocalSub))
    (fun j φ hφ => hD1 j φ (hφ.trans hVlocalSub)) hH00 hH01 hH10 hH11 R1 R2 hR1 hR2 K P Q hK hP hQ hGn hRn hD0n hD1n
    hH00n hH01n hH10n hH11n hR1n hR2n θlocal hθlocal2 hθlocalV hθlocalR aθ bθ cθ
    haθ hbθ hcθ lam ξ hlamR hlamW hξW hξ2 hξT a b c r s p q t ha hb hc hr hs hp hq ht
  let Larr := max (Packet05AssembledArrayCeiling.ceiling aθ bθ cθ K P Q)
    (Packet05AssembledArrayCeiling.ceiling aθ bθ cθ K K K)
  let Tang := Packet05ExplicitAnisotropicBound.universalConstant *
    ((α+3*β+6*γ)*αk*K+(α+2*β)*3*(αk*P+βk*K)+6*(α*Q+β*(αk*P+βk*K)))
  let X := max W0 (max Tang (Packet05NormalFluxUniformCeiling.coefficient d a b c r s p q t * Larr))
  have hW0X : W0 ≤ X := le_max_left _ _
  have hTangX : Tang ≤ X := (le_max_left _ _).trans (le_max_right _ _)
  have hNormX : Packet05NormalFluxUniformCeiling.coefficient d a b c r s p q t * Larr ≤ X :=
    (le_max_right _ _).trans (le_max_right _ _)
  apply Packet05BootstrapPhysicalBranches.bootstrap_physical_branches up i g hg GphysChart Qchart Bs hBs A d hd
    T hT ε hε hweight hmetric χ W hW Qeq E Gphysical Qphysical hG hQphysical Ω hmap hE
    κboot hκboot u f0 f1 fn hf0 hf1 hfn h0 h1 hn M Einv X hM hEinv hab
  intro x hx
  exact ⟨(h0n x).trans hTangX,(h1n x).trans hTangX,(hnn x).trans hNormX,
    (hW0 x hx 0).trans hW0X,(hW0 x hx 1).trans hW0X,(hW0 x hx 2).trans hW0X⟩

end OQ14.Packet05NestedBootstrapPhysicalBranch
#print axioms OQ14.Packet05NestedBootstrapPhysicalBranch.nested_bootstrap_physical_branch
