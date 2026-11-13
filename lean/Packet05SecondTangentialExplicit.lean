import Packet05RegionalDifferentiatedScalar
import Packet05ExplicitLocalizedForcing
import Packet05DifferentiatedSourceRegularity
import Packet05LocalizedScalarForcingDerivative
import Packet05ScalarDirectionalTangentialH2
import Packet05CutoffDerivativeH1

/-! Second tangential iteration of the variable-coefficient binary scalar
transmission equation, with the outer localization source constructed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 300000
namespace OQ14.Packet05SecondTangentialExplicit
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.DivCurlCompact OQ14.Packet05RegionalPartial
  OQ14.Packet05RegionalDivergence OQ14.Packet05RegionalDifferentiatedScalar
  OQ14.Packet05ScalarDielectricFlux OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarPrincipalLocalization
  OQ14.Packet05RegionalScalarLocalization OQ14.Packet05LocalizedScalarForcingDerivative
  OQ14.Packet05DifferentiatedScalarEquation OQ14.Packet05DifferentiatedSourceRegularity
  OQ14.Packet05ScalarDirectionalTangentialH2 OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05PartialProduct OQ14.Packet05CurlSourceH1 OQ14.Packet05CutoffDerivativeH1
  OQ14.Packet05ScalarCutoffTesting OQ14.Packet05WeakFourier OQ14.Packet05FlatWeight
  OQ14.Packet05TensorCommutator OQ14.Packet05MatrixWeakDerivative OQ14.MaxwellCutoffCommutator
open scoped Topology
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem second_tangential_iteration_explicit
    (V S : Set Space) (hV : IsOpen V) (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (u D : L2Scalar) (C F Fi Ft Fit : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasDivergenceOn V (fun j => flux A C d hd j-F j) D)
    (hD : ∀ᵐ x ∂volume, x ∈ V → D x = 0)
    (i t : Fin 3) (hi : i ≠ 2) (ht : t ≠ 2)
    (hFi : ∀ j, HasWeakPartial (F j) (Fi j) i)
    (hFt : ∀ j, HasWeakPartial (F j) (Ft j) t)
    (hFit : ∀ j, HasWeakPartial (Fi j) (Fit j) t)
    (τ : RealTest Set.univ) (hτ2 : ContDiff ℝ 2 τ.function) (hτ : ∀ x ∈ V, τ.function x = 1)
    (hCi : ∀ j, ∃ v, HasWeakPartial (cutScalar τ (C j)) v i)
    (hCt : ∀ j, ∃ v, HasWeakPartial (cutScalar τ (C j)) v t)
    (κ : RealTest Set.univ) (hκ2 : ContDiff ℝ 2 κ.function) (hκV : tsupport κ.function ⊆ V)
    (hκS : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ)))
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (ζ : RealTest Set.univ) (δ : ℝ) (hδ : 0 < δ)
    (hζS : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis t ∈ S)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b)
    (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i)
    (hmetric : ∀ x ∈ tsupport ζ.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (a ηa ηb : ℝ) (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hηa : ∀ x, ‖ζ.complexTest.function x‖ ≤ ηa)
    (hηb : ∀ j x, ‖dcoord ζ.complexTest.function x j‖ ≤ ηb) :
    let C' := cutVector τ C
    let DF : L2Vector := fun j => cutoffProductDerivative τ.complexTest.toTest (F j) (Fi j) i
    let DDF : L2Vector := fun j => cutoffProductDerivative τ.complexTest.toTest (Fi j) (Fit j) t +
      cutoffProductDerivative (derivativeCutoff τ.complexTest.toTest
        (Complex.ofRealCLM.contDiff.comp hτ2) i) (F j) (Ft j) t
    ∃ DC TC : L2Vector, (∀ j, HasWeakPartial (cutScalar τ (C j)) (DC j) i) ∧
      (∀ j, HasWeakPartial (cutScalar τ (C j)) (TC j) t) ∧
      let R := differentiatedSource A hA2 C' DF d hd i
      let DR : L2Vector := fun j => DDF j - mulWeight d hd
        (matrixField (derivativeMatrix A hA2 i) TC j +
          matrixField (derivativeMatrix (derivativeMatrix A hA2 i) (derivativeMatrix_c2 A hA2 hA3 i) t) C' j)
      let J := OQ14.Packet05LocalizedForcingBootstrap.forceDerivative κ hκ2 A hA2 (C i) (DC t) R DR d hd t
      (∀ j, HasWeakPartial (localizedForcing κ A (C i) R d hd j) (J j) t) ∧
      ∀ j, ∃ H : L2Scalar, HasWeakPartial
        (cutScalar ζ (localizedGradient κ (C i) DC j)) H t ∧
        ‖H‖ ≤ Real.sqrt (OQ14.Packet05ScalarDirectionalUniformQuotients.uniformEnergyBound
          (localizedGradient κ (C i) DC) J d b M a ηa ηb) +
          3*ηb*‖localizedGradient κ (C i) DC j‖ := by
  choose DC hDC using hCi
  choose TC hTC using hCt
  let C' := cutVector τ C
  let F' := cutVector τ F
  let DF : L2Vector := fun j => cutoffProductDerivative τ.complexTest.toTest (F j) (Fi j) i
  let DDF : L2Vector := fun j => cutoffProductDerivative τ.complexTest.toTest (Fi j) (Fit j) t +
    cutoffProductDerivative (MaxwellCutoffCommutator.derivativeCutoff τ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hτ2) i) (F j) (Ft j) t
  have hτc : ∀ x ∈ V, τ.complexTest.function x = 1 := by
    intro x hx; simp [RealTest.complexTest,hτ x hx]
  have hCeq (j : Fin 3) : ∀ᵐ x ∂volume, x ∈ V → C' j x = C j x := by
    filter_upwards [cutVector_ae τ C j] with x hx hVx
    rw [hx,hτ x hVx]; simp
  have hFeq (j : Fin 3) : ∀ᵐ x ∂volume, x ∈ V → F' j x = F j x := by
    filter_upwards [cutVector_ae τ F j] with x hx hVx
    rw [hx,hτ x hVx]; simp
  have hC'i (j : Fin 3) : HasWeakPartial (C' j) (DC j) i := hDC j
  have hC't (j : Fin 3) : HasWeakPartial (C' j) (TC j) t := hTC j
  have hF'i (j : Fin 3) : HasWeakPartial (F' j) (DF j) i := cutoff_weak_partial τ.complexTest.toTest (F j) (Fi j) i (hFi j)
  have hDFt (j : Fin 3) : HasWeakPartial (DF j) (DDF j) t :=
    cutoff_product_derivative_partial τ.complexTest.toTest (Complex.ofRealCLM.contDiff.comp hτ2)
      (F j) (Fi j) (Ft j) (Fit j) i t (hFit j) (hFt j)
  let R := differentiatedSource A hA2 C' DF d hd i
  have hregional : HasDivergenceOn V (fun j => flux A DC d hd j-R j) 0 :=
    regional_differentiated_scalar_equation V hV A hA2 C C' DC F F' DF D d hd i hi hdiv hD hCeq hFeq hC'i hF'i
  have hgrad (j : Fin 3) : HasPartialOn V (C i) (DC j) j := by
    have hl : HasPartialOn V (C j) (DC j) i := cutoff_partial_on V τ.complexTest.toTest (C j) (DC j) i hτc (hDC j)
    exact mixed_partial_on_commute V hV u (C j) (C i) (DC j) j i
      (global_partial_on V u (C j) j (hC j)) (global_partial_on V u (C i) i (hC i)) hl
  let DR : L2Vector := fun j => DDF j - mulWeight d hd
    (matrixField (derivativeMatrix A hA2 i) TC j +
      matrixField (derivativeMatrix (derivativeMatrix A hA2 i) (derivativeMatrix_c2 A hA2 hA3 i) t) C' j)
  have hRt (j : Fin 3) : HasWeakPartial (R j) (DR j) t :=
    differentiated_source_tangential_partial A hA2 hA3 C' TC DF DDF d hd i t ht hC't hDFt j
  have hRlocal (j : Fin 3) : HasPartialOn V (R j) (DR j) t := global_partial_on V _ _ t (hRt j)
  obtain ⟨hgradκ,hdivκ,hDκ,hvκ,hFκ⟩ := localize_regional_scalar_equation V S A (C i) DC R d hd hgrad hregional κ hκV hκS
  let J := OQ14.Packet05LocalizedForcingBootstrap.forceDerivative κ hκ2 A hA2 (C i) (DC t) R DR d hd t
  have hJ := OQ14.Packet05ExplicitLocalizedForcing.localized_forcing_tangential_derivative_explicit V A hA2 (C i) (DC t) R DR d hd t ht (hgrad t) hRlocal κ hκ2 hκV
  refine ⟨DC,TC,hDC,hTC,hJ,?_⟩
  intro j
  obtain ⟨H,hH,hbound⟩ := directional_tangential_gradient_derivative g hg ζ A (cutScalar κ (C i))
    (OQ14.Packet05RegionalFluxCutoff.cutFluxSource κ.complexTest.toTest (fun j => flux A DC d hd j-R j))
    (localizedGradient κ (C i) DC) (localizedForcing κ A (C i) R d hd) J d hd hgradκ hdivκ hvκ hFκ
    S δ hδ t j ht hJ hDκ hζS b hb M hM B hB hmetric a ηa ηb ha hηa hηb
  exact ⟨H,hH,hbound⟩

end OQ14.Packet05SecondTangentialExplicit
#print axioms OQ14.Packet05SecondTangentialExplicit.second_tangential_iteration_explicit
