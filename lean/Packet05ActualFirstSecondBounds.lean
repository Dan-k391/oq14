import Packet05ScalarSecondTangential
import Packet05SecondTangentialExplicit
import Packet05FirstTangentialArrayBound
import Packet05LocalDerivative

/-! Direct two-tangential derivative construction from the original scalar
transmission equation, using two nested localization stages. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 300000
namespace OQ14.Packet05ActualFirstSecondBounds
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05RegionalDivergence OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05RegionalScalarLocalization
  OQ14.Packet05ScalarDirectionalTangentialH2 OQ14.Packet05ScalarSecondTangential
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05ScalarPrincipalLocalization
open scoped Topology
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem actual_first_second_explicit_bounds
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (u D : L2Scalar) (C F Fi Ft Fit : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j-F j) D)
    (hu : CompactRepresentative u) (hF : ∀ j, CompactRepresentative (F j))
    (i t : Fin 3) (hi : i ≠ 2) (ht : t ≠ 2)
    (hFi : ∀ j, HasWeakPartial (F j) (Fi j) i)
    (hFt : ∀ j, HasWeakPartial (F j) (Ft j) t)
    (hFit : ∀ j, HasWeakPartial (Fi j) (Fit j) t)
    (S₀ V S : Set Space) (hV : IsOpen V) (hVS₀ : V ⊆ S₀)
    (hD : ∀ᵐ x ∂volume, x ∈ S₀ → D x = 0)
    (τ : RealTest Set.univ) (hτ2 : ContDiff ℝ 2 τ.function) (hτ : ∀ x ∈ V, τ.function x = 1)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hτSi : ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis i ∈ S₀)
    (hτSt : ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis t ∈ S₀)
    (κ : RealTest Set.univ) (hκ2 : ContDiff ℝ 2 κ.function) (hκV : tsupport κ.function ⊆ V)
    (hκS : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ)))
    (ζ : RealTest Set.univ) (δ : ℝ) (hδ : 0 < δ)
    (hζS : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis t ∈ S)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b)
    (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B : Fin 2 → ℝ) (hB : ∀ l x, ‖slopeC g l.castSucc x‖ ≤ B l)
    (hmetricτ : ∀ x ∈ tsupport τ.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (hmetricζ : ∀ x ∈ tsupport ζ.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (a τa τb ηa ηb : ℝ) (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hτa : ∀ x, ‖τ.complexTest.function x‖ ≤ τa)
    (hτb : ∀ j x, ‖dcoord τ.complexTest.function x j‖ ≤ τb)
    (hηa : ∀ x, ‖ζ.complexTest.function x‖ ≤ ηa)
    (hηb : ∀ j x, ‖dcoord ζ.complexTest.function x j‖ ≤ ηb) :
    let C' := cutVector τ C
    let DF : L2Vector := fun j => OQ14.Packet05CurlSourceH1.cutoffProductDerivative τ.complexTest.toTest (F j) (Fi j) i
    let DDF : L2Vector := fun j => OQ14.Packet05CurlSourceH1.cutoffProductDerivative τ.complexTest.toTest (Fi j) (Fit j) t +
      OQ14.Packet05CurlSourceH1.cutoffProductDerivative (OQ14.MaxwellCutoffCommutator.derivativeCutoff τ.complexTest.toTest
        (Complex.ofRealCLM.contDiff.comp hτ2) i) (F j) (Ft j) t
    ∃ DC TC : L2Vector,
      (∀ j, HasWeakPartial (cutScalar τ (C j)) (DC j) i) ∧
      (∀ j, HasWeakPartial (cutScalar τ (C j)) (TC j) t) ∧
      (∑ j : Fin 3, ‖DC j‖) ≤ 3 * Real.sqrt (OQ14.Packet05ScalarDirectionalUniformQuotients.uniformEnergyBound C Fi d b M a τa τb) +
        3*τb*(‖C 0‖+‖C 1‖+‖C 2‖) ∧
      (∑ j : Fin 3, ‖TC j‖) ≤ 3 * Real.sqrt (OQ14.Packet05ScalarDirectionalUniformQuotients.uniformEnergyBound C Ft d b M a τa τb) +
        3*τb*(‖C 0‖+‖C 1‖+‖C 2‖) ∧
      let R := OQ14.Packet05DifferentiatedScalarEquation.differentiatedSource A hA2 C' DF d hd i
      let DR : L2Vector := fun j => DDF j - OQ14.Packet05FlatWeight.mulWeight d hd
        (OQ14.Packet05TensorCommutator.matrixField (OQ14.Packet05MatrixWeakDerivative.derivativeMatrix A hA2 i) TC j +
          OQ14.Packet05TensorCommutator.matrixField (OQ14.Packet05MatrixWeakDerivative.derivativeMatrix
            (OQ14.Packet05MatrixWeakDerivative.derivativeMatrix A hA2 i)
            (OQ14.Packet05DifferentiatedSourceRegularity.derivativeMatrix_c2 A hA2 hA3 i) t) C' j)
      let J := OQ14.Packet05LocalizedForcingBootstrap.forceDerivative κ hκ2 A hA2 (C i) (DC t) R DR d hd t
      (∀ j, HasWeakPartial (localizedForcing κ A (C i) R d hd j) (J j) t) ∧
      ∀ j, ∃ H : L2Scalar, HasWeakPartial
        (cutScalar ζ (localizedGradient κ (C i) DC j)) H t ∧
        ‖H‖ ≤ Real.sqrt (OQ14.Packet05ScalarDirectionalUniformQuotients.uniformEnergyBound
          (localizedGradient κ (C i) DC) J d b M a ηa ηb) +
          3*ηb*‖localizedGradient κ (C i) DC j‖ := by
  obtain ⟨Di,hDi,hDiNorm⟩ := OQ14.Packet05FirstTangentialArrayBound.first_tangential_array_bound
    g hg τ A u D C F Fi d hd hC hdiv hu hF S₀ δ₀ hδ₀ i hi hFi hD hτSi
    b hb M hM B hB hmetricτ a τa τb ha hτa hτb
  obtain ⟨Dt,hDt,hDtNorm⟩ := OQ14.Packet05FirstTangentialArrayBound.first_tangential_array_bound
    g hg τ A u D C F Ft d hd hC hdiv hu hF S₀ δ₀ hδ₀ t ht hFt hD hτSt
    b hb M hM B hB hmetricτ a τa τb ha hτa hτb
  have hCi (j : Fin 3) : ∃ v, HasWeakPartial (cutScalar τ (C j)) v i := ⟨Di j,hDi j⟩
  have hCt (j : Fin 3) : ∃ v, HasWeakPartial (cutScalar τ (C j)) v t := ⟨Dt j,hDt j⟩
  have hDV : ∀ᵐ x ∂volume, x ∈ V → D x = 0 := by
    filter_upwards [hD] with x hx hVx
    exact hx (hVS₀ hVx)
  obtain ⟨DC,TC,hDC,hTC,hJ,hH⟩ := OQ14.Packet05SecondTangentialExplicit.second_tangential_iteration_explicit
    V S hV A hA2 hA3 u D C F Fi Ft Fit d hd hC
    (global_divergence_on V _ D hdiv) hDV i t hi ht hFi hFt hFit τ hτ2 hτ hCi hCt
    κ hκ2 hκV hκS g hg ζ δ hδ hζS b hb M hM B hB hmetricζ a ηa ηb ha hηa hηb
  have heq : DC=Di := by
    funext j
    exact OQ14.Packet05LocalDerivative.weak_partial_unique (cutScalar τ (C j)) (DC j) (Di j) i (hDC j) (hDi j)
  have heq' : TC=Dt := by
    funext j
    exact OQ14.Packet05LocalDerivative.weak_partial_unique (cutScalar τ (C j)) (TC j) (Dt j) t (hTC j) (hDt j)
  refine ⟨DC,TC,hDC,hTC,?_,?_,hJ,hH⟩
  · simpa [heq] using hDiNorm
  · simpa [heq'] using hDtNorm

end OQ14.Packet05ActualFirstSecondBounds
#print axioms OQ14.Packet05ActualFirstSecondBounds.actual_first_second_explicit_bounds
