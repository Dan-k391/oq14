import Packet05ActualNormalFluxContinuous
import Packet05ActualScalarTangentialContinuity
import Packet05ScalarCutoffRepresentative
import Packet05LocalNormalFluxContinuity


/-! Continuity of an actual tangential scalar-gradient component, derived by
both tangential iterations of the variable-metric transmission equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
namespace OQ14.Packet05ActualTransmissionContinuous
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.DivCurlCompact OQ14.Packet05RegionalPartial
  OQ14.Packet05LocalPartialProduct OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05RegionalScalarLocalization
  OQ14.Packet05ActualLocalSecondDerivatives OQ14.Packet05ScalarActualSecondTangential OQ14.Packet05LocalSecondTangential
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05LocalDerivative
  OQ14.Packet05ActualAllTangential OQ14.Packet05LocalNormalFluxContinuity
  OQ14.Packet05RegionalDivergence OQ14.Packet05ActualNormalFluxContinuous
  OQ14.Packet05ActualScalarTangentialContinuity OQ14.Packet05ScalarCutoffRepresentative
open scoped Topology
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem actual_transmission_continuous
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (u D : L2Scalar) (C F F0 F1 F00 F01 F10 F11 : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j-F j) D)
    (hu : CompactRepresentative u) (hF : ∀ j, CompactRepresentative (F j))
    (hF0 : ∀ j, HasWeakPartial (F j) (F0 j) 0)
    (hF1 : ∀ j, HasWeakPartial (F j) (F1 j) 1)
    (hF00 : ∀ j, HasWeakPartial (F0 j) (F00 j) 0)
    (hF01 : ∀ j, HasWeakPartial (F0 j) (F01 j) 1)
    (hF10 : ∀ j, HasWeakPartial (F1 j) (F10 j) 0)
    (hF11 : ∀ j, HasWeakPartial (F1 j) (F11 j) 1)
    (S₀ V S W : Set Space) (hV : IsOpen V) (hW : IsOpen W) (hWV : W ⊆ V) (hVS₀ : V ⊆ S₀)
    (hD : ∀ᵐ x ∂volume, x ∈ S₀ → D x = 0)
    (τ : RealTest Set.univ) (hτ2 : ContDiff ℝ 2 τ.function) (hτ : ∀ x ∈ V, τ.function x = 1)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hτS0 : ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis 0 ∈ S₀)
    (hτS1 : ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis 1 ∈ S₀)
    (κ : RealTest Set.univ) (hκ2 : ContDiff ℝ 2 κ.function) (hκV : tsupport κ.function ⊆ V)
    (hκS : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ)))
    (ζ : RealTest Set.univ) (δ : ℝ) (hδ : 0 < δ)
    (hζS0 : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis 0 ∈ S)
    (hζS1 : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis 1 ∈ S)
    (hκW : ∀ x ∈ W, κ.function x = 1) (hζW : ∀ x ∈ W, ζ.function x = 1)
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
    (hηb : ∀ j x, ‖dcoord ζ.complexTest.function x j‖ ≤ ηb)
    (V' U T : Set Space) (hU : IsOpen U) (hT : IsOpen T)
    (hVW' : V' ⊆ W) (hUV : U ⊆ V') (hTU : T ⊆ U)
    (θ η χ : Test) (hθ2 : ContDiff ℝ 2 θ.function) (hθW : tsupport θ.function ⊆ W)
    (hθV : ∀ x ∈ V', θ.function x = 1)
    (hηV : tsupport η.function ⊆ V') (hηU : ∀ x ∈ U, η.function x = 1)
    (hχU : tsupport χ.function ⊆ U) (hχ2 : ContDiff ℝ 2 χ.function)
    (hχT : ∀ x ∈ T, χ.function x = 1) :
    ∃ f0 f1 fn : Space → ℂ,
      Continuous f0 ∧ Continuous f1 ∧ Continuous fn ∧
      (C 0 : Space → ℂ) =ᵐ[volume.restrict T] f0 ∧
      (C 1 : Space → ℂ) =ᵐ[volume.restrict T] f1 ∧
      (fun x => (flux A C d hd 2-F 2 : L2Scalar) x) =ᵐ[volume.restrict T] fn := by
  obtain ⟨fn,hfn,hfnAE⟩ := actual_normal_flux_continuous
    g hg A hA2 hA3 u D C F F0 F1 F00 F01 F10 F11 d hd hC hdiv hu hF
    hF0 hF1 hF00 hF01 hF10 hF11 S₀ V S W hV hW hWV hVS₀ hD τ hτ2 hτ δ₀ hδ₀ hτS0 hτS1
    κ hκ2 hκV hκS ζ δ hδ hζS0 hζS1 hκW hζW b hb M hM B hB hmetricτ hmetricζ
    a τa τb ηa ηb ha hτa hτb hηa hηb V' U T hU hT hVW' hUV hTU θ η χ hθ2 hθW hθV hηV hηU hχU hχ2 hχT
  have hχW : tsupport χ.function ⊆ W := hχU.trans (hUV.trans hVW')
  obtain ⟨f0,hf0,hf0AE⟩ := actual_tangential_gradient_continuous
    g hg A hA2 hA3 u D C F F0 F0 F1 F00 F01 d hd hC hdiv hu hF
    0 (by decide) hF0 hF0 hF1 hF00 hF01 S₀ V S W hV hW hVS₀ hD τ hτ2 hτ
    δ₀ hδ₀ hτS0 hτS0 hτS1 κ hκ2 hκV hκS ζ δ hδ hζS0 hζS1 hζW χ hχW hχ2
    b hb M hM B hB hmetricτ hmetricζ a τa τb ηa ηb ha hτa hτb hηa hηb
  obtain ⟨f1,hf1,hf1AE⟩ := actual_tangential_gradient_continuous
    g hg A hA2 hA3 u D C F F1 F0 F1 F10 F11 d hd hC hdiv hu hF
    1 (by decide) hF1 hF0 hF1 hF10 hF11 S₀ V S W hV hW hVS₀ hD τ hτ2 hτ
    δ₀ hδ₀ hτS1 hτS0 hτS1 κ hκ2 hκV hκS ζ δ hδ hζS0 hζS1 hζW χ hχW hχ2
    b hb M hM B hB hmetricτ hmetricζ a τa τb ηa ηb ha hτa hτb hηa hηb
  have hκT : ∀ x ∈ T, κ.function x = 1 := fun x hx => hκW x (hVW' (hUV (hTU hx)))
  refine ⟨f0,f1,fn,hf0,hf1,hfn,?_,?_,hfnAE⟩
  · exact uncut_on_plateau T hT κ χ hκT hχT (C 0) f0 hf0AE
  · exact uncut_on_plateau T hT κ χ hκT hχT (C 1) f1 hf1AE

end OQ14.Packet05ActualTransmissionContinuous
#print axioms OQ14.Packet05ActualTransmissionContinuous.actual_transmission_continuous
