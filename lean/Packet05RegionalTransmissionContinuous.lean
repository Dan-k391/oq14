import Packet05RegionalBootstrappedScalar
import Packet05ActualTransmissionContinuous
import Packet05BootstrapRepresentativeTransfer

/-! Actual regional scalar transmission has all three continuous
transmission representatives, after the explicit annulus bootstrap. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
namespace OQ14.Packet05RegionalTransmissionContinuous
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05RegionalDivergence
  OQ14.Packet05RegionalBootstrappedScalar OQ14.Packet05ActualTransmissionContinuous
  OQ14.Packet05BootstrapRepresentativeTransfer OQ14.Packet05RegionalScalarLocalization
  OQ14.Packet05RegionalFluxCutoff OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05GraphSlopeMultiplier
open scoped Topology
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem regional_transmission_continuous
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (u : L2Scalar) (C F : L2Vector) (F1 : Fin 3 → L2Vector) (F2 : Fin 3 → Fin 3 → L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (hC : ∀ j, HasWeakPartial u (C j) j) (hu : CompactRepresentative u)
    (hF : ∀ j, CompactRepresentative (F j))
    (hF1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F j) (F1 i j) i)
    (hF2 : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t)
    (Ω S₀ V S : Set Space) (hdiv : HasDivergenceOn Ω (fun j => flux A C d hd j-F j) 0)
    (θ : Test) (hθΩ : tsupport θ.function ⊆ Ω)
    (hθS : ∀ x ∈ S₀, θ.function =ᶠ[nhds x] (fun _ => (1 : ℂ)))
    (τ : RealTest Set.univ) (hτV : ∀ x ∈ V, τ.function x = 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hτS : ∀ t, t ≠ 2 → ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport τ.function,
      x ∈ S₀ ∧ x+h • basis t ∈ S₀)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b)
    (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B : Fin 2 → ℝ) (hB : ∀ l x, ‖slopeC g l.castSucc x‖ ≤ B l)
    (hmetric : ∀ x ∈ tsupport τ.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (a τa τb : ℝ) (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hτa : ∀ x, ‖τ.complexTest.function x‖ ≤ τa)
    (hτb : ∀ j x, ‖dcoord τ.complexTest.function x j‖ ≤ τb)
    (κ : RealTest Set.univ) (hκ2 : ContDiff ℝ 2 κ.function) (hκ3 : ContDiff ℝ 3 κ.function)
    (hκΩ : tsupport κ.function ⊆ Ω) (hκV : tsupport κ.function ⊆ V)
    (hκS : ∀ x ∈ S, κ.function =ᶠ[nhds x] (fun _ => (1 : ℝ)))
    (V₁ S₁ W₁ V₂ U₂ T : Set Space) (hV₁ : IsOpen V₁) (hW₁ : IsOpen W₁)
    (hW₁V₁ : W₁ ⊆ V₁) (hV₁S : V₁ ⊆ S) (hU₂ : IsOpen U₂) (hT : IsOpen T)
    (hV₂W₁ : V₂ ⊆ W₁) (hU₂V₂ : U₂ ⊆ V₂) (hTU₂ : T ⊆ U₂) (hTS : T ⊆ S)
    (τ₁ : RealTest Set.univ) (hτ₁2 : ContDiff ℝ 2 τ₁.function) (hτ₁V : ∀ x ∈ V₁, τ₁.function x = 1)
    (δ₁ : ℝ) (hδ₁ : 0 < δ₁)
    (hτ₁S0 : ∀ h : ℝ, |h| < δ₁ → ∀ x ∈ tsupport τ₁.function, x ∈ S ∧ x+h • basis 0 ∈ S)
    (hτ₁S1 : ∀ h : ℝ, |h| < δ₁ → ∀ x ∈ tsupport τ₁.function, x ∈ S ∧ x+h • basis 1 ∈ S)
    (κ₁ : RealTest Set.univ) (hκ₁2 : ContDiff ℝ 2 κ₁.function) (hκ₁V : tsupport κ₁.function ⊆ V₁)
    (hκ₁S : ∀ x ∈ S₁, κ₁.function =ᶠ[nhds x] (fun _ => (1 : ℝ)))
    (ζ₁ : RealTest Set.univ) (δ₂ : ℝ) (hδ₂ : 0 < δ₂)
    (hζ₁S0 : ∀ h : ℝ, |h| < δ₂ → ∀ x ∈ tsupport ζ₁.function, x ∈ S₁ ∧ x+h • basis 0 ∈ S₁)
    (hζ₁S1 : ∀ h : ℝ, |h| < δ₂ → ∀ x ∈ tsupport ζ₁.function, x ∈ S₁ ∧ x+h • basis 1 ∈ S₁)
    (hκ₁W : ∀ x ∈ W₁, κ₁.function x = 1) (hζ₁W : ∀ x ∈ W₁, ζ₁.function x = 1)
    (hmetricτ₁ : ∀ x ∈ tsupport τ₁.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (hmetricζ₁ : ∀ x ∈ tsupport ζ₁.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (τa₁ τb₁ ηa₁ ηb₁ : ℝ) (hτa₁ : ∀ x, ‖τ₁.complexTest.function x‖ ≤ τa₁)
    (hτb₁ : ∀ j x, ‖dcoord τ₁.complexTest.function x j‖ ≤ τb₁)
    (hηa₁ : ∀ x, ‖ζ₁.complexTest.function x‖ ≤ ηa₁)
    (hηb₁ : ∀ j x, ‖dcoord ζ₁.complexTest.function x j‖ ≤ ηb₁)
    (θ₁ η₁ χ₁ : Test) (hθ₁2 : ContDiff ℝ 2 θ₁.function) (hθ₁W : tsupport θ₁.function ⊆ W₁)
    (hθ₁V : ∀ x ∈ V₂, θ₁.function x = 1)
    (hη₁V : tsupport η₁.function ⊆ V₂) (hη₁U : ∀ x ∈ U₂, η₁.function x = 1)
    (hχ₁U : tsupport χ₁.function ⊆ U₂) (hχ₁2 : ContDiff ℝ 2 χ₁.function)
    (hχ₁T : ∀ x ∈ T, χ₁.function x = 1) :
    ∃ f0 f1 fn : Space → ℂ,
      Continuous f0 ∧ Continuous f1 ∧ Continuous fn ∧
      (C 0 : Space → ℂ) =ᵐ[volume.restrict T] f0 ∧
      (C 1 : Space → ℂ) =ᵐ[volume.restrict T] f1 ∧
      (fun x => (flux A C d hd 2-F 2 : L2Scalar) x) =ᵐ[volume.restrict T] fn := by
  have hbdata := regional_bootstrapped_scalar g hg A hA2 hA3 u C F F1 F2 d hd hC hu hF hF1 hF2
    Ω S₀ V S hdiv θ hθΩ hθS τ hτV δ hδ hτS b hb M hM B hB hmetric a τa τb ha hτa hτb
    κ hκ2 hκ3 hκΩ hκV hκS
  dsimp only at hbdata
  obtain ⟨hG,hdiv',hD,huc,hFc,R1,R2,hR1,hR2⟩ := hbdata
  let U' := cutScalar κ u
  let G' := localizedGradient κ u C
  let R' := localizedForcing κ A u F d hd
  let D' := cutFluxSource κ.complexTest.toTest (fun j => flux A C d hd j-F j)
  obtain ⟨f0,f1,fn,hf0,hf1,hfn,h0,h1,hn⟩ := actual_transmission_continuous g hg A hA2 hA3
    U' D' G' R' (R1 0) (R1 1) (R2 0 0) (R2 0 1) (R2 1 0) (R2 1 1) d hd
    hG hdiv' huc hFc (hR1 0 (by decide)) (hR1 1 (by decide))
    (hR2 0 (by decide) 0 (by decide)) (hR2 0 (by decide) 1 (by decide))
    (hR2 1 (by decide) 0 (by decide)) (hR2 1 (by decide) 1 (by decide))
    S V₁ S₁ W₁ hV₁ hW₁ hW₁V₁ hV₁S hD τ₁ hτ₁2 hτ₁V δ₁ hδ₁ hτ₁S0 hτ₁S1
    κ₁ hκ₁2 hκ₁V hκ₁S ζ₁ δ₂ hδ₂ hζ₁S0 hζ₁S1 hκ₁W hζ₁W
    b hb M hM B hB hmetricτ₁ hmetricζ₁ a τa₁ τb₁ ηa₁ ηb₁ ha hτa₁ hτb₁ hηa₁ hηb₁
    V₂ U₂ T hU₂ hT hV₂W₁ hU₂V₂ hTU₂ θ₁ η₁ χ₁ hθ₁2 hθ₁W hθ₁V hη₁V hη₁U hχ₁U hχ₁2 hχ₁T
  have hκT : ∀ x ∈ T, κ.function x = 1 := fun x hx => (hκS x (hTS hx)).self_of_nhds
  have he := bootstrap_representatives_on_plateau T hT κ hκT A u C F d hd f0 f1 fn h0 h1 hn
  exact ⟨f0,f1,fn,hf0,hf1,hfn,he.1,he.2.1,he.2.2⟩

end OQ14.Packet05RegionalTransmissionContinuous
#print axioms OQ14.Packet05RegionalTransmissionContinuous.regional_transmission_continuous
