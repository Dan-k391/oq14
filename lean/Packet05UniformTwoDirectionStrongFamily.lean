import Packet05UniformTwoDirectionStrong

/-! One fixed pair of derivative ceilings works for an entire field family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace OQ14.Packet05UniformTwoDirectionStrongFamily
open MeasureTheory Set Filter Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalPartial Packet05RegionalDivergence Packet05ScalarDielectricFlux
  Packet05ScalarCutoffTransfer Packet05RegionalScalarLocalization Packet05GraphSlopeMultiplier
open scoped Topology
abbrev Plane := ConicalSmoothJunction.Plane

theorem uniform_two_direction_strong_family
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (u D : ℕ → L2Scalar) (C F : ℕ → L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (S₀ V S : Set Space) (hV : IsOpen V) (hVS₀ : V ⊆ S₀)
    (τ : RealTest Set.univ) (hτ2 : ContDiff ℝ 2 τ.function) (hτ : ∀ x ∈ V, τ.function x = 1)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hτS : ∀ i, i ≠ 2 → ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis i ∈ S₀)
    (κ : RealTest Set.univ) (hκ2 : ContDiff ℝ 2 κ.function) (hκV : tsupport κ.function ⊆ V)
    (hκS : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ)))
    (ζ : RealTest Set.univ) (δ : ℝ) (hδ : 0 < δ)
    (hζS : ∀ t, t ≠ 2 → ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis t ∈ S)
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
    (hηb : ∀ j x, ‖dcoord ζ.complexTest.function x j‖ ≤ ηb)  (c τc κa κb κc : ℝ)
    (hc : ∀ i t j k x, ‖dcoord (OQ14.Packet05MatrixWeakDerivative.derivativeMatrix A hA2 i j k).function x t‖ ≤ c)
    (hτc : ∀ i t x, ‖dcoord (OQ14.MaxwellCutoffCommutator.derivativeCutoff τ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hτ2) i).function x t‖ ≤ τc)
    (hκa : ∀ x, ‖κ.complexTest.function x‖ ≤ κa)
    (hκb : ∀ j x, ‖dcoord κ.complexTest.function x j‖ ≤ κb)
    (hκc : ∀ j t x, ‖dcoord (OQ14.MaxwellCutoffCommutator.derivativeCutoff κ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hκ2) j).function x t‖ ≤ κc)  (K : ℝ)
    (W : Set Space) (hW : IsOpen W) (hWV : W ⊆ V)
    (hκW : ∀ x ∈ W, κ.function x = 1) (hζW : ∀ x ∈ W, ζ.function x = 1) (hfamily : ∀ᶠ m : ℕ in atTop,
      (∀ j, HasWeakPartial (u m) (C m j) j) ∧
      HasWeakDivergence (fun j => flux A (C m) d hd j-F m j) (D m) ∧
      (∀ᵐ x ∂volume, x ∈ S₀ → D m x = 0) ∧ CompactRepresentative (u m) ∧
      (∀ j, CompactRepresentative (F m j)) ∧ (∀ j, ‖C m j‖ ≤ K) ∧ (∀ j, ‖F m j‖ ≤ K) ∧
      ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
        (∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F m j) (F1 i j) i) ∧
        (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t) ∧
        (∀ i, i ≠ 2 → ∀ j, ‖F1 i j‖ ≤ K) ∧
        (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, ‖F2 i t j‖ ≤ K)) :
    let P := 3 * Real.sqrt (Packet05EnergyEnvelope.envelope (3*K) (3*K) d b M a τa τb) + 9*τb*K
    let Q := Real.sqrt (Packet05EnergyEnvelope.envelope
      (Packet05SecondEnvelope.gradient (3*K) (3*K) d b M a τa τb κa κb)
      (Packet05SecondEnvelope.forcing (3*K) (3*K) (3*K) (3*K) (3*K) d b a c τa τb τc κa κb κc M)
      d b M a ηa ηb) + 3*ηb*(Packet05SecondEnvelope.gradient (3*K) (3*K) d b M a τa τb κa κb)
    ∀ᶠ m : ℕ in atTop, ∃ D0 D1 H00 H01 H10 H11 : L2Vector,
      (∀ j, HasWeakPartial (cutScalar τ (C m j)) (D0 j) 0) ∧
      (∀ j, HasWeakPartial (cutScalar τ (C m j)) (D1 j) 1) ∧
      (∀ j, HasPartialOn W (C m j) (D0 j) 0) ∧ (∀ j, HasPartialOn W (C m j) (D1 j) 1) ∧
      (∀ j, HasPartialOn W (D0 j) (H00 j) 0) ∧ (∀ j, HasPartialOn W (D0 j) (H01 j) 1) ∧
      (∀ j, HasPartialOn W (D1 j) (H10 j) 0) ∧ (∀ j, HasPartialOn W (D1 j) (H11 j) 1) ∧
      (∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C m 0) D0 j)) (H00 j) 0) ∧
      (∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C m 0) D0 j)) (H01 j) 1) ∧
      (∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C m 1) D1 j)) (H10 j) 0) ∧
      (∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C m 1) D1 j)) (H11 j) 1) ∧
      (∑ j : Fin 3, ‖D0 j‖) ≤ P ∧ (∑ j : Fin 3, ‖D1 j‖) ≤ P ∧
      (∀ j, ‖H00 j‖ ≤ Q ∧ ‖H01 j‖ ≤ Q ∧ ‖H10 j‖ ≤ Q ∧ ‖H11 j‖ ≤ Q) := by
  dsimp only
  filter_upwards [hfamily] with m hm
  obtain ⟨hC,hdiv,hD,hu,hF,hCn,hFn,F1,F2,hF1,hF2,hF1n,hF2n⟩ := hm
  exact Packet05UniformTwoDirectionStrong.uniform_two_direction_strong g hg A hA2 hA3
    (u m) (D m) (C m) (F m) F1 F2 d hd hC hdiv hu hF hF1 hF2
    S₀ V S hV hVS₀ hD τ hτ2 hτ δ₀ hδ₀ hτS κ hκ2 hκV hκS ζ δ hδ hζS
    b hb M hM B hB hmetricτ hmetricζ a τa τb ηa ηb ha hτa hτb hηa hηb
    c τc κa κb κc hc hτc hκa hκb hκc K hCn hFn hF1n hF2n W hW hWV hκW hζW

end OQ14.Packet05UniformTwoDirectionStrongFamily
#print axioms OQ14.Packet05UniformTwoDirectionStrongFamily.uniform_two_direction_strong_family
