import Packet05EventualChoice
import Packet05RegionalFamilyBootstrap

/-! Uniform regional bootstrap for an entire fixed-chart field family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OQ14.Packet05RegionalFamilyChosenBootstrap
open MeasureTheory Set Filter Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalPartial Packet05RegionalDivergence Packet05RegionalScalarLocalization Packet05RegionalFluxCutoff
  Packet05ScalarCutoffTransfer Packet05ScalarDielectricFlux Packet05GraphSlopeMultiplier
open scoped Topology
abbrev Plane := ConicalSmoothJunction.Plane

theorem regional_family_chosen_bootstrap
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (u : ℕ → L2Scalar) (C F : ℕ → L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (Ω S₀ V S : Set Space)
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
    (hκS : ∀ x ∈ S, κ.function =ᶠ[nhds x] (fun _ => (1 : ℝ)))  (c α β γ ξ U0 P F0 F1b F2b : ℝ)
    (hc : ∀ i t j k x, ‖dcoord (OQ14.Packet05MatrixWeakDerivative.derivativeMatrix A hA2 i j k).function x t‖ ≤ c)
    (hα : ∀ x, ‖κ.complexTest.function x‖ ≤ α)
    (hβ : ∀ i x, ‖dcoord κ.complexTest.function x i‖ ≤ β)
    (hγ : ∀ i t x, ‖dcoord (OQ14.MaxwellCutoffCommutator.derivativeCutoff κ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hκ2) i).function x t‖ ≤ γ)
    (hξ : ∀ k i t x, ‖dcoord (OQ14.MaxwellCutoffCommutator.derivativeCutoff
      (OQ14.MaxwellCutoffCommutator.derivativeCutoff κ.complexTest.toTest (Complex.ofRealCLM.contDiff.comp hκ2) k)
      (by
        have hh : ContDiff ℝ 2 (fderiv ℝ κ.complexTest.function) :=
          (contDiff_succ_iff_fderiv (n := 2)).mp (Complex.ofRealCLM.contDiff.comp hκ3) |>.2.2
        exact hh.clm_apply contDiff_const) i).function x t‖ ≤ ξ)
    (hfamily : ∀ᶠ m : ℕ in atTop, ∃ (F1 : Fin 3 → L2Vector) (F2 : Fin 3 → Fin 3 → L2Vector),
      (∀ j, HasWeakPartial (u m) (C m j) j) ∧ CompactRepresentative (u m) ∧
      (∀ j, CompactRepresentative (F m j)) ∧
      (∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F m j) (F1 i j) i) ∧
      (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t) ∧
      HasDivergenceOn Ω (fun j => flux A (C m) d hd j-F m j) 0 ∧
      ‖u m‖ ≤ U0 ∧ (∑ j : Fin 3, ‖C m j‖) ≤ P ∧ (∑ j : Fin 3, ‖F m j‖) ≤ F0 ∧
      (∀ i, i ≠ 2 → (∑ j : Fin 3, ‖F1 i j‖) ≤ F1b) ∧
      (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → (∑ j : Fin 3, ‖F2 i t j‖) ≤ F2b)) :
    let K := Packet05RegionalBootstrapCeiling.ceiling P F1b d b M a τa τb α β γ ξ U0 F0 F2b c
    ∀ᶠ m : ℕ in atTop,
      let U := cutScalar κ (u m)
      let G := localizedGradient κ (u m) (C m)
      let R := localizedForcing κ A (u m) (F m) d hd
      let D := cutFluxSource κ.complexTest.toTest (fun j => flux A (C m) d hd j-F m j)
      (∀ j, HasWeakPartial U (G j) j) ∧
      HasWeakDivergence (fun j => flux A G d hd j-R j) D ∧
      (∀ᵐ x ∂volume, x ∈ S → D x = 0) ∧ CompactRepresentative U ∧
      (∀ j, CompactRepresentative (R j)) ∧ ‖U‖ ≤ K ∧ (∀ j, ‖G j‖ ≤ K) ∧
      (∀ j, ‖R j‖ ≤ K) ∧
      ∃ R1 : Fin 3 → L2Vector, ∃ R2 : Fin 3 → Fin 3 → L2Vector,
        (∀ i, i ≠ 2 → ∀ j, HasWeakPartial (R j) (R1 i j) i) ∧
        (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (R1 i j) (R2 i t j) t) ∧
        (∀ i, i ≠ 2 → ∀ j, ‖R1 i j‖ ≤ K) ∧
        (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, ‖R2 i t j‖ ≤ K) := by
  classical
  let PropAt (m : ℕ) (q : (Fin 3 → L2Vector) × (Fin 3 → Fin 3 → L2Vector)) : Prop :=
    (∀ j, HasWeakPartial (u m) (C m j) j) ∧ CompactRepresentative (u m) ∧
    (∀ j, CompactRepresentative (F m j)) ∧
    (∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F m j) (q.1 i j) i) ∧
    (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (q.1 i j) (q.2 i t j) t) ∧
    HasDivergenceOn Ω (fun j => flux A (C m) d hd j-F m j) 0 ∧
    ‖u m‖ ≤ U0 ∧ (∑ j : Fin 3, ‖C m j‖) ≤ P ∧ (∑ j : Fin 3, ‖F m j‖) ≤ F0 ∧
    (∀ i, i ≠ 2 → (∑ j : Fin 3, ‖q.1 i j‖) ≤ F1b) ∧
    (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → (∑ j : Fin 3, ‖q.2 i t j‖) ≤ F2b)
  have hex : ∀ᶠ m : ℕ in atTop, ∃ q, PropAt m q := by
    filter_upwards [hfamily] with m hm
    obtain ⟨F1,F2,h⟩ := hm
    exact ⟨⟨F1,F2⟩,h⟩
  obtain ⟨q,hq⟩ := Packet05EventualChoice.choose_eventually PropAt hex
  exact Packet05RegionalFamilyBootstrap.regional_family_bootstrap g hg A hA2 hA3 u C F
    (fun m => (q m).1) (fun m => (q m).2) d hd Ω S₀ V S θ hθΩ hθS τ hτV δ hδ hτS
    b hb M hM B hB hmetric a τa τb ha hτa hτb κ hκ2 hκ3 hκΩ hκV hκS
    c α β γ ξ U0 P F0 F1b F2b hc hα hβ hγ hξ hq

end OQ14.Packet05RegionalFamilyChosenBootstrap
#print axioms OQ14.Packet05RegionalFamilyChosenBootstrap.regional_family_chosen_bootstrap
