import Packet05RegionalForcingBootstrap
import Packet05RegionalScalarLocalization

/-! Turn the actual regional graph equation into a compact global scalar
problem whose forcing has the tangential derivatives obtained by bootstrap. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05RegionalBootstrappedScalar
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05RegionalDivergence
  OQ14.Packet05RegionalForcingBootstrap OQ14.Packet05LocalizedForcingBootstrap
  OQ14.Packet05RegionalScalarLocalization OQ14.Packet05RegionalFluxCutoff
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05LocalDerivative
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem regional_bootstrapped_scalar
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
    (hκS : ∀ x ∈ S, κ.function =ᶠ[nhds x] (fun _ => (1 : ℝ))) :
    let U := cutScalar κ u
    let G := localizedGradient κ u C
    let R := localizedForcing κ A u F d hd
    let D := cutFluxSource κ.complexTest.toTest (fun j => flux A C d hd j-F j)
    (∀ j, HasWeakPartial U (G j) j) ∧
    HasWeakDivergence (fun j => flux A G d hd j-R j) D ∧
    (∀ᵐ x ∂volume, x ∈ S → D x = 0) ∧ CompactRepresentative U ∧
    (∀ j, CompactRepresentative (R j)) ∧
    ∃ R1 : Fin 3 → L2Vector, ∃ R2 : Fin 3 → Fin 3 → L2Vector,
      (∀ i, i ≠ 2 → ∀ j, HasWeakPartial (R j) (R1 i j) i) ∧
      (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (R1 i j) (R2 i t j) t) := by
  dsimp only
  obtain ⟨hG,hdiv',hD,hU,hR⟩ := localize_regional_scalar_equation Ω S A u C F d hd
    (fun j => global_partial_on Ω _ _ j (hC j)) hdiv κ hκΩ hκS
  refine ⟨hG,hdiv',hD,hU,hR,?_⟩
  classical
  let R := localizedForcing κ A u F d hd
  let R1 (i : Fin 3) (j : Fin 3) :=
    forceDerivative κ hκ2 A hA2 u (C i) F (F1 i) d hd i j
  have hR1 (i : Fin 3) (hi : i ≠ 2) : ∀ j, HasWeakPartial (R j) (R1 i j) i :=
    forcing_first_tangential V κ hκ2 hκV A hA2 u (C i) F (F1 i) d hd i hi
      (global_partial_on V _ _ i (hC i)) (fun j => global_partial_on V _ _ i (hF1 i hi j))
  have hex (i : Fin 3) (hi : i ≠ 2) (t : Fin 3) (ht : t ≠ 2) (j : Fin 3) :
      ∃ H, HasWeakPartial (R1 i j) H t := by
    obtain ⟨Di,Dt,Dit,hDi,hDt,hDit⟩ := regional_forcing_bootstrap g hg A hA2 hA3
      u C F (F1 i) (F1 t) (F2 i t) d hd hC hu hF i t hi ht (hF1 i hi) (hF1 t ht) (hF2 i hi t ht)
      Ω S₀ V hdiv θ hθΩ hθS τ hτV δ hδ (hτS t ht) b hb M hM B hB hmetric a τa τb ha hτa hτb
      κ hκ2 hκ3 hκV
    have heq : Di j = R1 i j := weak_partial_unique (R j) (Di j) (R1 i j) i (hDi j) (hR1 i hi j)
    rw [← heq]
    exact ⟨Dit j,hDit j⟩
  let R2 (i t : Fin 3) (j : Fin 3) :=
    if hi : i ≠ 2 then if ht : t ≠ 2 then Classical.choose (hex i hi t ht j) else 0 else 0
  refine ⟨R1,R2,hR1,?_⟩
  intro i hi t ht j
  simpa [R2,hi,ht] using Classical.choose_spec (hex i hi t ht j)

end OQ14.Packet05RegionalBootstrappedScalar
#print axioms OQ14.Packet05RegionalBootstrappedScalar.regional_bootstrapped_scalar
