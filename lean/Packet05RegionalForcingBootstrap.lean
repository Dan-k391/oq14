import Packet05RegionalDirectionalTangentialH2
import Packet05LocalizedForcingBootstrap

/-! Bootstrap both tangential derivatives of the localized regional forcing
from the actual regional PDE, without a priori scalar H² regularity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05RegionalForcingBootstrap
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05RegionalDivergence
  OQ14.Packet05RegionalDirectionalTangentialH2 OQ14.Packet05LocalizedForcingBootstrap
  OQ14.Packet05RegionalScalarLocalization OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05GraphSlopeMultiplier
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem regional_forcing_bootstrap
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (u : L2Scalar) (C F Fi Ft Fit : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j) (hu : CompactRepresentative u)
    (hF : ∀ j, CompactRepresentative (F j)) (i t : Fin 3) (hi : i ≠ 2) (ht : t ≠ 2)
    (hFi : ∀ j, HasWeakPartial (F j) (Fi j) i)
    (hFt : ∀ j, HasWeakPartial (F j) (Ft j) t)
    (hFit : ∀ j, HasWeakPartial (Fi j) (Fit j) t)
    (Ω S₀ V : Set Space)
    (hdiv : HasDivergenceOn Ω (fun j => flux A C d hd j-F j) 0)
    (θ : Test) (hθΩ : tsupport θ.function ⊆ Ω)
    (hθS : ∀ x ∈ S₀, θ.function =ᶠ[nhds x] (fun _ => (1 : ℂ)))
    (τ : RealTest Set.univ) (hτV : ∀ x ∈ V, τ.function x = 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hτS : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x+h • basis t ∈ S₀)
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
    (ζ : RealTest Set.univ) (hζ2 : ContDiff ℝ 2 ζ.function) (hζ3 : ContDiff ℝ 3 ζ.function)
    (hζV : tsupport ζ.function ⊆ V) :
    ∃ Di Dt Dit : L2Vector,
      (∀ j, HasWeakPartial (localizedForcing ζ A u F d hd j) (Di j) i) ∧
      (∀ j, HasWeakPartial (localizedForcing ζ A u F d hd j) (Dt j) t) ∧
      (∀ j, HasWeakPartial (Di j) (Dit j) t) := by
  obtain ⟨H,hH,_⟩ := regional_tangential_gradient_derivative g hg τ A u C F Ft d hd hC Ω hdiv
    hu hF S₀ θ hθΩ hθS δ hδ t i ht hFt hτS b hb M hM B hB hmetric a τa τb ha hτa hτb
  have hτc : ∀ x ∈ V, τ.complexTest.function x = 1 := by
    intro x hx
    simp [RealTest.complexTest,hτV x hx]
  have hCit : HasPartialOn V (C i) H t := by
    apply cutoff_partial_on V τ.complexTest.toTest (C i) H t hτc
    exact hH
  let Di := forceDerivative ζ hζ2 A hA2 u (C i) F Fi d hd i
  let Dt := forceDerivative ζ hζ2 A hA2 u (C t) F Ft d hd t
  have hDi : ∀ j, HasWeakPartial (localizedForcing ζ A u F d hd j) (Di j) i :=
    forcing_first_tangential V ζ hζ2 hζV A hA2 u (C i) F Fi d hd i hi
      (global_partial_on V _ _ i (hC i)) (fun j => global_partial_on V _ _ i (hFi j))
  have hDt : ∀ j, HasWeakPartial (localizedForcing ζ A u F d hd j) (Dt j) t :=
    forcing_first_tangential V ζ hζ2 hζV A hA2 u (C t) F Ft d hd t ht
      (global_partial_on V _ _ t (hC t)) (fun j => global_partial_on V _ _ t (hFt j))
  have hDit (j : Fin 3) : ∃ H, HasWeakPartial (Di j) H t :=
    forcing_second_tangential V ζ hζ2 hζ3 hζV A hA2 hA3 u (C i) (C t) H F Fi Ft Fit d hd i t ht
      (global_partial_on V _ _ t (hC t)) hCit
      (fun j => global_partial_on V _ _ t (hFt j)) (fun j => global_partial_on V _ _ t (hFit j)) j
  classical
  choose Dit hDit' using hDit
  exact ⟨Di,Dt,Dit,hDi,hDt,hDit'⟩

end OQ14.Packet05RegionalForcingBootstrap
#print axioms OQ14.Packet05RegionalForcingBootstrap.regional_forcing_bootstrap
