import Packet05RegionalDirectionalTangentialH2
import Packet05ExplicitSecondForcing
import Packet05SecondRegionalForcingNorm
import Packet05EnergyEnvelope
import Packet05LocalizedForcingBootstrap

/-! Bootstrap both tangential derivatives of the localized regional forcing
from the actual regional PDE, without a priori scalar H² regularity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05RegionalForcingUniform
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05RegionalDivergence
  OQ14.Packet05RegionalDirectionalTangentialH2 OQ14.Packet05LocalizedForcingBootstrap
  OQ14.Packet05RegionalScalarLocalization OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05GraphSlopeMultiplier
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem regional_forcing_bootstrap_uniform
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
    (hζV : tsupport ζ.function ⊆ V)  (c α β γ ξ U P F0 F1 F2 F12 : ℝ)
    (hc : ∀ j k x, ‖dcoord (OQ14.Packet05MatrixWeakDerivative.derivativeMatrix A hA2 i j k).function x t‖ ≤ c)
    (hα : ∀ x, ‖ζ.complexTest.function x‖ ≤ α)
    (hβ : ∀ k x, ‖dcoord ζ.complexTest.function x k‖ ≤ β)
    (hγ : ∀ k l x, ‖dcoord (OQ14.MaxwellCutoffCommutator.derivativeCutoff ζ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hζ2) k).function x l‖ ≤ γ)
    (hξ : ∀ k x, ‖dcoord (OQ14.MaxwellCutoffCommutator.derivativeCutoff
      (OQ14.MaxwellCutoffCommutator.derivativeCutoff ζ.complexTest.toTest (Complex.ofRealCLM.contDiff.comp hζ2) k)
      (by
        have hh : ContDiff ℝ 2 (fderiv ℝ ζ.complexTest.function) :=
          (contDiff_succ_iff_fderiv (n := 2)).mp (Complex.ofRealCLM.contDiff.comp hζ3) |>.2.2
        exact hh.clm_apply contDiff_const) i).function x t‖ ≤ ξ)
    (hU : ‖u‖ ≤ U) (hP : (∑ j : Fin 3, ‖C j‖) ≤ P)
    (hF0 : (∑ j : Fin 3, ‖F j‖) ≤ F0) (hF1 : (∑ j : Fin 3, ‖Fi j‖) ≤ F1)
    (hF2 : (∑ j : Fin 3, ‖Ft j‖) ≤ F2) (hF12 : (∑ j : Fin 3, ‖Fit j‖) ≤ F12) :
    let Hceil := Real.sqrt (OQ14.Packet05EnergyEnvelope.envelope P F2 d b M a τa τb) + 3*τb*P
    ∃ Di Dt Dit : L2Vector,
      (∀ j, HasWeakPartial (localizedForcing ζ A u F d hd j) (Di j) i) ∧
      (∀ j, HasWeakPartial (localizedForcing ζ A u F d hd j) (Dt j) t) ∧
      (∀ j, HasWeakPartial (Di j) (Dit j) t) ∧
      (∀ j, ‖Dit j‖ ≤ α*F12 + β*(F1+F2) + γ*F0 + (1+d)*3*
        (a*(β*Hceil + 2*γ*P + ξ*U) + 2*b*(β*P+γ*U) + c*β*U)) := by
  dsimp only
  obtain ⟨H,hH,hHnorm⟩ := regional_tangential_gradient_derivative g hg τ A u C F Ft d hd hC Ω hdiv
    hu hF S₀ θ hθΩ hθS δ hδ t i ht hFt hτS b hb M hM B hB hmetric a τa τb ha hτa hτb
  have hτc : ∀ x ∈ V, τ.complexTest.function x = 1 := by
    intro x hx
    simp [RealTest.complexTest,hτV x hx]
  have hCit : HasPartialOn V (C i) H t := by
    apply cutoff_partial_on V τ.complexTest.toTest (C i) H t hτc
    exact hH
  let Di := forceDerivative ζ hζ2 A hA2 u (C i) F Fi d hd i
  let Dt := forceDerivative ζ hζ2 A hA2 u (C t) F Ft d hd t
  let Dit := OQ14.Packet05ExplicitSecondForcing.forceSecondDerivative ζ hζ2 hζ3 A hA2 hA3 u (C i) (C t) H F Fi Ft Fit d hd i t
  have hDi : ∀ j, HasWeakPartial (localizedForcing ζ A u F d hd j) (Di j) i :=
    forcing_first_tangential V ζ hζ2 hζV A hA2 u (C i) F Fi d hd i hi
      (global_partial_on V _ _ i (hC i)) (fun j => global_partial_on V _ _ i (hFi j))
  have hDt : ∀ j, HasWeakPartial (localizedForcing ζ A u F d hd j) (Dt j) t :=
    forcing_first_tangential V ζ hζ2 hζV A hA2 u (C t) F Ft d hd t ht
      (global_partial_on V _ _ t (hC t)) (fun j => global_partial_on V _ _ t (hFt j))
  have hDit : ∀ j, HasWeakPartial (Di j) (Dit j) t :=
    OQ14.Packet05ExplicitSecondForcing.forcing_second_tangential_explicit V ζ hζ2 hζ3 hζV A hA2 hA3 u (C i) (C t) H F Fi Ft Fit d hd i t ht
      (global_partial_on V _ _ t (hC t)) hCit
      (fun j => global_partial_on V _ _ t (hFt j)) (fun j => global_partial_on V _ _ t (hFit j))
  refine ⟨Di,Dt,Dit,hDi,hDt,hDit,?_⟩
  intro j
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0 0 0)
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 0 0)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0 0 0)
  have hτa0 : 0 ≤ τa := (norm_nonneg _).trans (hτa 0)
  have hτb0 : 0 ≤ τb := (norm_nonneg _).trans (hτb 0 0)
  have hα0 : 0 ≤ α := (norm_nonneg _).trans (hα 0)
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans (hβ 0 0)
  have hγ0 : 0 ≤ γ := (norm_nonneg _).trans (hγ 0 0 0)
  have hξ0 : 0 ≤ ξ := (norm_nonneg _).trans (hξ 0 0)
  have hCi : ‖C i‖ ≤ P := (Finset.single_le_sum (fun k _ => norm_nonneg (C k)) (Finset.mem_univ i)).trans hP
  have hCt : ‖C t‖ ≤ P := (Finset.single_le_sum (fun k _ => norm_nonneg (C k)) (Finset.mem_univ t)).trans hP
  have hFj : ‖F j‖ ≤ F0 := (Finset.single_le_sum (fun k _ => norm_nonneg (F k)) (Finset.mem_univ j)).trans hF0
  have hFij : ‖Fi j‖ ≤ F1 := (Finset.single_le_sum (fun k _ => norm_nonneg (Fi k)) (Finset.mem_univ j)).trans hF1
  have hFtj : ‖Ft j‖ ≤ F2 := (Finset.single_le_sum (fun k _ => norm_nonneg (Ft k)) (Finset.mem_univ j)).trans hF2
  have hFitj : ‖Fit j‖ ≤ F12 := (Finset.single_le_sum (fun k _ => norm_nonneg (Fit k)) (Finset.mem_univ j)).trans hF12
  have he := OQ14.Packet05EnergyEnvelope.regional_energy_le_envelope C Ft P F2 d b M a τa τb
    hd hb0 ha0 hτa0 hτb0 (by simpa only [Fin.sum_univ_three] using hP) hF2
  have hH' : ‖H‖ ≤ Real.sqrt (OQ14.Packet05EnergyEnvelope.envelope P F2 d b M a τa τb) + 3*τb*P :=
    hHnorm.trans (add_le_add (Real.sqrt_le_sqrt he) (mul_le_mul_of_nonneg_left hCi (by positivity)))
  have hraw := OQ14.Packet05SecondRegionalForcingNorm.second_forcing_norm ζ hζ2 hζ3 A hA2 hA3 u (C i) (C t) H
    F Fi Ft Fit d hd i t j a b c α β γ ξ ha hb hc hα hβ hγ hξ
  have h1 := mul_le_mul_of_nonneg_left hFitj hα0
  have h2 := mul_le_mul_of_nonneg_left (add_le_add hFij hFtj) hβ0
  have h3 := mul_le_mul_of_nonneg_left hFj hγ0
  have h4 := mul_le_mul_of_nonneg_left hH' hβ0
  have h5 := mul_le_mul_of_nonneg_left (add_le_add hCi hCt) hγ0
  have h6 := mul_le_mul_of_nonneg_left hU hξ0
  have h7 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h4 h5) h6) ha0
  have h8 := mul_le_mul_of_nonneg_left hCi hβ0
  have h9 := mul_le_mul_of_nonneg_left hCt hβ0
  have h10 := mul_le_mul_of_nonneg_left hU hγ0
  have h11 := mul_le_mul_of_nonneg_left (add_le_add h8 h10) hb0
  have h12 := mul_le_mul_of_nonneg_left (add_le_add h9 h10) hb0
  have h13 := mul_le_mul_of_nonneg_left hU (show 0 ≤ c*β by positivity)
  have h14 : a*(β*‖H‖+γ*(‖C i‖+‖C t‖)+ξ*‖u‖) +
      b*(β*‖C i‖+γ*‖u‖) + b*(β*‖C t‖+γ*‖u‖) + c*β*‖u‖ ≤
      a*(β*(Real.sqrt (OQ14.Packet05EnergyEnvelope.envelope P F2 d b M a τa τb)+3*τb*P)+2*γ*P+ξ*U) +
        2*b*(β*P+γ*U) + c*β*U := by nlinarith
  have h15 := mul_le_mul_of_nonneg_left h14 (show 0 ≤ (1+d)*3 by positivity)
  exact hraw.trans (by linarith)

end OQ14.Packet05RegionalForcingUniform
#print axioms OQ14.Packet05RegionalForcingUniform.regional_forcing_bootstrap_uniform
