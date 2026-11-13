import Packet05RegionalForcingBootstrap
import Packet05RegionalForcingUniform
import Packet05RegionalFirstForcingUniform
import Packet05RegionalLocalizedNorm
import Packet05RegionalScalarLocalization

/-! Turn the actual regional graph equation into a compact global scalar
problem whose forcing has the tangential derivatives obtained by bootstrap. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05RegionalBootstrapUniform
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05RegionalDivergence
  OQ14.Packet05RegionalForcingBootstrap OQ14.Packet05LocalizedForcingBootstrap
  OQ14.Packet05RegionalScalarLocalization OQ14.Packet05RegionalFluxCutoff
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05LocalDerivative
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem regional_bootstrapped_scalar_uniform
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
    (hU0 : ‖u‖ ≤ U0) (hP : (∑ j : Fin 3, ‖C j‖) ≤ P)
    (hF0 : (∑ j : Fin 3, ‖F j‖) ≤ F0)
    (hF1b : ∀ i, i ≠ 2 → (∑ j : Fin 3, ‖F1 i j‖) ≤ F1b)
    (hF2b : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → (∑ j : Fin 3, ‖F2 i t j‖) ≤ F2b) :
    let U := cutScalar κ u
    let G := localizedGradient κ u C
    let R := localizedForcing κ A u F d hd
    let D := cutFluxSource κ.complexTest.toTest (fun j => flux A C d hd j-F j)
    let Hceil := Real.sqrt (OQ14.Packet05EnergyEnvelope.envelope P F1b d b M a τa τb) + 3*τb*P
    let K0 := α*U0
    let K1 := α*P+β*U0
    let K2 := α*F0+3*(1+d)*a*β*U0
    let K3 := α*F1b+β*F0+(1+d)*(3*a*(β*P+γ*U0)+3*b*β*U0)
    let K4 := α*F2b + β*(F1b+F1b) + γ*F0 + (1+d)*3*
      (a*(β*Hceil + 2*γ*P + ξ*U0) + 2*b*(β*P+γ*U0) + c*β*U0)
    let K := max 0 (max K0 (max K1 (max K2 (max K3 K4))))
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
  dsimp only
  obtain ⟨hG,hdiv',hD,hU,hR⟩ := localize_regional_scalar_equation Ω S A u C F d hd
    (fun j => global_partial_on Ω _ _ j (hC j)) hdiv κ hκΩ hκS
  let R := localizedForcing κ A u F d hd
  let R1 (i : Fin 3) (j : Fin 3) := forceDerivative κ hκ2 A hA2 u (C i) F (F1 i) d hd i j
  have hR1 (i : Fin 3) (hi : i ≠ 2) : ∀ j, HasWeakPartial (R j) (R1 i j) i :=
    forcing_first_tangential V κ hκ2 hκV A hA2 u (C i) F (F1 i) d hd i hi
      (global_partial_on V _ _ i (hC i)) (fun j => global_partial_on V _ _ i (hF1 i hi j))
  have hCi (j : Fin 3) : ‖C j‖ ≤ P :=
    (Finset.single_le_sum (fun k _ => norm_nonneg (C k)) (Finset.mem_univ j)).trans hP
  have hFj (j : Fin 3) : ‖F j‖ ≤ F0 :=
    (Finset.single_le_sum (fun k _ => norm_nonneg (F k)) (Finset.mem_univ j)).trans hF0
  have hFi (i : Fin 3) (hi : i ≠ 2) (j : Fin 3) : ‖F1 i j‖ ≤ F1b :=
    (Finset.single_le_sum (fun k _ => norm_nonneg (F1 i k)) (Finset.mem_univ j)).trans (hF1b i hi)
  have hnorm := OQ14.Packet05RegionalLocalizedNorm.localized_fields_norm κ A u C F d hd U0 P F0 a α β hU0 hCi hFj ha hα hβ
  let K0 := α*U0
  let K1 := α*P+β*U0
  let K2 := α*F0+3*(1+d)*a*β*U0
  let K3 := α*F1b+β*F0+(1+d)*(3*a*(β*P+γ*U0)+3*b*β*U0)
  let Hceil := Real.sqrt (OQ14.Packet05EnergyEnvelope.envelope P F1b d b M a τa τb) + 3*τb*P
  let K4 := α*F2b + β*(F1b+F1b) + γ*F0 + (1+d)*3*
      (a*(β*Hceil + 2*γ*P + ξ*U0) + 2*b*(β*P+γ*U0) + c*β*U0)
  let K := max 0 (max K0 (max K1 (max K2 (max K3 K4))))
  have hk0 : K0 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hk1 : K1 ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hk2 : K2 ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hk3 : K3 ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hk4 : K4 ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  have hR1norm (i : Fin 3) (hi : i ≠ 2) (j : Fin 3) : ‖R1 i j‖ ≤ K3 :=
    OQ14.Packet05RegionalFirstForcingUniform.first_forcing_uniform κ hκ2 A hA2 u C F (F1 i) d hd i j
      U0 P F0 F1b a b α β γ hU0 (hCi i) (hFj j) (hFi i hi j) ha (fun j k x => hb j k i x) hα hβ (fun k x => hγ k i x)
  have hex (i : Fin 3) (hi : i ≠ 2) (t : Fin 3) (ht : t ≠ 2) (j : Fin 3) :
      ∃ H, HasWeakPartial (R1 i j) H t ∧ ‖H‖ ≤ K4 := by
    obtain ⟨Di,Dt,Dit,hDi,hDt,hDit,hDitN⟩ := OQ14.Packet05RegionalForcingUniform.regional_forcing_bootstrap_uniform
      g hg A hA2 hA3 u C F (F1 i) (F1 t) (F2 i t) d hd hC hu hF i t hi ht (hF1 i hi) (hF1 t ht) (hF2 i hi t ht)
      Ω S₀ V hdiv θ hθΩ hθS τ hτV δ hδ (hτS t ht) b hb M hM B hB hmetric a τa τb ha hτa hτb
      κ hκ2 hκ3 hκV c α β γ ξ U0 P F0 F1b F1b F2b (hc i t) hα hβ hγ (fun k x => hξ k i t x)
      hU0 hP hF0 (hF1b i hi) (hF1b t ht) (hF2b i hi t ht)
    have heq : Di j = R1 i j := weak_partial_unique (R j) (Di j) (R1 i j) i (hDi j) (hR1 i hi j)
    refine ⟨Dit j,?_,hDitN j⟩
    rw [← heq]
    exact hDit j
  classical
  let R2 (i t : Fin 3) (j : Fin 3) :=
    if hi : i ≠ 2 then if ht : t ≠ 2 then Classical.choose (hex i hi t ht j) else 0 else 0
  refine ⟨hG,hdiv',hD,hU,hR,hnorm.1.trans hk0,fun j => (hnorm.2.1 j).trans hk1,
    (fun j => (hnorm.2.2 j).trans hk2),R1,R2,hR1,?_,?_,?_⟩
  · intro i hi t ht j
    simpa [R2,hi,ht] using (Classical.choose_spec (hex i hi t ht j)).1
  · intro i hi j
    exact (hR1norm i hi j).trans hk3
  · intro i hi t ht j
    exact (by simpa [R2,hi,ht] using (Classical.choose_spec (hex i hi t ht j)).2 : ‖R2 i t j‖ ≤ K4) |>.trans hk4

end OQ14.Packet05RegionalBootstrapUniform
#print axioms OQ14.Packet05RegionalBootstrapUniform.regional_bootstrapped_scalar_uniform
