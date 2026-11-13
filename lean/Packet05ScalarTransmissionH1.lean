import Packet05GraphNormalFluxH1
import Packet05CurlSourceH1
import Packet05ActualDirectionalGradientH1
import Packet05RegionalDivergenceCongruence

/-! First-order transmission regularity of the scalar graph problem: both
tangential gradient components and the conserved normal flux are H¹ locally,
derived from the equation and tangential forcing derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05ScalarTransmissionH1
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.DivCurlCompact OQ14.Packet05RegionalDivergence
  OQ14.Packet05RegionalDivergenceCongruence OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarPrincipalLocalization OQ14.Packet05ScalarDirectionalTangentialH2
  OQ14.Packet05TangentialGradientH1 OQ14.Packet05GraphNormalFluxH1
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05PartialProduct OQ14.Packet05CurlSourceH1
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem scalar_transmission_h1
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (u D : L2Scalar) (C F F0 F1 : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j-F j) D)
    (hu : CompactRepresentative u) (hF : ∀ j, CompactRepresentative (F j))
    (hF0 : ∀ j, HasWeakPartial (F j) (F0 j) 0)
    (hF1 : ∀ j, HasWeakPartial (F j) (F1 j) 1)
    (S₀ V : Set Space) (hV : IsOpen V) (hVS₀ : V ⊆ S₀)
    (hD : ∀ᵐ x ∂volume, x ∈ S₀ → D x = 0)
    (τ : RealTest Set.univ) (hτ : ∀ x ∈ V, τ.function x = 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hτS0 : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis 0 ∈ S₀)
    (hτS1 : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis 1 ∈ S₀)
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
    (χ : Test) (hχV : tsupport χ.function ⊆ V) :
    ∃ D0 D1 DN : L2Vector,
      (∀ j, HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact (C 0)) (D0 j) j) ∧
      (∀ j, HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact (C 1)) (D1 j) j) ∧
      (∀ j, HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact
        (flux A (cutVector τ C) d hd 2-cutVector τ F 2)) (DN j) j) := by
  have hC0 (j : Fin 3) : ∃ v, HasWeakPartial (cutScalar τ (C j)) v 0 := by
    obtain ⟨v,hv,_⟩ := directional_tangential_gradient_derivative g hg τ A u D C F F0 d hd
      hC hdiv hu hF S₀ δ hδ 0 j (by decide) hF0 hD hτS0 b hb M hM B hB hmetric a τa τb ha hτa hτb
    exact ⟨v,hv⟩
  have hC1 (j : Fin 3) : ∃ v, HasWeakPartial (cutScalar τ (C j)) v 1 := by
    obtain ⟨v,hv,_⟩ := directional_tangential_gradient_derivative g hg τ A u D C F F1 d hd
      hC hdiv hu hF S₀ δ hδ 1 j (by decide) hF1 hD hτS1 b hb M hM B hB hmetric a τa τb ha hτa hτb
    exact ⟨v,hv⟩
  classical
  choose DC0 hDC0 using hC0
  choose DC1 hDC1 using hC1
  have hτc : ∀ x ∈ V, τ.complexTest.function x = 1 := by
    intro x hx; simp [RealTest.complexTest,hτ x hx]
  obtain ⟨D0,hD0⟩ := localized_tangential_gradient_h1 V hV u C hC τ.complexTest.toTest χ hτc hχV 0 (fun j => ⟨DC0 j,hDC0 j⟩)
  obtain ⟨D1,hD1⟩ := localized_tangential_gradient_h1 V hV u C hC τ.complexTest.toTest χ hτc hχV 1 (fun j => ⟨DC1 j,hDC1 j⟩)
  let C' := cutVector τ C
  let F' := cutVector τ F
  have hCeq (j : Fin 3) : ∀ᵐ x ∂volume, x ∈ V → C' j x = C j x := by
    filter_upwards [cutVector_ae τ C j] with x hx hVx
    rw [hx,hτ x hVx]; simp
  have hFeq (j : Fin 3) : ∀ᵐ x ∂volume, x ∈ V → F' j x = F j x := by
    filter_upwards [cutVector_ae τ F j] with x hx hVx
    rw [hx,hτ x hVx]; simp
  have hD0V : ∀ᵐ x ∂volume, x ∈ V → D x = 0 := by
    filter_upwards [hD] with x hx hVx
    exact hx (hVS₀ hVx)
  have hdiv0 : HasDivergenceOn V (fun j => flux A C d hd j-F j) 0 := by
    intro φ hφ
    have he := global_divergence_on V _ D hdiv φ hφ
    have hz : valuePair φ D = 0 := by
      simp only [valuePair, testPair_integral]
      apply integral_eq_zero_of_ae
      filter_upwards [hD0V] with x hx
      by_cases hxV : x ∈ V
      · simp [hx hxV]
      · have hn : x ∉ tsupport φ.function := fun hh => hxV (hφ hh)
        simp [image_eq_zero_of_nmem_tsupport hn]
    simpa [hz] using he
  have hdiv' : HasDivergenceOn V (fun j => flux A C' d hd j-F' j) 0 := by
    apply divergence_on_of_ae_eq V _ _ 0 hdiv0
    intro j
    filter_upwards [flux_local_ae_eq V A C C' d hd hCeq j,hFeq j,
      Lp.coeFn_sub (flux A C' d hd j) (F' j), Lp.coeFn_sub (flux A C d hd j) (F j)] with x ha hb hc hd' hx
    rw [hc,hd']
    simp only [Pi.sub_apply,ha hx,hb hx]
  let DF0 : L2Vector := fun j => cutoffProductDerivative τ.complexTest.toTest (F j) (F0 j) 0
  let DF1 : L2Vector := fun j => cutoffProductDerivative τ.complexTest.toTest (F j) (F1 j) 1
  have hDF0 (j : Fin 3) : HasWeakPartial (F' j) (DF0 j) 0 := cutoff_weak_partial _ _ _ _ (hF0 j)
  have hDF1 (j : Fin 3) : HasWeakPartial (F' j) (DF1 j) 1 := cutoff_weak_partial _ _ _ _ (hF1 j)
  obtain ⟨DN,hDN⟩ := conserved_normal_flux_h1 V A hA C' F' DC0 DC1 DF0 DF1 d hd hdiv'
    hDC0 hDC1 hDF0 hDF1 χ hχV
  exact ⟨D0,D1,DN,hD0,hD1,hDN⟩

end OQ14.Packet05ScalarTransmissionH1
#print axioms OQ14.Packet05ScalarTransmissionH1.scalar_transmission_h1
