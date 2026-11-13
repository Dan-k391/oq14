import Packet05IncidentUniformH2
import Packet05UniformMaterialCorrection
import Packet05NestedCutoffSupport
import Packet06ScalarGaussLocalization

/-! Uniform actual driven correction, including the fixed smooth illumination. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet07DrivenUniformCorrection
open MeasureTheory Set Metric Maxwell WeakCurl WeakPoynting DivCurlCompact
open scoped Topology
abbrev Space := Maxwell.Space

theorem driven_correction {A : Type*} (c : A → StaticCoefficient.Coefficient)
    (z : A → ℂ) (u : A → VectorFourier.VectorL2) (R S Z B L : ℝ)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (hc : ∀ a x, x ∉ closedBall (0 : Space) S → (c a).value (VectorFourier.coordinateMap x)=0)
    (hb : ∀ a, (c a).bound ≤ B) (hz : ∀ a, ‖z a‖ ≤ Z) (hu : ∀ a, ‖u a‖ ≤ L)
    (χ : ContDiffBump (0 : Space)) (hχR : χ.rOut < R)
    (E : Field) (hE : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => E x i)) :
    let W : A → Field := fun a x i => E x i + Packet06ComplexPotential.correction (z a) (DynamicVolume.source (c a) (u a)) x i
    ∃ hW : ∀ a i, Continuous (fun x => W a x i),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a k,
      ∃ D : Fin 3 → L2Scalar, ∃ T : Fin 3 → Fin 3 → L2Scalar,
        (∀ i, HasWeakPartial (Packet06ScalarGaussLocalization.correction χ (W a) (hW a) k) (D i) i) ∧
        (∀ i j, HasWeakPartial (D i) (T i j) j) ∧
        ‖Packet06ScalarGaussLocalization.correction χ (W a) (hW a) k‖ ≤ K ∧
        (∀ i, ‖D i‖ ≤ K) ∧ (∀ i j, ‖T i j‖ ≤ K) := by
  dsimp only
  let W : A → Field := fun a x i => E x i + Packet06ComplexPotential.correction (z a) (DynamicVolume.source (c a) (u a)) x i
  have hW : ∀ a i, Continuous (fun x => W a x i) := by
    intro a i
    exact (hE i).continuous.add (Packet06ComplexPotential.correction_continuous (z a) S
      (StaticCoefficient.sqrtMultiplier (c a) (u a)) (DynamicVolume.source (c a) (u a))
      (DynamicVolume.source_zero (c a) (u a) S (hc a)) (StaticNewton.material_source_ae (c a) (u a)) i)
  let ψ : Test := (Packet05NestedChartCutoffs.realTest χ).complexTest.toTest
  have hψ : ContDiff ℝ 2 ψ.function := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hψR : tsupport ψ.function ⊆ ball (0 : Space) R := by
    have he : tsupport ψ.function = closedBall (0 : Space) χ.rOut :=
      (Packet05NestedCutoffSupport.complex_support (Packet05NestedChartCutoffs.realTest χ)).trans χ.tsupport_eq
    rw [he]
    exact closedBall_subset_ball hχR
  obtain ⟨N,hN,hall⟩ := Packet05UniformMaterialCorrection.material_family_correction c z u R S Z B L hR hS hZ hL hc hb hz hu ψ hψ hψR
  have hk (k : Fin 3) : ∃ K : ℝ, 0 ≤ K ∧ ∀ a,
      ∃ D : Fin 3 → L2Scalar, ∃ T : Fin 3 → Fin 3 → L2Scalar,
        (∀ i, HasWeakPartial (Packet06ScalarGaussLocalization.correction χ (W a) (hW a) k) (D i) i) ∧
        (∀ i j, HasWeakPartial (D i) (T i j) j) ∧
        ‖Packet06ScalarGaussLocalization.correction χ (W a) (hW a) k‖ ≤ K ∧
        (∀ i, ‖D i‖ ≤ K) ∧ (∀ i j, ‖T i j‖ ≤ K) := by
    choose U D T hD hT hval hUn hDn hTn hpoint using fun a => hall a k
    let f : Space → ℂ := fun x => (χ x : ℂ)*E x k
    have hf : ContDiff ℝ (⊤ : ℕ∞) f := (Complex.ofRealCLM.contDiff.comp χ.contDiff).mul (hE k)
    have hfc : HasCompactSupport f := (χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right
    obtain ⟨K,hK,hadd⟩ := Packet05IncidentUniformH2.fixed_smooth_addition U N hN
      (fun a => ⟨D a,T a,hD a,hT a,hUn a,hDn a,hTn a⟩) f hf hfc
    refine ⟨K,hK,?_⟩
    intro a
    obtain ⟨V,D',T',hD',hT',hv,hvn,hdn,htn⟩ := hadd a
    have heq : Packet06ScalarGaussLocalization.correction χ (W a) (hW a) k = V := by
      apply Lp.ext
      filter_upwards [Packet06ScalarGaussLocalization.correction_ae χ (W a) (hW a) k,hv,hval a] with x hx hy hz'
      have hψx : ψ.function x = (χ x : ℂ) := rfl
      rw [hx,hy,hz',hψx]
      dsimp [W,f,ψ,Packet05NestedChartCutoffs.realTest,ConicalGradientGraph.bump]
      ring
    rw [← heq] at hD' hvn
    exact ⟨D',T',hD',hT',hvn,hdn,htn⟩
  choose K hK hbound using hk
  refine ⟨hW,∑ k : Fin 3, K k,Finset.sum_nonneg (fun k _ => hK k),?_⟩
  intro a k
  obtain ⟨D,T,hD,hT,hu',hd,ht⟩ := hbound k a
  have hk' : K k ≤ ∑ i : Fin 3, K i := Finset.single_le_sum (fun i _ => hK i) (Finset.mem_univ k)
  exact ⟨D,T,hD,hT,hu'.trans hk',fun i => (hd i).trans hk',fun i j => (ht i j).trans hk'⟩
end OQ14.Packet07DrivenUniformCorrection
#print axioms OQ14.Packet07DrivenUniformCorrection.driven_correction
