import Packet05QuantitativeCompactGreen
import Packet06UniformGreenOperators

/-! A fixed compact cutoff has one actual Green H2 bound for every source
and every frequency in a bounded complex disk. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05UniformCompactGreen
open MeasureTheory Set Metric Maxwell WeakCurl WeakPoynting DivCurlCompact
  MaxwellCutoffCommutator Packet05QuantitativeCompactGreen

theorem test_bounds (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function) :
    ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ (∀ x, ‖χ.function x‖ ≤ a) ∧
      (∀ i x, ‖dcoord χ.function x i‖ ≤ b) ∧
      ∀ i j x, ‖dcoord (derivativeCutoff χ hχ2 i).function x j‖ ≤ c := by
  obtain ⟨a,ha⟩ := χ.compact.exists_bound_of_continuous χ.regular.continuous
  have hd (i : Fin 3) := (χ.compact.fderiv_apply ℝ (basis i)).exists_bound_of_continuous
    (partial_continuous χ.regular i)
  choose b hb using hd
  have hdd (i j : Fin 3) := ((derivativeCutoff χ hχ2 i).compact.fderiv_apply ℝ (basis j)).exists_bound_of_continuous
    (partial_continuous (derivativeCutoff χ hχ2 i).regular j)
  choose c hc using hdd
  refine ⟨max a 0,∑ i, max (b i) 0,∑ i, ∑ j, max (c i j) 0,le_max_right _ _,
    Finset.sum_nonneg (fun _ _ => le_max_right _ _),
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_right _ _)),
    fun x => (ha x).trans (le_max_left _ _),?_,?_⟩
  · intro i x
    exact (hb i x).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun k _ => le_max_right (b k) 0) (Finset.mem_univ i)))
  · intro i j x
    exact (hc i j x).trans ((le_max_left _ _).trans
      ((Finset.single_le_sum (fun k _ => le_max_right (c i k) 0) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => le_max_right (c k l) 0)) (Finset.mem_univ i))))

theorem uniform_compact_green (R S Z : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function) (hχR : tsupport χ.function ⊆ ball (0 : Space) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ), ‖z‖ ≤ Z → ∀ (F : NewtonL2.ScalarL2) (ρ : Space → ℂ),
      (F : Space → ℂ) =ᵐ[volume] ρ → Integrable ρ → HasCompactSupport ρ →
      (∀ y, y ∉ closedBall 0 S → ρ y=0) →
      ∃ U : L2Scalar, ∃ D : Fin 3 → L2Scalar, ∃ T : Fin 3 → Fin 3 → L2Scalar,
        (∀ i, HasWeakPartial U (D i) i) ∧ (∀ i j, HasWeakPartial (D i) (T i j) j) ∧
        (∀ᵐ x ∂volume, U x=χ.function x*KernelConvolution.response (ComplexGreenKernel.phi z) ρ x) ∧
        ‖U‖ ≤ C*‖F‖ ∧ (∀ i, ‖D i‖ ≤ C*‖F‖) ∧ ∀ i j, ‖T i j‖ ≤ C*‖F‖ := by
  obtain ⟨a,b,c,ha0,hb0,hc0,ha,hb,hc⟩ := test_bounds χ hχ2
  obtain ⟨P,hP0,hP⟩ := Packet06UniformGreenOperators.phi_uniform (R+S) Z (by positivity) hZ
  choose G hG0 hG using Packet06UniformGreenOperators.gradient_uniform (R+S) Z hZ
  choose H hH0 hH using Packet06UniformGreenOperators.hessian_uniform (R+S) Z (by positivity) hZ
  let Gsum := ∑ i : Fin 3, G i
  let Hsum := ∑ i : Fin 3, ∑ j : Fin 3, H i j
  have hGs : 0 ≤ Gsum := Finset.sum_nonneg (fun i _ => hG0 i)
  have hHs : 0 ≤ Hsum := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hH0 i j))
  let C := a*P+(a*Gsum+b*P)+(a*(1+Hsum)+2*b*Gsum+c*P)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC0,?_⟩
  intro z hz F ρ hF hρ hcompact hs
  obtain ⟨U,D,T,hD,hT,hval,hUn,hDn,hTn⟩ := quantitative_compact_green z R S F ρ hF hρ hcompact hs
    χ hχ2 hχR a b c P Gsum Hsum ha0 hb0 hc0 ha hb hc (hP z hz)
    (fun i => (hG i z hz).trans (Finset.single_le_sum (fun k _ => hG0 k) (Finset.mem_univ i)))
    (fun i j => (hH i j z hz).trans
      ((Finset.single_le_sum (fun k _ => hH0 i k) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hH0 k l)) (Finset.mem_univ i))))
  have hC1 : a*P ≤ C := by dsimp [C]; nlinarith [mul_nonneg ha0 hGs,mul_nonneg hb0 hP0,mul_nonneg ha0 (show 0 ≤ 1+Hsum by linarith),mul_nonneg hb0 hGs,mul_nonneg hc0 hP0]
  have hC2 : a*Gsum+b*P ≤ C := by dsimp [C]; nlinarith [mul_nonneg ha0 hP0,mul_nonneg ha0 (show 0 ≤ 1+Hsum by linarith),mul_nonneg hb0 hGs,mul_nonneg hc0 hP0]
  have hC3 : a*(1+Hsum)+2*b*Gsum+c*P ≤ C := by dsimp [C]; nlinarith [mul_nonneg ha0 hP0,mul_nonneg ha0 hGs,mul_nonneg hb0 hP0]
  exact ⟨U,D,T,hD,hT,hval,hUn.trans (mul_le_mul_of_nonneg_right hC1 (norm_nonneg _)),
    fun i => (hDn i).trans (mul_le_mul_of_nonneg_right hC2 (norm_nonneg _)),
    fun i j => (hTn i j).trans (mul_le_mul_of_nonneg_right hC3 (norm_nonneg _))⟩

end OQ14.Packet05UniformCompactGreen
#print axioms OQ14.Packet05UniformCompactGreen.test_bounds
#print axioms OQ14.Packet05UniformCompactGreen.uniform_compact_green
