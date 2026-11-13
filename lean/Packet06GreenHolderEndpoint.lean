import Packet06GreenHolderIntegral
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06GreenHolderEndpoint
open MeasureTheory Metric Set OQ14.Maxwell OQ14.Packet06GreenHolderIntegral
open OQ14.Packet06GreenHolderSourceRows

def constant (Z R S : ℝ) : ℝ :=
  Real.sqrt (2*K^2 * (L Z (R+S)^2 * V * (R+S+1) + E Z (R+S)^2 * (14*V)))

theorem sourceRow_difference_bound (z : ℂ) (Z R S : ℝ) (hZ : ‖z‖ ≤ Z)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (x x' : Space) (hx : ‖x‖ ≤ R) (hx' : ‖x'‖ ≤ R)
    (hsmall : ‖x-x'‖ ≤ 1) :
    dist (sourceRow z R S x) (sourceRow z R S x') ≤ constant Z R S * Real.sqrt (dist x x') := by
  by_cases heq : x=x'
  · subst x'
    simp [constant]
  have hp : 0 < ‖x-x'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
  have hxmem : x ∈ closedBall (0 : Space) R := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hx'mem : x' ∈ closedBall (0 : Space) R := by simpa only [mem_closedBall,dist_zero_right] using hx'
  have hi := kernel_squared_integral z Z R S hZ hR hS x x' hx hx' hsmall hp
  have hn : ‖sourceRow z R S x - sourceRow z R S x'‖^2 =
      ∫ y : Space in closedBall 0 S,
        ‖ComplexGreenKernel.phi z (x-y) - ComplexGreenKernel.phi z (x'-y)‖^2 := by
    rw [L2Parametric.norm_sq_integral, ← integral_indicator measurableSet_closedBall]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (sourceRow z R S x) (sourceRow z R S x'),
      sourceRow_actual_ae z R S x hxmem, sourceRow_actual_ae z R S x' hx'mem] with y hs ha hb
    rw [hs]
    simp only [Pi.sub_apply, ha, hb]
    by_cases hy : y ∈ closedBall (0 : Space) S
    · simp [hy]
    · simp [hy]
  have hc : 0 ≤ 2*K^2 * (L Z (R+S)^2 * V * (R+S+1) + E Z (R+S)^2 * (14*V)) := by
    have hv : 0 ≤ V := by dsimp [V]; positivity
    positivity
  have hs : ‖sourceRow z R S x - sourceRow z R S x'‖^2 ≤
      (constant Z R S * Real.sqrt ‖x-x'‖)^2 := by
    rw [hn]
    rw [mul_pow]
    dsimp only [constant]
    rw [Real.sq_sqrt hc, Real.sq_sqrt (norm_nonneg _)]
    exact hi
  rw [dist_eq_norm, dist_eq_norm]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1 hs

/-- Uniform one-half-Hölder bound for the literal compact-source Helmholtz response,
including its actual z² prefactor. The constant depends only on Z, the common
source and observation radii, and the source L² norm. -/
theorem actual_response_holder (z : ℂ) (Z R S : ℝ) (hZ : ‖z‖ ≤ Z)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (ρ : Space → ℂ)
    (F : FourierL2.ScalarL2) (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0)
    (x x' : Space) (hx : ‖x‖ ≤ R) (hx' : ‖x'‖ ≤ R) (hsmall : ‖x-x'‖ ≤ 1) :
    dist (z^2 * KernelConvolution.response (ComplexGreenKernel.phi z) ρ x)
      (z^2 * KernelConvolution.response (ComplexGreenKernel.phi z) ρ x') ≤
      Z^2 * ‖F‖ * constant Z R S * Real.sqrt (dist x x') := by
  have hxmem : x ∈ closedBall (0 : Space) R := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hx'mem : x' ∈ closedBall (0 : Space) R := by simpa only [mem_closedBall,dist_zero_right] using hx'
  have h := response_difference_of_sourceRow_bound z R S ρ F hF hc x x' hxmem hx'mem
    (constant Z R S) (sourceRow_difference_bound z Z R S hZ hR hS x x' hx hx' hsmall)
  have hZ0 : 0 ≤ Z := (norm_nonneg z).trans hZ
  have hsq : ‖z‖^2 ≤ Z^2 := (sq_le_sq₀ (norm_nonneg z) hZ0).2 hZ
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (norm_nonneg F))
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
#print axioms OQ14.Packet06GreenHolderEndpoint.actual_response_holder
#print axioms OQ14.Packet06GreenHolderEndpoint.sourceRow_difference_bound
end OQ14.Packet06GreenHolderEndpoint
