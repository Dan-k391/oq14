import StaticPlaneSource

/-! Genuine whole-plane static field errors, including a gap proportional to radius. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.StaticPlaneError

open MeasureTheory Metric StaticPlaneKernel StaticPlaneSource PlaneInverseCube
open scoped Topology

theorem difference_gap (d : ℝ) (f g : Space → ℂ)
    (hf : ∀ᵐ y, f y ≠ 0 → d ≤ |y 2|) (hg : ∀ᵐ y, g y ≠ 0 → d ≤ |y 2|) :
    ∀ᵐ y, f y-g y ≠ 0 → d ≤ |y 2| := by
  filter_upwards [hf, hg] with y hy hz hsub
  by_cases hn : f y=0
  · apply hz
    intro hzero
    exact hsub (by rw [hn, hzero, sub_self])
  · exact hy hn

theorem field_sub_ae (d : ℝ) (hd : 0 < d) (f g : Space → ℂ)
    (hf : Integrable f) (hg : Integrable g)
    (hsf : ∀ᵐ y, f y ≠ 0 → d ≤ |y 2|) (hsg : ∀ᵐ y, g y ≠ 0 → d ≤ |y 2|)
    (i j : Fin 3) :
    field (fun y => f y-g y) i j =ᵐ[volume] fun q => field f i j q-field g i j q := by
  filter_upwards [(integrand_integrable d hd f hf hsf i j).prod_left_ae,
    (integrand_integrable d hd g hg hsg i j).prod_left_ae] with q hqf hqg
  unfold field
  dsimp only [integrand] at hqf hqg
  rw [← integral_sub hqf hqg]
  apply integral_congr_ae
  filter_upwards with y
  ring

theorem difference_integrable (d : ℝ) (hd : 0 < d) (f g : Space → ℂ)
    (hf : Integrable f) (hg : Integrable g)
    (hsf : ∀ᵐ y, f y ≠ 0 → d ≤ |y 2|) (hsg : ∀ᵐ y, g y ≠ 0 → d ≤ |y 2|)
    (i j : Fin 3) : Integrable (fun q => field f i j q-field g i j q) :=
  (field_integrable d hd (fun y => f y-g y) (hf.sub hg) (difference_gap d f g hsf hsg) i j).congr
    (field_sub_ae d hd f g hf hg hsf hsg i j)

theorem difference_mass (d : ℝ) (hd : 0 < d) (f g : Space → ℂ)
    (hf : Integrable f) (hg : Integrable g)
    (hsf : ∀ᵐ y, f y ≠ 0 → d ≤ |y 2|) (hsg : ∀ᵐ y, g y ≠ 0 → d ≤ |y 2|)
    (i j : Fin 3) :
    (∫ q : Plane, ‖field f i j q-field g i j q‖) ≤ (3/d)*(∫ y, ‖f y-g y‖) := by
  have he : (∫ q : Plane, ‖field f i j q-field g i j q‖) =
      ∫ q : Plane, ‖field (fun y => f y-g y) i j q‖ := by
    apply integral_congr_ae
    filter_upwards [field_sub_ae d hd f g hf hg hsf hsg i j] with q hq
    rw [hq]
  rw [he]
  exact field_mass d hd (fun y => f y-g y) (hf.sub hg) (difference_gap d f g hsf hsg) i j

theorem moving_gap_mass (γ a C : ℝ) (hγ : 0 < γ) (ha : 0 < a)
    (f g : Space → ℂ) (hf : Integrable f) (hg : Integrable g)
    (hsf : ∀ᵐ y, f y ≠ 0 → γ*a ≤ |y 2|) (hsg : ∀ᵐ y, g y ≠ 0 → γ*a ≤ |y 2|)
    (he : (∫ y, ‖f y-g y‖) ≤ C*a^3) (i j : Fin 3) :
    (∫ q : Plane, ‖field f i j q-field g i j q‖) ≤ (3*C/γ)*a^2 := by
  apply (difference_mass (γ*a) (mul_pos hγ ha) f g hf hg hsf hsg i j).trans
  apply (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 3/(γ*a))).trans_eq
  field_simp
  ring

end OQ14.StaticPlaneError

#print axioms OQ14.StaticPlaneError.difference_gap
#print axioms OQ14.StaticPlaneError.field_sub_ae
#print axioms OQ14.StaticPlaneError.difference_integrable
#print axioms OQ14.StaticPlaneError.difference_mass
#print axioms OQ14.StaticPlaneError.moving_gap_mass
