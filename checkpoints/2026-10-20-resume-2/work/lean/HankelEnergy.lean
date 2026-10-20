import RadialRellich
import RadialGreen

/-! # Actual all-degree outgoing radial energy and low-order bounds

The energy identity uses the explicit finite Riccati--Hankel functions.
Its normalization at infinity comes from their actual inverse polynomial.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.HankelEnergy

open Complex Filter Set OQ14.ModalAlgebra OQ14.ModalWronskian
open scoped Topology ComplexConjugate

def angular (l : ℕ) : ℝ := (l : ℝ)*(l+1)
def weight (l : ℕ) (r : ℝ) : ℝ := 1-angular l/r^2
def energy (l : ℕ) (r : ℝ) : ℝ :=
  Complex.normSq (xiD l r)+weight l r*Complex.normSq (xi l r)

theorem weight_hasDerivAt (l : ℕ) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (weight l) (2*angular l/r^3) r := by
  have h := ((hasDerivAt_const r (angular l)).div
    ((hasDerivAt_id r).pow 2) (pow_ne_zero 2 hr)).const_sub 1
  convert h using 1
  dsimp only [weight]
  field_simp
  ring

theorem energy_hasDerivAt (l : ℕ) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (energy l) (2*angular l/r^3*Complex.normSq (xi l r)) r := by
  have hx := (xi_hasDerivAt l (r : ℂ) (ofReal_ne_zero.mpr hr)).comp_ofReal
  have hd := (xiD_hasDerivAt l (r : ℂ) (ofReal_ne_zero.mpr hr)).comp_ofReal
  have he : (l : ℂ)*(l+1)/(r : ℂ)^2-1 = -(weight l r : ℂ) := by
    simp only [weight,angular,ofReal_sub,ofReal_div,ofReal_pow,ofReal_mul,
      ofReal_natCast,ofReal_add,ofReal_one]
    ring
  rw [he] at hd
  have h := (RadialGreen.normSq_hasDerivAt hd).add
    ((weight_hasDerivAt l r hr).mul (RadialGreen.normSq_hasDerivAt hx))
  convert h using 1
  simp only [RadialGreen.radialLoad_components, Complex.mul_re, Complex.mul_im,
    Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,neg_zero,
    zero_mul,sub_zero,add_zero]
  ring

theorem inverse_real_tendsto :
    Tendsto (fun r : ℝ => (r : ℂ)⁻¹) atTop (𝓝 0) := by
  simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero] using
    (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp
      (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0))

theorem hankelPolyD_tendsto (l : ℕ) (phase : ℂ) :
    Tendsto (fun r : ℝ => hankelPolyD l phase r) atTop (𝓝 0) := by
  have hp := (inversePolyD_differentiable l phase).continuous.continuousAt.tendsto.comp
    inverse_real_tendsto
  have h := (inverse_real_tendsto.pow 2).neg.mul hp
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0),neg_zero,zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  dsimp only [Function.comp_def]
  rw [← inversePolyD_eq l phase ((r : ℂ)⁻¹) (inv_ne_zero (ofReal_ne_zero.mpr hr.ne')),
    inv_inv]

theorem xi_normSq_eq (l : ℕ) (r : ℝ) :
    Complex.normSq (xi l r) = Complex.normSq (p l r) := by
  simp [xi,map_mul,map_pow,Complex.normSq_eq_norm_sq,Complex.norm_exp]

theorem xiD_normSq_eq (l : ℕ) (r : ℝ) :
    Complex.normSq (xiD l r) = Complex.normSq (I*p l r+pD l r) := by
  simp [xiD,map_mul,map_pow,Complex.normSq_eq_norm_sq,Complex.norm_exp]

theorem xi_normSq_tendsto (l : ℕ) :
    Tendsto (fun r : ℝ => Complex.normSq (xi l r)) atTop (𝓝 1) := by
  have hp := RadialRellich.hankelPoly_radial_limit l 1 (by norm_num) I
  simp only [one_mul] at hp
  simpa only [xi_normSq_eq,Complex.normSq_one,p,Function.comp_def] using
    (Complex.continuous_normSq.tendsto (1 : ℂ)).comp hp

theorem xiD_normSq_tendsto (l : ℕ) :
    Tendsto (fun r : ℝ => Complex.normSq (xiD l r)) atTop (𝓝 1) := by
  have hp := RadialRellich.hankelPoly_radial_limit l 1 (by norm_num) I
  simp only [one_mul] at hp
  have hd := (hp.const_mul I).add (hankelPolyD_tendsto l I)
  simp only [mul_one,add_zero] at hd
  simpa only [xiD_normSq_eq,Complex.normSq_I,p,pD,Function.comp_def] using
    (Complex.continuous_normSq.tendsto I).comp hd

theorem weight_tendsto (l : ℕ) : Tendsto (weight l) atTop (𝓝 1) := by
  have h := (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).pow 2
  have hc := (h.const_mul (angular l)).const_sub 1
  simpa [weight,div_eq_mul_inv,inv_pow] using hc

theorem energy_tendsto (l : ℕ) : Tendsto (energy l) atTop (𝓝 2) := by
  simpa only [energy,mul_one,one_add_one_eq_two] using
    (xiD_normSq_tendsto l).add ((weight_tendsto l).mul (xi_normSq_tendsto l))

theorem energy_monotone (l : ℕ) : MonotoneOn (energy l) (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro r hr
    exact (energy_hasDerivAt l r (ne_of_gt hr)).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioi] at hr
    exact (energy_hasDerivAt l r (ne_of_gt hr)).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Ioi] at hr
    rw [(energy_hasDerivAt l r (ne_of_gt hr)).deriv]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (Nat.cast_nonneg l) (by positivity))) (le_of_lt (pow_pos hr 3)))
      (Complex.normSq_nonneg _)

theorem energy_le_two (l : ℕ) (r : ℝ) (hr : 0 < r) : energy l r ≤ 2 := by
  apply ge_of_tendsto (energy_tendsto l)
  filter_upwards [eventually_ge_atTop r] with s hs
  exact energy_monotone l hr (lt_of_lt_of_le hr hs) hs

theorem low_range_weight (l : ℕ) (c R r : ℝ) (hR : 0 < R) (hRr : R ≤ r)
    (hl : angular l ≤ c^2*R^2) : 1-c^2 ≤ weight l r := by
  have hr : 0 < r := lt_of_lt_of_le hR hRr
  have hs : R^2 ≤ r^2 := sq_le_sq₀ hR.le hr.le |>.mpr hRr
  have hbound : angular l ≤ c^2*r^2 := hl.trans (mul_le_mul_of_nonneg_left hs (sq_nonneg c))
  have hd : angular l/r^2 ≤ c^2 := (div_le_iff₀ (sq_pos_of_pos hr)).mpr hbound
  dsimp only [weight]
  linarith

theorem low_range_normSq_bounds (l : ℕ) (c R r : ℝ)
    (hc : c^2 < 1) (hR : 0 < R) (hRr : R ≤ r)
    (hl : angular l ≤ c^2*R^2) :
    Complex.normSq (xiD l r) ≤ 2 ∧ Complex.normSq (xi l r) ≤ 2/(1-c^2) := by
  have hw := low_range_weight l c R r hR hRr hl
  have hwpos : 0 ≤ weight l r := le_trans (by linarith) hw
  have he := energy_le_two l r (lt_of_lt_of_le hR hRr)
  have hx := Complex.normSq_nonneg (xi l r)
  have hdx := Complex.normSq_nonneg (xiD l r)
  change Complex.normSq (xiD l r)+weight l r*Complex.normSq (xi l r) ≤ 2 at he
  constructor
  · nlinarith [mul_nonneg hwpos hx]
  · apply (le_div_iff₀ (by linarith : 0 < 1-c^2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hw hx]

end OQ14.HankelEnergy

#print axioms OQ14.HankelEnergy.weight_hasDerivAt
#print axioms OQ14.HankelEnergy.energy_hasDerivAt
#print axioms OQ14.HankelEnergy.inverse_real_tendsto
#print axioms OQ14.HankelEnergy.hankelPolyD_tendsto
#print axioms OQ14.HankelEnergy.xi_normSq_eq
#print axioms OQ14.HankelEnergy.xiD_normSq_eq
#print axioms OQ14.HankelEnergy.xi_normSq_tendsto
#print axioms OQ14.HankelEnergy.xiD_normSq_tendsto
#print axioms OQ14.HankelEnergy.weight_tendsto
#print axioms OQ14.HankelEnergy.energy_tendsto
#print axioms OQ14.HankelEnergy.energy_monotone
#print axioms OQ14.HankelEnergy.energy_le_two
#print axioms OQ14.HankelEnergy.low_range_weight
#print axioms OQ14.HankelEnergy.low_range_normSq_bounds
