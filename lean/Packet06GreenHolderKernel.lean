import Packet06GreenHolderNear
import Packet06GreenHolderExponential
import Packet06ComplexScalarKernel
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06GreenHolderKernel
open Metric OQ14.Maxwell OQ14.Packet06GreenHolderExponential

theorem phi_difference_bound (z : ℂ) (Z T : ℝ) (hZ : ‖z‖ ≤ Z)
    (u v : Space) (hu : ‖u‖ ≤ T) (hv : ‖v‖ ≤ T) :
    ‖ComplexGreenKernel.phi z u - ComplexGreenKernel.phi z v‖ ≤
      (4*Real.pi)⁻¹ *
        ((Real.exp (Z*T) * Real.exp (2*(Z*T))) * (Z*‖u-v‖) * ‖u‖⁻¹ +
          Real.exp (Z*T) * |‖u‖⁻¹ - ‖v‖⁻¹|) := by
  let a : ℂ := Complex.exp (Complex.I*z*(‖u‖ : ℂ))
  let b : ℂ := Complex.exp (Complex.I*z*(‖v‖ : ℂ))
  have huT : 0 ≤ T := (norm_nonneg u).trans hu
  have hZ0 : 0 ≤ Z := (norm_nonneg z).trans hZ
  have hE : ‖b‖ ≤ Real.exp (Z*T) := by
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    dsimp [b]
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg v)]
    exact mul_le_mul hZ hv (norm_nonneg _) hZ0
  have hd : ‖a-b‖ ≤ (Real.exp (Z*T) * Real.exp (2*(Z*T))) * (Z*‖u-v‖) :=
    radial_exp_difference z Z T hZ u v hu hv
  have hid : ComplexGreenKernel.phi z u - ComplexGreenKernel.phi z v =
      (((a-b) * (‖u‖ : ℂ)⁻¹ + b * ((‖u‖ : ℂ)⁻¹ - (‖v‖ : ℂ)⁻¹)) /
        (4*Real.pi : ℂ)) := by
    dsimp [ComplexGreenKernel.phi, ComplexGreenKernel.radial, a, b]
    ring
  rw [hid, norm_div]
  have hp : 0 < 4*Real.pi := by positivity
  have hn : ‖(4*Real.pi : ℂ)‖ = 4*Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [hn, div_eq_inv_mul]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hp))
  have ht := norm_add_le ((a-b) * (‖u‖ : ℂ)⁻¹)
    (b * ((‖u‖ : ℂ)⁻¹ - (‖v‖ : ℂ)⁻¹))
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg u), ← Complex.ofReal_inv, ← Complex.ofReal_sub] at ht
  simpa only [Complex.ofReal_inv, Complex.ofReal_sub] using ht.trans (add_le_add (mul_le_mul_of_nonneg_right hd (inv_nonneg.mpr (norm_nonneg u)))
    (mul_le_mul_of_nonneg_right hE (abs_nonneg _)))

#print axioms OQ14.Packet06GreenHolderKernel.phi_difference_bound
end OQ14.Packet06GreenHolderKernel
