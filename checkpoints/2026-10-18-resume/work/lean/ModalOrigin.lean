import ModalInterface
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Removable center of the actual regular dipole

Repeated divided differences of the exponential construct the regular radial
profile without an assumed asymptotic expansion.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.ModalOrigin

open Complex Filter Asymptotics OQ14.Maxwell OQ14.GreenKernel
  OQ14.ModalAlgebra OQ14.ModalDipole OQ14.ModalInterface
open scoped Topology

def expTail (m : ℕ) : ℂ → ℂ := (Function.swap dslope (0 : ℂ))^[m] Complex.exp

theorem expTail_series (m : ℕ) :
    HasFPowerSeriesAt (expTail m)
      (FormalMultilinearSeries.fslope^[m] (NormedSpace.expSeries ℂ ℂ)) 0 := by
  apply HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.exp_hasFPowerSeriesAt_zero

theorem expTail_zero (m : ℕ) : expTail m 0 = (Nat.factorial m : ℂ)⁻¹ := by
  rw [← (expTail_series m).coeff_zero 1]
  change (FormalMultilinearSeries.fslope^[m] (NormedSpace.expSeries ℂ ℂ)).coeff 0 = _
  rw [FormalMultilinearSeries.coeff_iterate_fslope]
  simp only [zero_add, FormalMultilinearSeries.coeff]
  change NormedSpace.expSeries ℂ ℂ m (fun _ => 1) = _
  rw [NormedSpace.expSeries_apply_eq]
  simp

theorem expTail_differentiable (m : ℕ) : Differentiable ℂ (expTail m) := by
  induction m with
  | zero => exact Complex.differentiable_exp
  | succ m ih =>
    simp only [expTail, Function.iterate_succ_apply']
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr ih.differentiableOn

theorem expTail_step (m : ℕ) (z : ℂ) :
    z * expTail (m+1) z = expTail m z - (Nat.factorial m : ℂ)⁻¹ := by
  rw [expTail, Function.iterate_succ_apply']
  simpa [expTail_zero] using sub_smul_dslope (expTail m) 0 z

def profile (z : ℂ) : ℂ :=
  (expTail 2 (I*z) + expTail 2 (-I*z) -
    expTail 3 (I*z) - expTail 3 (-I*z)) / 2

theorem profile_differentiable : Differentiable ℂ profile := by
  unfold profile
  exact ((((expTail_differentiable 2).comp ((differentiable_const I).mul differentiable_id)).add
    ((expTail_differentiable 2).comp ((differentiable_const (-I)).mul differentiable_id))).sub
    ((expTail_differentiable 3).comp ((differentiable_const I).mul differentiable_id)) |>.sub
    ((expTail_differentiable 3).comp ((differentiable_const (-I)).mul differentiable_id))).div_const 2

theorem profile_zero : profile 0 = 1/3 := by
  norm_num [profile, expTail_zero, Nat.factorial]

theorem profile_hasDerivAt_zero : HasDerivAt profile 0 0 := by
  have hp (m : ℕ) := ((expTail_differentiable m (I*0)).hasDerivAt).comp 0
    ((hasDerivAt_id (0 : ℂ)).const_mul I)
  have hm (m : ℕ) := ((expTail_differentiable m (-I*0)).hasDerivAt).comp 0
    ((hasDerivAt_id (0 : ℂ)).const_mul (-I))
  convert (((hp 2).add (hm 2)).sub (hp 3) |>.sub (hm 3)).div_const 2 using 1
  simp only [mul_zero, mul_one]; ring

theorem expTail_two_identity (z : ℂ) :
    z^2 * expTail 2 z = exp z - 1 - z := by
  have h0 := expTail_step 0 z
  have h1 := expTail_step 1 z
  norm_num [expTail, Nat.factorial] at h0
  norm_num [Nat.factorial] at h1
  linear_combination z*h1+h0

theorem expTail_three_identity (z : ℂ) :
    z^3 * expTail 3 z = exp z - 1 - z - z^2/2 := by
  have h2 := expTail_step 2 z
  have h1 := expTail_two_identity z
  norm_num [Nat.factorial] at h2
  linear_combination z^2*h2+h1

theorem psi_profile (z : ℂ) (hz : z ≠ 0) : psi 1 z = z^2 * profile z := by
  have hp2 := expTail_two_identity (I*z)
  have hm2 := expTail_two_identity (-I*z)
  have hp3 := expTail_three_identity (I*z)
  have hm3 := expTail_three_identity (-I*z)
  unfold psi xi xiMinus profile
  rw [p_one, pMinus_one]
  norm_num
  apply (mul_left_cancel₀ hz)
  field_simp [hz]
  linear_combination -z/2*hp2-z/2*hm2-I/2*hp3+I/2*hm3

theorem psiD_profile (z : ℂ) (hz : z ≠ 0) :
    psiD 1 z = 2*z*profile z + z^2*deriv profile z := by
  have he : psi 1 =ᶠ[𝓝 z] fun w => w^2*profile w := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw using psi_profile w hw
  have hd := ((hasDerivAt_id z).pow 2).mul (profile_differentiable z).hasDerivAt
  simpa using (he.hasDerivAt_iff.mp (psi_hasDerivAt 1 z hz)).unique hd

end OQ14.ModalOrigin
