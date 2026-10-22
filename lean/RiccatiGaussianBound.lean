import RiccatiBarrierNormalization
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-! # The actual Gaussian lower bound for the regular Riccati solution -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RiccatiGaussianBound

open Filter Set Metric OQ14.RiccatiBarrier OQ14.RiccatiLogDerivative
open OQ14.RiccatiBarrierNormalization OQ14.RiccatiSeriesCoefficients OQ14.HankelRealBasis
open OQ14.RiccatiOriginLimits
open scoped Topology

def deficit (l : ℕ) (β x : ℝ) : ℝ :=
  x^((l : ℝ)+β)*((l+1)-y l x-x^2/((l : ℝ)+β+2))

theorem deficit_zero (l : ℕ) (β : ℝ) : deficit l β 0 = 0 := by simp [deficit,y_zero]

theorem deficit_continuousOn (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (β : ℝ) (hβ : 1 ≤ β) : ContinuousOn (deficit l β) (Icc 0 R) := by
  exact (Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ l+β)).continuousOn.mul
    ((continuousOn_const.sub (y_continuousOn l R hR hbarrier)).sub
      ((continuous_id.pow 2).div_const ((l : ℝ)+β+2)).continuousOn)

theorem deficit_hasDerivAt (l : ℕ) (β x : ℝ) (hx : x ≠ 0) (hu : u l x ≠ 0)
    (hd : (l : ℝ)+β+2 ≠ 0) :
    HasDerivAt (deficit l β)
      ((x^((l : ℝ)+β)/x)*(β-y l x)*((l+1)-y l x)) x := by
  have h := (Real.hasDerivAt_rpow_const (x := x) (p := (l : ℝ)+β) (Or.inl hx)).mul
    (((hasDerivAt_const x (l+1 : ℝ)).sub (y_hasDerivAt l x hx hu)).sub
      (((hasDerivAt_id x).pow 2).div_const ((l : ℝ)+β+2)))
  convert h using 1
  dsimp only [id_eq]
  rw [Real.rpow_sub_one hx ((l : ℝ)+β)]
  unfold ν
  field_simp [hx,hd]
  ring

theorem deficit_nonpositive (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (x : ℝ) (hx : x ∈ Ioc 0 R) : deficit l (gamma l R) x ≤ 0 := by
  have hγ := gamma_ge_one l R hbarrier
  have hd : (l : ℝ)+gamma l R+2 ≠ 0 := by positivity
  have hm : AntitoneOn (deficit l (gamma l R)) (Icc 0 R) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 R)
      (deficit_continuousOn l R hR hbarrier (gamma l R) hγ)
    · intro t ht
      rw [interior_Icc] at ht
      have hu : 0 < u l t := by
        rw [u_eq_regular l t ht.1.ne']
        exact (barrier_positive l R hR hbarrier t ⟨ht.1,ht.2.le⟩).1
      exact (deficit_hasDerivAt l (gamma l R) t ht.1.ne' hu.ne' hd).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hu : 0 < u l t := by
        rw [u_eq_regular l t ht.1.ne']
        exact (barrier_positive l R hR hbarrier t ⟨ht.1,ht.2.le⟩).1
      rw [(deficit_hasDerivAt l (gamma l R) t ht.1.ne' hu.ne' hd).deriv]
      have hy := y_barrier_bounds l R hR hbarrier t ⟨ht.1,ht.2.le⟩
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (div_nonneg (Real.rpow_nonneg ht.1.le _) ht.1.le)
          (sub_nonpos.mpr hy.1)) (sub_nonneg.mpr hy.2)
  have h := hm ⟨le_rfl,hR.le⟩ ⟨hx.1.le,hx.2⟩ hx.1.le
  rwa [deficit_zero] at h

theorem deficit_bound (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (x : ℝ) (hx : x ∈ Ioc 0 R) : (l+1)-y l x ≤ x^2/((l : ℝ)+gamma l R+2) := by
  have h := deficit_nonpositive l R hR hbarrier x hx
  have hw : 0 < x^((l : ℝ)+gamma l R) := Real.rpow_pos_of_pos hx.1 _
  have hi : (l+1)-y l x-x^2/((l : ℝ)+gamma l R+2) ≤ 0 := nonpos_of_mul_nonpos_right h hw
  linarith

def compensated (l : ℕ) (R x : ℝ) : ℝ :=
  Real.exp (x^2/(2*((l : ℝ)+gamma l R+2)))*v l x

theorem compensated_continuous (l : ℕ) (R : ℝ) : Continuous (compensated l R) :=
  (Real.continuous_exp.comp ((continuous_id.pow 2).div_const
    (2*((l : ℝ)+gamma l R+2)))).mul (v_continuous l)

theorem compensated_zero (l : ℕ) (R : ℝ) : compensated l R 0 = amplitude l 0 := by
  simp [compensated,v_zero]

theorem compensated_hasDerivAt (l : ℕ) (R x : ℝ) (hx : x ≠ 0) (hu : u l x ≠ 0)
    (hd : (l : ℝ)+gamma l R+2 ≠ 0) :
    HasDerivAt (compensated l R)
      (Real.exp (x^2/(2*((l : ℝ)+gamma l R+2)))*v l x*
        (x/((l : ℝ)+gamma l R+2)+(y l x-(l+1))/x)) x := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (t^2/(2*((l : ℝ)+gamma l R+2))))
      (Real.exp (x^2/(2*((l : ℝ)+gamma l R+2)))*(x/((l : ℝ)+gamma l R+2))) x := by
    convert (((hasDerivAt_id x).pow 2).div_const (2*((l : ℝ)+gamma l R+2))).exp using 1
    dsimp only [id_eq]
    field_simp [hd]
    ring
  convert he.mul (v_log_hasDerivAt l x hx hu) using 1
  ring

theorem compensated_monotoneOn (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l) :
    MonotoneOn (compensated l R) (Icc 0 R) := by
  have hγ := gamma_ge_one l R hbarrier
  have hd : (l : ℝ)+gamma l R+2 ≠ 0 := by positivity
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 R) (compensated_continuous l R).continuousOn
  · intro t ht
    rw [interior_Icc] at ht
    have hu : 0 < u l t := by
      rw [u_eq_regular l t ht.1.ne']
      exact (barrier_positive l R hR hbarrier t ⟨ht.1,ht.2.le⟩).1
    exact (compensated_hasDerivAt l R t ht.1.ne' hu.ne' hd).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have hu : 0 < u l t := by
      rw [u_eq_regular l t ht.1.ne']
      exact (barrier_positive l R hR hbarrier t ⟨ht.1,ht.2.le⟩).1
    rw [(compensated_hasDerivAt l R t ht.1.ne' hu.ne' hd).deriv]
    have hdef := deficit_bound l R hR hbarrier t ⟨ht.1,ht.2.le⟩
    have he : t/((l : ℝ)+gamma l R+2)+(y l t-(l+1))/t =
        (t^2/((l : ℝ)+gamma l R+2)+y l t-(l+1))/t := by
      field_simp [ht.1.ne']
      ring
    rw [he]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (v_positive l R hR hbarrier t ⟨ht.1.le,ht.2.le⟩).le)
      (div_nonneg (by linarith) ht.1.le)

theorem normalized_gaussian_lower (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (x : ℝ) (hx : x ∈ Ioc 0 R) :
    amplitude l 0*Real.exp (-x^2/(2*((l : ℝ)+gamma l R+2))) ≤ v l x := by
  have h := compensated_monotoneOn l R hR hbarrier ⟨le_rfl,hR.le⟩ ⟨hx.1.le,hx.2⟩ hx.1.le
  rw [compensated_zero] at h
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-x^2/(2*((l : ℝ)+gamma l R+2)))).le
  have he : Real.exp (-x^2/(2*((l : ℝ)+gamma l R+2)))*
      Real.exp (x^2/(2*((l : ℝ)+gamma l R+2))) = 1 := by
    rw [← Real.exp_add]
    have hh : -x^2/(2*((l : ℝ)+gamma l R+2))+x^2/(2*((l : ℝ)+gamma l R+2)) = 0 := by ring
    rw [hh,Real.exp_zero]
  dsimp only [compensated] at hm
  rw [← mul_assoc,he,one_mul] at hm
  simpa only [mul_comm] using hm

theorem regular_gaussian_lower (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (x : ℝ) (hx : x ∈ Ioc 0 R) :
    amplitude l 0*x^(l+1)*Real.exp (-x^2/(2*((l : ℝ)+gamma l R+2))) ≤ regular l x := by
  have h := mul_le_mul_of_nonneg_left (normalized_gaussian_lower l R hR hbarrier x hx)
    (pow_nonneg hx.1.le (l+1))
  have he : x^(l+1)*v l x = regular l x := (regular_factor l x hx.1.ne').symm
  rw [he] at h
  convert h using 1
  ring

theorem normalized_upper (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (x : ℝ) (hx : x ∈ Ioc 0 R) : v l x ≤ amplitude l 0 := by
  have hm : AntitoneOn (v l) (Icc 0 R) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 R) (v_continuous l).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      have hu : 0 < u l t := by
        rw [u_eq_regular l t ht.1.ne']
        exact (barrier_positive l R hR hbarrier t ⟨ht.1,ht.2.le⟩).1
      exact (v_log_hasDerivAt l t ht.1.ne' hu.ne').differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hu : 0 < u l t := by
        rw [u_eq_regular l t ht.1.ne']
        exact (barrier_positive l R hR hbarrier t ⟨ht.1,ht.2.le⟩).1
      rw [(v_log_hasDerivAt l t ht.1.ne' hu.ne').deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (v_positive l R hR hbarrier t ⟨ht.1.le,ht.2.le⟩).le
          (sub_nonpos.mpr (y_barrier_bounds l R hR hbarrier t ⟨ht.1,ht.2.le⟩).2)) ht.1.le
  have h := hm ⟨le_rfl,hR.le⟩ ⟨hx.1.le,hx.2⟩ hx.1.le
  rwa [v_zero] at h

theorem regular_upper (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (x : ℝ) (hx : x ∈ Ioc 0 R) : regular l x ≤ amplitude l 0*x^(l+1) := by
  have h := mul_le_mul_of_nonneg_left (normalized_upper l R hR hbarrier x hx)
    (pow_nonneg hx.1.le (l+1))
  have he : x^(l+1)*v l x = regular l x := (regular_factor l x hx.1.ne').symm
  rw [he] at h
  simpa only [mul_comm] using h

theorem amplitude_doubleFactorial (l : ℕ) :
    amplitude l 0 = 1/(Nat.doubleFactorial (2*l+1) : ℝ) := by
  have hdf : (Nat.doubleFactorial (2*l+1) : ℝ) ≠ 0 := by positivity
  unfold amplitude
  simp only [Nat.add_zero,Nat.factorial_zero,Nat.cast_one,one_mul]
  rw [Nat.factorial_eq_mul_doubleFactorial (2*l),Nat.doubleFactorial_two_mul]
  push_cast
  field_simp [hdf]
  ring

theorem barrier_amplitude_bounds (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (x : ℝ) (hx : x ∈ Ioc 0 R) :
    x^(l+1)/(Nat.doubleFactorial (2*l+1) : ℝ)*
        Real.exp (-x^2/(2*((l : ℝ)+gamma l R+2))) ≤ regular l x ∧
      regular l x ≤ x^(l+1)/(Nat.doubleFactorial (2*l+1) : ℝ) := by
  have hlo := regular_gaussian_lower l R hR hbarrier x hx
  have hhi := regular_upper l R hR hbarrier x hx
  rw [amplitude_doubleFactorial] at hlo hhi
  constructor
  · convert hlo using 1
    ring
  · convert hhi using 1
    ring

end OQ14.RiccatiGaussianBound

#print axioms OQ14.RiccatiGaussianBound.deficit_zero
#print axioms OQ14.RiccatiGaussianBound.deficit_continuousOn
#print axioms OQ14.RiccatiGaussianBound.deficit_hasDerivAt
#print axioms OQ14.RiccatiGaussianBound.deficit_nonpositive
#print axioms OQ14.RiccatiGaussianBound.deficit_bound
#print axioms OQ14.RiccatiGaussianBound.compensated_continuous
#print axioms OQ14.RiccatiGaussianBound.compensated_zero
#print axioms OQ14.RiccatiGaussianBound.compensated_hasDerivAt
#print axioms OQ14.RiccatiGaussianBound.compensated_monotoneOn
#print axioms OQ14.RiccatiGaussianBound.normalized_gaussian_lower
#print axioms OQ14.RiccatiGaussianBound.regular_gaussian_lower
#print axioms OQ14.RiccatiGaussianBound.normalized_upper
#print axioms OQ14.RiccatiGaussianBound.regular_upper
#print axioms OQ14.RiccatiGaussianBound.amplitude_doubleFactorial
#print axioms OQ14.RiccatiGaussianBound.barrier_amplitude_bounds
