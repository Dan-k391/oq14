import SphereDyadicTransform
import HCurl

/-! Genuine magnetic sphere kernels and actual curl of the literal electric tensor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SphereMagneticKernel
open MeasureTheory Metric Set SphereReactionKernel SphereWaveCalculus SphereWaveTransform
open Maxwell (dcoord basis partial_const_mul curl pd)
open WeakCurl (next previous)
open scoped Topology

def transverse (i j : Fin 3) (θ : Sphere) : ℂ :=
  coordinate (next i) θ*(if previous i=j then 1 else 0)-
    coordinate (previous i) θ*(if next i=j then 1 else 0)

def K (k : ℝ) (x : Space) (i j : Fin 3) : ℂ :=
  ((k^3/(16*Real.pi^2) : ℝ) : ℂ)*moment (transverse i j) k x

private theorem amplitude_continuous (i j : Fin 3) : Continuous (fun θ : Sphere => amplitude θ i j) :=
  continuous_const.sub ((coordinate_continuous i).mul (coordinate_continuous j))

private theorem J_derivative (k : ℝ) (x : Space) (i j : Fin 3) :
    HasFDerivAt (fun y => J k y i j)
      (((k^3/(16*Real.pi^2) : ℝ) : ℂ) •
        (∫ θ : Sphere, (amplitude θ i j*wave k x θ) • phase k θ ∂surface)) x :=
  (moment_hasFDerivAt (fun θ => amplitude θ i j) (amplitude_continuous i j) 2
    (fun θ => amplitude_bound θ i j) k x).const_mul _

theorem J_partial (k : ℝ) (x : Space) (a i j : Fin 3) :
    dcoord (fun y => J k y i j) x a =
      ((k^3/(16*Real.pi^2) : ℝ) : ℂ)*(Complex.I*(k : ℂ))*
        moment (fun θ => amplitude θ i j*coordinate a θ) k x := by
  change dcoord (fun y => ((k^3/(16*Real.pi^2) : ℝ) : ℂ)*
    moment (fun θ => amplitude θ i j) k y) x a = _
  rw [partial_const_mul (moment_hasFDerivAt _ (amplitude_continuous i j) 2
    (fun θ => amplitude_bound θ i j) k x).differentiableAt,
    moment_partial _ (amplitude_continuous i j) 2 (fun θ => amplitude_bound θ i j)]
  simp only [coordinate, mul_assoc]

theorem transverse_continuous (i j : Fin 3) : Continuous (transverse i j) :=
  ((coordinate_continuous _).mul continuous_const).sub ((coordinate_continuous _).mul continuous_const)

theorem transverse_bound (i j : Fin 3) (θ : Sphere) : ‖transverse i j θ‖ ≤ 2 := by
  have hd (a b : Fin 3) : ‖(if a=b then 1 else 0 : ℂ)‖ ≤ 1 := by split_ifs <;> norm_num
  unfold transverse
  apply (norm_sub_le _ _).trans
  rw [norm_mul, norm_mul]
  exact (add_le_add
    (mul_le_mul (coordinate_bound _ θ) (hd _ _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
    (mul_le_mul (coordinate_bound _ θ) (hd _ _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))).trans_eq (by norm_num)

theorem curl_J (k : ℝ) (x : Space) (i j : Fin 3) :
    curl (fun y a => J k y a j) x i = (Complex.I*(k : ℂ))*K k x i j := by
  have he : curl (fun y a => J k y a j) x i =
      dcoord (fun y => J k y (previous i) j) x (next i)-
        dcoord (fun y => J k y (next i) j) x (previous i) := by fin_cases i <;> rfl
  rw [he, J_partial, J_partial]
  have hi (a b : Fin 3) : Integrable (fun θ : Sphere =>
      (amplitude θ a j*coordinate b θ)*wave k x θ) surface :=
    moment_integrable _ ((amplitude_continuous a j).mul (coordinate_continuous b)) 2
      (fun θ => by
        rw [norm_mul]
        exact (mul_le_mul (amplitude_bound θ a j) (coordinate_bound b θ) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num)) k x
  have hm : moment (fun θ => amplitude θ (previous i) j*coordinate (next i) θ) k x-
      moment (fun θ => amplitude θ (next i) j*coordinate (previous i) θ) k x =
        moment (transverse i j) k x := by
    unfold moment
    rw [← integral_sub (hi _ _) (hi _ _)]
    apply integral_congr_ae
    filter_upwards with θ
    unfold transverse amplitude coordinate
    ring
  unfold K
  calc
    _ = (Complex.I*(k : ℂ))*((k^3/(16*Real.pi^2) : ℝ) : ℂ)*
      (moment (fun θ => amplitude θ (previous i) j*coordinate (next i) θ) k x-
        moment (fun θ => amplitude θ (next i) j*coordinate (previous i) θ) k x) := by ring
    _ = _ := by rw [hm]; ring

theorem K_bound (k : ℝ) (x : Space) (i j : Fin 3) : ‖K k x i j‖ ≤ entryBound k := by
  have hi := norm_integral_le_of_norm_le_const (μ := surface)
    (Filter.Eventually.of_forall (fun θ : Sphere =>
      (show ‖transverse i j θ*wave k x θ‖ ≤ 2 by
        simpa only [norm_mul, wave_norm, mul_one] using transverse_bound i j θ)))
  unfold K moment entryBound surfaceMass
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)

theorem K_continuous (k : ℝ) (i j : Fin 3) : Continuous (fun x => K k x i j) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact continuousAt_const.mul
    (moment_hasFDerivAt _ (transverse_continuous i j) 2 (transverse_bound i j) k x).continuousAt

theorem K_moment (k : ℝ) (x : Space) (i j : Fin 3) : K k x i j =
    ((k^3/(16*Real.pi^2) : ℝ) : ℂ)*
      (moment (coordinate (next i)) k x*(if previous i=j then 1 else 0)-
        moment (coordinate (previous i)) k x*(if next i=j then 1 else 0)) := by
  have hi (a : Fin 3) := moment_integrable _ (coordinate_continuous a) 1 (coordinate_bound a) k x
  unfold K
  congr 1
  unfold moment transverse
  rw [← integral_mul_const, ← integral_mul_const,
    ← integral_sub ((hi (next i)).mul_const _) ((hi (previous i)).mul_const _)]
  apply integral_congr_ae
  filter_upwards with θ
  ring

def magneticDyadic (k : ℝ) (x : Space) (i j : Fin 3) : ℂ :=
  -(Complex.I*(k : ℂ))*
    (GreenKernel.phiGradient k x (next i)*(if previous i=j then 1 else 0)-
      GreenKernel.phiGradient k x (previous i)*(if next i=j then 1 else 0))

theorem K_magnetic (k : ℝ) (x : Space) (hk : k ≠ 0) (hx : x ≠ 0) (i j : Fin 3) :
    K k x i j = (magneticDyadic k x i j+magneticDyadic (-k) x i j)/(2*Complex.I) := by
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hkc
  have hm (a : Fin 3) : moment (coordinate a) k x =
      (((8*Real.pi^2 : ℝ) : ℂ)/(Complex.I*(k : ℂ))*
        (GreenKernel.phiGradient k x a-GreenKernel.phiGradient (-k) x a))/(Complex.I*(k : ℂ)) := by
    apply (eq_div_iff hI).mpr
    have hs := SphereDyadicTransform.scalar_partial k x a
    rw [SphereDyadicTransform.scalar_partial_phi k x hk hx a] at hs
    simpa only [mul_comm] using hs.symm
  rw [K_moment, hm, hm]
  unfold magneticDyadic
  push_cast
  split_ifs <;> field_simp [hkc, hp, Complex.I_ne_zero]
  all_goals ring_nf
  all_goals field_simp [hkc, hp, Complex.I_ne_zero]
  all_goals ring
end OQ14.SphereMagneticKernel
#print axioms OQ14.SphereMagneticKernel.J_partial
#print axioms OQ14.SphereMagneticKernel.transverse_continuous
#print axioms OQ14.SphereMagneticKernel.transverse_bound
#print axioms OQ14.SphereMagneticKernel.curl_J


#print axioms OQ14.SphereMagneticKernel.K_bound
#print axioms OQ14.SphereMagneticKernel.K_continuous
#print axioms OQ14.SphereMagneticKernel.K_moment
#print axioms OQ14.SphereMagneticKernel.K_magnetic
