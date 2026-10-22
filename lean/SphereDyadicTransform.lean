import SphereWaveCalculus
import KernelGradient

/-! Identification of the actual sphere-integral transverse tensor with genuine dyadic kernels. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SphereDyadicTransform
open MeasureTheory Metric Set SphereReactionKernel SphereWaveCalculus SphereWaveTransform
open Maxwell (dcoord basis partial_const_mul partial_sub)
open scoped InnerProductSpace Topology

theorem scalar_partial (k : ℝ) (x : Space) (i : Fin 3) :
    dcoord (scalar k) x i = (Complex.I*(k : ℂ))*moment (coordinate i) k x := by
  have he : moment (fun _ => 1) k = scalar k := by
    funext y
    simp only [moment, scalar, one_mul]
  have hh := moment_partial (fun _ => 1) continuous_const 1 (fun _ => by norm_num) k x i
  rw [he] at hh
  simpa only [moment, one_mul, coordinate] using hh
theorem scalar_second_partial (k : ℝ) (x : Space) (i j : Fin 3) :
    dcoord (fun y => dcoord (scalar k) y j) x i =
      -(k : ℂ)^2*moment (fun θ => coordinate i θ*coordinate j θ) k x := by
  have he : (fun y => dcoord (scalar k) y j) =
      (fun y => (Complex.I*(k : ℂ))*moment (coordinate j) k y) := funext (fun y => scalar_partial k y j)
  rw [he, partial_const_mul (moment_hasFDerivAt (coordinate j) (coordinate_continuous j) 1
    (coordinate_bound j) k x).differentiableAt]
  rw [moment_partial (coordinate j) (coordinate_continuous j) 1 (coordinate_bound j)]
  have hw : (fun θ : Sphere => coordinate j θ*(θ.val i : ℂ)) =
      (fun θ => coordinate i θ*coordinate j θ) := by funext θ; unfold coordinate; ring
  rw [hw]
  ring_nf
  simp [Complex.I_sq]

theorem J_moment (k : ℝ) (x : Space) (i j : Fin 3) : J k x i j =
    ((k^3/(16*Real.pi^2) : ℝ) : ℂ)*
      ((if i=j then 1 else 0 : ℂ)*scalar k x-
        moment (fun θ => coordinate i θ*coordinate j θ) k x) := by
  have hi : Integrable (fun θ : Sphere => (coordinate i θ*coordinate j θ)*wave k x θ) surface :=
    moment_integrable _ ((coordinate_continuous i).mul (coordinate_continuous j)) 1
      (fun θ => (norm_mul _ _).trans_le
        ((mul_le_mul (coordinate_bound i θ) (coordinate_bound j θ) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by norm_num))) k x
  unfold J
  congr 1
  unfold scalar moment
  rw [← integral_const_mul, ← integral_sub ((wave_integrable k x).const_mul _) hi]
  apply integral_congr_ae
  filter_upwards with θ
  unfold amplitude coordinate
  ring

theorem scalar_partial_phi (k : ℝ) (x : Space) (hk : k ≠ 0) (hx : x ≠ 0) (i : Fin 3) :
    dcoord (scalar k) x i = ((8*Real.pi^2 : ℝ) : ℂ)/(Complex.I*(k : ℂ))*
      (GreenKernel.phiGradient k x i-GreenKernel.phiGradient (-k) x i) := by
  have he : scalar k =ᶠ[nhds x] (fun y => ((8*Real.pi^2 : ℝ) : ℂ)/(Complex.I*(k : ℂ))*
      (GreenKernel.phi k y-GreenKernel.phi (-k) y)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact scalar_phi k y hk hy
  change fderiv ℝ (scalar k) x (basis i) = _
  rw [he.fderiv_eq]
  change dcoord (fun y => ((8*Real.pi^2 : ℝ) : ℂ)/(Complex.I*(k : ℂ))*
    (GreenKernel.phi k y-GreenKernel.phi (-k) y)) x i = _
  have hf := (GreenKernel.phi_contDiffAt k x hx).differentiableAt (by simp)
  have hg := (GreenKernel.phi_contDiffAt (-k) x hx).differentiableAt (by simp)
  rw [partial_const_mul (hf.sub hg), partial_sub hf hg, GreenKernel.phi_partial k x hx,
    GreenKernel.phi_partial (-k) x hx]

theorem scalar_second_phi (k : ℝ) (x : Space) (hk : k ≠ 0) (hx : x ≠ 0) (i j : Fin 3) :
    dcoord (fun y => dcoord (scalar k) y j) x i = ((8*Real.pi^2 : ℝ) : ℂ)/(Complex.I*(k : ℂ))*
      (GreenKernel.phiHessian k x i j-GreenKernel.phiHessian (-k) x i j) := by
  have he : (fun y => dcoord (scalar k) y j) =ᶠ[nhds x]
      (fun y => ((8*Real.pi^2 : ℝ) : ℂ)/(Complex.I*(k : ℂ))*
        (GreenKernel.phiGradient k y j-GreenKernel.phiGradient (-k) y j)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact scalar_partial_phi k y hk hy j
  change fderiv ℝ (fun y => dcoord (scalar k) y j) x (basis i) = _
  rw [he.fderiv_eq]
  change dcoord (fun y => ((8*Real.pi^2 : ℝ) : ℂ)/(Complex.I*(k : ℂ))*
    (GreenKernel.phiGradient k y j-GreenKernel.phiGradient (-k) y j)) x i = _
  have hf := KernelGradient.gradient_differentiableAt k j x hx
  have hg := KernelGradient.gradient_differentiableAt (-k) j x hx
  rw [partial_const_mul (hf.sub hg), partial_sub hf hg, GreenKernel.phiGradient_partial k x hx,
    GreenKernel.phiGradient_partial (-k) x hx]

theorem J_dyadic (k : ℝ) (x : Space) (hk : k ≠ 0) (hx : x ≠ 0) (i j : Fin 3) :
    J k x i j = (DyadicKernel.dyadic k x i j-DyadicKernel.dyadic (-k) x i j)/(2*Complex.I) := by
  have hs := scalar_second_partial k x i j
  rw [scalar_second_phi k x hk hx i j] at hs
  rw [J_moment, scalar_phi k x hk hx]
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hm : moment (fun θ => coordinate i θ*coordinate j θ) k x =
      -(((8*Real.pi^2 : ℝ) : ℂ)/(Complex.I*(k : ℂ))*
        (GreenKernel.phiHessian k x i j-GreenKernel.phiHessian (-k) x i j))/(k : ℂ)^2 := by
    apply (eq_div_iff (pow_ne_zero 2 hkc)).mpr
    linear_combination hs
  rw [hm]
  unfold DyadicKernel.dyadic
  push_cast
  split_ifs <;> field_simp [hkc, hp, Complex.I_ne_zero]
  all_goals ring_nf
  all_goals field_simp [hkc, hp, Complex.I_ne_zero]
  all_goals ring

end OQ14.SphereDyadicTransform
#print axioms OQ14.SphereDyadicTransform.scalar_partial
#print axioms OQ14.SphereDyadicTransform.scalar_second_partial
#print axioms OQ14.SphereDyadicTransform.J_moment
#print axioms OQ14.SphereDyadicTransform.scalar_partial_phi
#print axioms OQ14.SphereDyadicTransform.scalar_second_phi
#print axioms OQ14.SphereDyadicTransform.J_dyadic
