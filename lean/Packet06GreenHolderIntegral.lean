import Packet06GreenHolderSourceMass
import Packet06GreenHolderSourceRows
import L2Parametric
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06GreenHolderIntegral
open MeasureTheory Metric Set OQ14.Maxwell OQ14.Packet06GreenHolderSourceMass
open OQ14.Packet06GreenHolderKernel OQ14.Packet06GreenHolderTranslatedMass

def V : ℝ := 3 * (volume : Measure Space).real (ball 0 1)
def K : ℝ := (4*Real.pi)⁻¹
def E (Z T : ℝ) : ℝ := Real.exp (Z*T)
def L (Z T : ℝ) : ℝ := E Z T * Real.exp (2*(Z*T)) * Z

theorem kernel_squared_integral (z : ℂ) (Z R S : ℝ) (hZ : ‖z‖ ≤ Z)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (x x' : Space) (hx : ‖x‖ ≤ R) (hx' : ‖x'‖ ≤ R)
    (hsmall : ‖x-x'‖ ≤ 1) (hpositive : 0 < ‖x-x'‖) :
    (∫ y : Space in closedBall 0 S,
      ‖ComplexGreenKernel.phi z (x-y) - ComplexGreenKernel.phi z (x'-y)‖^2) ≤
      (2*K^2 * (L Z (R+S)^2 * V * (R+S+1) + E Z (R+S)^2 * (14*V))) * ‖x-x'‖ := by
  let h := ‖x-x'‖
  let A : Set Space := closedBall 0 S
  let q : Space → ℝ := fun y => (‖x-y‖⁻¹)^2
  let d : Space → ℝ := fun y => |‖x-y‖⁻¹ - ‖x'-y‖⁻¹|^2
  let f : Space → ℝ := fun y => ‖ComplexGreenKernel.phi z (x-y) - ComplexGreenKernel.phi z (x'-y)‖^2
  let m : Space → ℝ := fun y => 2*K^2 * (L Z (R+S)^2*h^2*q y + E Z (R+S)^2*d y)
  have hZ0 : 0 ≤ Z := (norm_nonneg z).trans hZ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : 0 ≤ L Z (R+S) := by dsimp [L,E]; positivity
  have hE : 0 ≤ E Z (R+S) := (Real.exp_pos _).le
  have hA : MeasurableSet A := measurableSet_closedBall
  have hqB : IntegrableOn q {y | ‖x-y‖ ≤ R+S+1} :=
    inverse_sq_translated_ball_integrable x (R+S+1) (by linarith)
  have hq : IntegrableOn q A := by
    apply hqB.mono_set
    intro y hy
    change y ∈ closedBall (0 : Space) S at hy
    have hy' : ‖y‖ ≤ S := by simpa only [mem_closedBall,dist_zero_right] using hy
    change ‖x-y‖ ≤ R+S+1
    have hh := norm_sub_le x y
    linarith
  have hd : IntegrableOn d A := (coulomb_global_integrable x x' h hpositive rfl).integrableOn
  have hm : IntegrableOn m A := ((hq.const_mul (L Z (R+S)^2*h^2)).add
    (hd.const_mul (E Z (R+S)^2))).const_mul (2*K^2)
  have hfm : AEStronglyMeasurable f (volume.restrict A) := by
    apply Measurable.aestronglyMeasurable
    dsimp [f]
    exact (((OQ14.Packet06ComplexScalarKernel.phi_measurable z).comp
      (continuous_const.sub continuous_id).measurable).sub
      ((OQ14.Packet06ComplexScalarKernel.phi_measurable z).comp
      (continuous_const.sub continuous_id).measurable)).norm.pow_const 2
  have hpoint : ∀ y ∈ A, f y ≤ m y := by
    intro y hy
    change y ∈ closedBall (0 : Space) S at hy
    have hy' : ‖y‖ ≤ S := by simpa only [mem_closedBall,dist_zero_right] using hy
    have hu : ‖x-y‖ ≤ R+S := (norm_sub_le x y).trans (add_le_add hx hy')
    have hv : ‖x'-y‖ ≤ R+S := (norm_sub_le x' y).trans (add_le_add hx' hy')
    have hxy : (x-y)-(x'-y) = x-x' := by abel
    have ht := phi_difference_bound z Z (R+S) hZ (x-y) (x'-y) hu hv
    rw [hxy] at ht
    have ht' : ‖ComplexGreenKernel.phi z (x-y) - ComplexGreenKernel.phi z (x'-y)‖ ≤
        K * (L Z (R+S)*h*‖x-y‖⁻¹ + E Z (R+S)*|‖x-y‖⁻¹ - ‖x'-y‖⁻¹|) := by
      simpa only [K,L,E,mul_assoc] using ht
    have ha : 0 ≤ L Z (R+S)*h*‖x-y‖⁻¹ := by positivity
    have hb : 0 ≤ E Z (R+S)*|‖x-y‖⁻¹ - ‖x'-y‖⁻¹| := by positivity
    let a : ℝ := L Z (R+S)*h*‖x-y‖⁻¹
    let b : ℝ := E Z (R+S)*|‖x-y‖⁻¹ - ‖x'-y‖⁻¹|
    let n : ℝ := ‖ComplexGreenKernel.phi z (x-y) - ComplexGreenKernel.phi z (x'-y)‖
    have hn : 0 ≤ n := norm_nonneg _
    have hab : (a+b)^2 ≤ 2*(a^2+b^2) := by nlinarith [sq_nonneg (a-b)]
    have hns : n^2 ≤ (K*(a+b))^2 :=
      (sq_le_sq₀ hn (mul_nonneg hK (add_nonneg ha hb))).2 ht'
    have hm' := mul_le_mul_of_nonneg_left hab (sq_nonneg K)
    dsimp [f,m,q,d,a,b,n] at *
    nlinarith
  have hf : IntegrableOn f A := by
    apply hm.mono' hfm
    filter_upwards [ae_restrict_mem hA] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint y hy
  have hi := integral_mono_ae hf hm (by filter_upwards [ae_restrict_mem hA] with y hy; exact hpoint y hy)
  have hqbound := inverse_sq_source_integral x R S hR hS hx
  have hdbound : (∫ y : Space in A, d y) ≤ 14*h*V := by
    have hh := setIntegral_le_integral (s := A) (coulomb_global_integrable x x' h hpositive rfl)
      (by filter_upwards with y; exact sq_nonneg _)
    exact hh.trans (coulomb_global_integral x x' h hpositive rfl)
  change (∫ y : Space in A, q y) ≤ V*(R+S+1) at hqbound
  dsimp only [m] at hi
  rw [integral_const_mul, integral_add (hq.const_mul _) (hd.const_mul _),
    integral_const_mul, integral_const_mul] at hi
  have hh2 : h^2 ≤ h := by dsimp [h]; nlinarith [norm_nonneg (x-x')]
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hbq : L Z (R+S)^2*h^2*(∫ y : Space in A, q y) ≤
      L Z (R+S)^2*h*V*(R+S+1) := by
    calc
      _ ≤ L Z (R+S)^2*h^2*(V*(R+S+1)) := by gcongr
      _ ≤ L Z (R+S)^2*h*(V*(R+S+1)) := by gcongr
      _ = _ := by ring
  have hbd : E Z (R+S)^2*(∫ y : Space in A, d y) ≤
      E Z (R+S)^2*(14*h*V) := by gcongr
  have hh := add_le_add hbq hbd
  have hh' := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2*K^2 by positivity)
  change (∫ y : Space in A, f y) ≤ _
  calc
    _ ≤ 2*K^2 * (L Z (R+S)^2*h^2*(∫ y : Space in A, q y) +
        E Z (R+S)^2*(∫ y : Space in A, d y)) := hi
    _ ≤ 2*K^2 * (L Z (R+S)^2*h*V*(R+S+1) +
        E Z (R+S)^2*(14*h*V)) := hh'
    _ = _ := by dsimp [h]; ring
#print axioms OQ14.Packet06GreenHolderIntegral.kernel_squared_integral
end OQ14.Packet06GreenHolderIntegral
