import Packet06ActualAngularL2
import ComplexMagneticLocal
import ScalarPotentialBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ComplexScalarKernel
open MeasureTheory Metric Set OQ14.Maxwell OQ14.ComplexGreenKernel
open scoped Topology

theorem phi_measurable (z : ℂ) : Measurable (phi z) := by
  unfold phi radial
  fun_prop

theorem phi_bound_ball (z : ℂ) (R : ℝ) (x : Space) (hx : x ∈ closedBall 0 R) :
    ‖phi z x‖ ≤ Real.exp (‖z‖*R) * ‖GreenKernel.phi 0 x‖ := by
  have hr : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
  have he : ‖Complex.exp (Complex.I*z*‖x‖)‖ ≤ Real.exp (‖z‖*R) := by
    apply (ComplexDynamicKernel.exp_norm_bound _).trans
    apply Real.exp_le_exp.mpr
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_norm]
    exact mul_le_mul_of_nonneg_left hr (norm_nonneg z)
  unfold phi radial GreenKernel.phi GreenKernel.radial
  simp only [Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,one_div,
    norm_div,norm_mul,norm_one,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_norm,
    div_eq_mul_inv]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right he (inv_nonneg.mpr (norm_nonneg x)))
    (inv_nonneg.mpr (mul_nonneg (norm_nonneg (4:ℂ)) (abs_nonneg Real.pi)))
  simpa only [one_mul,mul_assoc] using hh

theorem phi_memLp_two_ball (z : ℂ) (R : ℝ) :
    MemLp (phi z) 2 (volume.restrict (closedBall 0 R)) := by
  apply (KernelIntegrability.phi_memLp_two_ball 0 R).of_le_mul
    ((phi_measurable z).aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  exact phi_bound_ball z R x hx

theorem phi_locallyIntegrable (z : ℂ) : LocallyIntegrable (phi z) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  have hi : IntegrableOn (phi z) (closedBall 0 (max R 0)) :=
    (phi_memLp_two_ball z (max R 0)).integrable (by norm_num)
  exact hi.mono_set (hR.trans (closedBall_subset_closedBall (le_max_left _ _)))
#print axioms OQ14.Packet06ComplexScalarKernel.phi_measurable
#print axioms OQ14.Packet06ComplexScalarKernel.phi_bound_ball
#print axioms OQ14.Packet06ComplexScalarKernel.phi_memLp_two_ball
#print axioms OQ14.Packet06ComplexScalarKernel.phi_locallyIntegrable
end OQ14.Packet06ComplexScalarKernel
