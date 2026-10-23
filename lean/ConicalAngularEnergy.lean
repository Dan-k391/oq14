import ConicalNontrivial
import ConicalMomentWeights

/-! Genuine positive tangential energy of the actual conical eigenprofile. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.ConicalAngularEnergy
open MeasureTheory Set OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1 OQ14.ConicalCapField
open scoped InnerProductSpace

def energy (a d t : ℝ) : ℝ := ∫ n : Sphere,
  CapSturmLiouville.coefficient d t ((n : Space) 2)*‖gradient a t n‖^2 ∂angularMeasure

theorem energy_integrable (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    Integrable (fun n : Sphere => CapSturmLiouville.coefficient d t ((n : Space) 2)*‖gradient a t n‖^2) angularMeasure :=
  SphereCapWeak.coefficient_integrable _ (gradient_memLp a t ha ht ht1 2).norm.integrable_sq d t

theorem energy_positive (a d t : ℝ) (ha : a ∈ Ioo (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1) :
    0 < energy a d t := by
  have hi := (gradient_memLp a t ⟨ha.1.le,ha.2.le⟩ ht ht1 2).norm.integrable_sq
  obtain ⟨S,_,_,hS,hG⟩ := ConicalNontrivial.exists_open_gradient_positive a t ha ht ht1
  have hp : 0 < ∫ n : Sphere, ‖gradient a t n‖^2 ∂angularMeasure := by
    apply (integral_pos_iff_support_of_nonneg (fun n => sq_nonneg _) hi).mpr
    apply hS.trans_le (measure_mono ?_)
    intro n hn
    exact (sq_pos_of_pos (hG n hn)).ne'
  apply hp.trans_le
  apply integral_mono hi (energy_integrable a d t ⟨ha.1.le,ha.2.le⟩ ht ht1)
  intro n
  have hc : 1 ≤ CapSturmLiouville.coefficient d t ((n : Space) 2) := by
    unfold CapSturmLiouville.coefficient
    split_ifs <;> linarith
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (sq_nonneg ‖gradient a t n‖)

theorem angular_tangent_identity (ν a d t : ℝ) (n : Sphere) :
    (∑ i : Fin 3, angularElectric ν a t n i*(CapSturmLiouville.coefficient d t ((n : Space) 2)*gradient a t n i))=
      CapSturmLiouville.coefficient d t ((n : Space) 2)*‖gradient a t n‖^2 := by
  have hi : ⟪angularElectric ν a t n,gradient a t n⟫_ℝ=‖gradient a t n‖^2 := by
    rw [angularElectric,inner_add_left,inner_smul_left,gradient_tangent,mul_zero,zero_add,real_inner_self_eq_norm_sq]
  rw [← hi,PiLp.inner_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RCLike.inner_apply,conj_trivial]
  ring

end OQ14.ConicalAngularEnergy

#print axioms OQ14.ConicalAngularEnergy.energy_integrable
#print axioms OQ14.ConicalAngularEnergy.energy_positive
#print axioms OQ14.ConicalAngularEnergy.angular_tangent_identity
