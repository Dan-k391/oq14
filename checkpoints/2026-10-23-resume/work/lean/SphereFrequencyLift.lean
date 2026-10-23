import AngularJetSymmetry

/-! Actual sphere directions realizing a transverse frequency disk. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SphereFrequencyLift
open Maxwell SphereReactionKernel
abbrev Space := FourierL2.Space

theorem exists_direction (k : ℝ) (hk : 0<k) (s t : ℝ) (hst : s^2+t^2≤k^2) :
    ∃ θ : Sphere, k*θ.val 0=s ∧ k*θ.val 1=t := by
  let x : Space := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![s/k,t/k,Real.sqrt (k^2-s^2-t^2)/k]
  have hsqrt := Real.sq_sqrt (by linarith : 0≤k^2-s^2-t^2)
  have hn : ‖x‖^2=1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [x,Fin.sum_univ_three,Real.norm_eq_abs,sq_abs]
    change (s/k)^2+(t/k)^2+(Real.sqrt (k^2-s^2-t^2)/k)^2=1
    field_simp
    nlinarith
  have hm : x∈Metric.sphere (0 : Space) 1 := by
    rw [Metric.mem_sphere,dist_zero_right]
    nlinarith [norm_nonneg x]
  refine ⟨⟨x,hm⟩,?_,?_⟩
  · change k*(s/k)=s
    field_simp
  · change k*(t/k)=t
    field_simp

theorem rectangle_direction (k : ℝ) (hk : 0<k) (s t : ℝ)
    (hs : -k/3<s) (hs' : s<k/3) (ht : -k/3<t) (ht' : t<k/3) :
    ∃ θ : Sphere, k*θ.val 0=s ∧ k*θ.val 1=t := by
  apply exists_direction k hk s t
  nlinarith [mul_nonneg (by linarith : 0≤k/3-s) (by linarith : 0≤k/3+s),
    mul_nonneg (by linarith : 0≤k/3-t) (by linarith : 0≤k/3+t)]

end OQ14.SphereFrequencyLift
#print axioms OQ14.SphereFrequencyLift.exists_direction
#print axioms OQ14.SphereFrequencyLift.rectangle_direction
