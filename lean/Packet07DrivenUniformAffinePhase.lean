import Packet07DrivenUniformAffineGeometry

/-! Positive affine transport of driven phase representatives and amplitude. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenUniformAffinePhase
open Set Metric Maxwell Packet07DrivenUniformAffineGeometry Packet05ActualMaximum Packet05BinaryPhaseMaximum
abbrev Space := Maxwell.Space

def transport (s : ℝ) (hs : 0 < s) (a : Space) (R : Fin 3 → Space → ℂ) : Fin 3 → Space → ℂ :=
  fun k y => (s : ℂ)*R k ((placement s hs a).symm y)

theorem amplitude_transport (s : ℝ) (hs : 0 < s) (a : Space) (R : Fin 3 → Space → ℂ) (y : Space) :
    physicalAmplitude (transport s hs a R) y = s*physicalAmplitude R ((placement s hs a).symm y) := by
  simp only [physicalAmplitude,transport,Fin.sum_univ_three,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  rw [show (s*‖R 0 ((placement s hs a).symm y)‖)^2+(s*‖R 1 ((placement s hs a).symm y)‖)^2+
      (s*‖R 2 ((placement s hs a).symm y)‖)^2 = s^2*(‖R 0 ((placement s hs a).symm y)‖^2+
      ‖R 1 ((placement s hs a).symm y)‖^2+‖R 2 ((placement s hs a).symm y)‖^2) by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_pos hs]

theorem continuous_transport (s : ℝ) (hs : 0 < s) (a : Space) (R : Fin 3 → Space → ℂ) (K : Set Space)
    (hR : ∀ k, ContinuousOn (R k) K) : ∀ k, ContinuousOn (transport s hs a R k) (placement s hs a '' K) := by
  intro k
  apply continuousOn_const.mul
  apply (hR k).comp (placement s hs a).symm.continuous.continuousOn
  rintro y ⟨x,hx,rfl⟩
  simpa using hx

theorem phase_transport (s : ℝ) (hs : 0 < s) (a : Space) (inside outside : Fin 3 → Space → ℂ) (b : Bool) :
    phaseField (transport s hs a inside) (transport s hs a outside) b = transport s hs a (phaseField inside outside b) := by cases b <;> rfl
end OQ14.Packet07DrivenUniformAffinePhase
#print axioms OQ14.Packet07DrivenUniformAffinePhase.amplitude_transport
#print axioms OQ14.Packet07DrivenUniformAffinePhase.continuous_transport
#print axioms OQ14.Packet07DrivenUniformAffinePhase.phase_transport
