import Packet06Laurent
import ComplexKernelResponse

/-! Exact two-sided weighted/unweighted inverse and kernel transport. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06WeightedTransport

theorem inverse_switch {R : Type*} [Ring R] (P Q J : R)
    (hl : (1-P*Q)*J = 1) (hr : J*(1-P*Q) = 1) :
    (1-Q*P)*(1+Q*J*P) = 1 ∧ (1+Q*J*P)*(1-Q*P) = 1 := by
  constructor
  · calc
      _ = 1+Q*((1-P*Q)*J-1)*P := by noncomm_ring
      _ = 1 := by rw [hl]; simp
  · calc
      _ = 1+Q*(J*(1-P*Q)-1)*P := by noncomm_ring
      _ = 1 := by rw [hr]; simp

theorem isUnit_switch {R : Type*} [Ring R] (P Q : R) :
    IsUnit (1-P*Q) ↔ IsUnit (1-Q*P) := by
  have imp (P Q : R) (h : IsUnit (1-P*Q)) : IsUnit (1-Q*P) := by
    obtain ⟨u,hu⟩ := h
    have hs := inverse_switch P Q (↑u⁻¹) (by rw [←hu]; simp)
      (by rw [←hu]; simp)
    exact ⟨⟨1-Q*P,1+Q*↑u⁻¹*P,hs.1,hs.2⟩,rfl⟩
  exact ⟨imp P Q,imp Q P⟩

theorem ring_inverse_switch {R : Type*} [Ring R] (P Q : R)
    (h : IsUnit (1-P*Q)) :
    Ring.inverse (1-Q*P) = 1+Q*Ring.inverse (1-P*Q)*P := by
  have hi := (isUnit_switch P Q).mp h
  have hs := inverse_switch P Q (Ring.inverse (1-P*Q))
    (Ring.mul_inverse_cancel _ h) (Ring.inverse_mul_cancel _ h)
  calc
    Ring.inverse (1-Q*P) = Ring.inverse (1-Q*P)*((1-Q*P)*(1+Q*Ring.inverse (1-P*Q)*P)) := by rw [hs.1,mul_one]
    _ = _ := by rw [←mul_assoc,Ring.inverse_mul_cancel _ hi,one_mul]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem kernel_forward (S K : H →L[ℂ] H) (E : H)
    (hE : (1-K*S*S) E = 0) : (1-S*K*S) (S E) = 0 := by
  have he : E = K (S (S E)) := by
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
      ContinuousLinearMap.mul_apply,sub_eq_zero] using hE
  change S E-S (K (S (S E))) = 0
  exact sub_eq_zero.mpr (congrArg S he)

theorem kernel_backward (S K : H →L[ℂ] H) (u : H)
    (hu : (1-S*K*S) u = 0) :
    (1-K*S*S) (K (S u)) = 0 ∧ S (K (S u)) = u := by
  have he : S (K (S u)) = u := by
    symm
    simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
      ContinuousLinearMap.mul_apply,sub_eq_zero] using hu
  refine ⟨?_,he⟩
  change K (S u)-K (S (S (K (S u)))) = 0
  rw [he,sub_self]

theorem kernel_forward_inverse (S K : H →L[ℂ] H) (E : H)
    (hE : (1-K*S*S) E = 0) : K (S (S E)) = E := by
  symm
  simpa only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
    ContinuousLinearMap.mul_apply,sub_eq_zero] using hE

theorem weighted_inverse_formula (S K : H →L[ℂ] H)
    (hu : IsUnit (1-S*K*S)) :
    IsUnit (1-K*S*S) ∧
    Ring.inverse (1-K*S*S) = 1+K*S*Ring.inverse (1-S*K*S)*S := by
  have he : 1-S*(K*S) = 1-S*K*S := by noncomm_ring
  have hl : 1-K*S*S = 1-(K*S)*S := rfl
  rw [hl]
  exact ⟨(isUnit_switch S (K*S)).mp (he.symm ▸ hu),by
    simpa only [he] using ring_inverse_switch S (K*S) (he.symm ▸ hu)⟩

end OQ14.Packet06WeightedTransport
#print axioms OQ14.Packet06WeightedTransport.inverse_switch
#print axioms OQ14.Packet06WeightedTransport.isUnit_switch
#print axioms OQ14.Packet06WeightedTransport.ring_inverse_switch
#print axioms OQ14.Packet06WeightedTransport.kernel_forward
#print axioms OQ14.Packet06WeightedTransport.kernel_backward
#print axioms OQ14.Packet06WeightedTransport.kernel_forward_inverse
#print axioms OQ14.Packet06WeightedTransport.weighted_inverse_formula
