import Packet06RankOneRepair
import FiniteRankSchur

/-! Scalar Schur reduction from an actual rank-one repair. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ScalarSchur
open Packet06RankOneRepair
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def scalar (A : E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ) : ℂ :=
  1-ψ (Ring.inverse (repair A w ψ) w)

theorem scalar_map_isUnit (a : ℂ) : IsUnit (a • (1 : ℂ →L[ℂ] ℂ)) ↔ a ≠ 0 := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · intro h ha
    have he : (0 : ℂ) = 1 := h.1 (by simp [ha])
    exact zero_ne_one he
  · intro ha
    constructor
    · intro x y h
      exact (mul_left_cancel₀ ha (by simpa using h))
    · intro y
      refine ⟨y/a,?_⟩
      change a*(y/a)=y
      field_simp

omit [CompleteSpace E] in
theorem isUnit_iff_scalar (A : E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ)
    (hC : IsUnit (repair A w ψ)) : IsUnit A ↔ scalar A w ψ ≠ 0 := by
  let Iw : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight w
  have he : repair A w ψ-Iw.comp ψ = A := by
    ext x
    change (A x+ψ x • w)-ψ x • w = A x
    abel
  have hs : FiniteRankSchur.schur (repair A w ψ) Iw ψ = scalar A w ψ • (1 : ℂ →L[ℂ] ℂ) := by
    apply ContinuousLinearMap.ext
    intro a
    change a-ψ (Ring.inverse (repair A w ψ) (a • w)) = scalar A w ψ * a
    rw [map_smul,map_smul]
    simp only [scalar,smul_eq_mul]
    ring
  have h := FiniteRankSchur.isUnit_iff_schur (repair A w ψ) hC Iw ψ
  rw [he,hs,scalar_map_isUnit] at h
  exact h

omit [CompleteSpace E] in
theorem scalar_zero (A : E →L[ℂ] E) (u w : E) (ψ : E →L[ℂ] ℂ)
    (hC : IsUnit (repair A w ψ)) (hAu : A u = 0) (hψ : ψ u = 1) : scalar A w ψ = 0 := by
  rw [scalar,repaired_inverse_vector A u w ψ hC hAu hψ,hψ,sub_self]

omit [CompleteSpace E] in
theorem scalar_kernel (A : E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ)
    (hC : IsUnit (repair A w ψ)) (hs : scalar A w ψ = 0) :
    Ring.inverse (repair A w ψ) w ≠ 0 ∧ A (Ring.inverse (repair A w ψ) w) = 0 ∧
      ψ (Ring.inverse (repair A w ψ) w) = 1 ∧
      (∀ x, A x = 0 ↔ x = ψ x • Ring.inverse (repair A w ψ) w) := by
  have hp : ψ (Ring.inverse (repair A w ψ) w) = 1 := by
    have hh : 1-ψ (Ring.inverse (repair A w ψ) w) = 0 := hs
    exact (sub_eq_zero.mp hh).symm
  have hCv := congrArg (fun L : E →L[ℂ] E => L w) (Ring.mul_inverse_cancel _ hC)
  change A (Ring.inverse (repair A w ψ) w)+ψ (Ring.inverse (repair A w ψ) w) • w = w at hCv
  rw [hp,one_smul] at hCv
  have hAv : A (Ring.inverse (repair A w ψ) w) = 0 := add_right_cancel (hCv.trans (zero_add w).symm)
  refine ⟨?_,hAv,hp,?_⟩
  · intro hz
    rw [hz,map_zero] at hp
    exact zero_ne_one hp
  · intro x
    constructor
    · intro hx
      have hCx : repair A w ψ x = ψ x • w := by simp [repair_apply,hx]
      have hh := congrArg (fun v : E => Ring.inverse (repair A w ψ) v) hCx
      have hi := congrArg (fun L : E →L[ℂ] E => L x) (Ring.inverse_mul_cancel _ hC)
      change Ring.inverse (repair A w ψ) (repair A w ψ x) = x at hi
      dsimp only at hh
      rw [hi,map_smul] at hh
      exact hh
    · intro hx
      rw [hx,map_smul,hAv,smul_zero]

end OQ14.Packet06ScalarSchur
#print axioms OQ14.Packet06ScalarSchur.scalar_map_isUnit
#print axioms OQ14.Packet06ScalarSchur.isUnit_iff_scalar
#print axioms OQ14.Packet06ScalarSchur.scalar_zero
#print axioms OQ14.Packet06ScalarSchur.scalar_kernel
