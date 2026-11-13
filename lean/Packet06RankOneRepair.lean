import Packet06SpherePole
import Mathlib.Analysis.Normed.Operator.Banach

/-! A genuine one-dimensional kernel and cokernel admit an invertible rank-one
repair. The right and left normalizations are independent. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06RankOneRepair
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def repair (A : E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ) : E →L[ℂ] E :=
  A+ψ.smulRight w

theorem repair_apply (A : E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ) (x : E) :
    repair A w ψ x = A x + ψ x • w := rfl

theorem repair_bijective (A : E →L[ℂ] E) (u w : E) (φ ψ : E →L[ℂ] ℂ)
    (hAu : A u = 0) (hψ : ψ u = 1) (hφ : φ w = 1)
    (hann : ∀ x, φ (A x) = 0)
    (hker : ∀ x, A x = 0 → ∃ a : ℂ, x = a • u)
    (hrange : ∀ y, φ y = 0 → ∃ x, A x = y) : Function.Bijective (repair A w ψ) := by
  have hzero : ∀ x, repair A w ψ x = 0 → x = 0 := by
    intro x hx
    have hp := congrArg φ hx
    simp only [repair_apply,map_add,map_smul,hann,hφ,smul_eq_mul,mul_one,zero_add,map_zero] at hp
    have ha : A x = 0 := by simpa only [repair_apply,hp,zero_smul,add_zero] using hx
    obtain ⟨a,ha⟩ := hker x ha
    have haz : a = 0 := by simpa only [ha,map_smul,hψ,smul_eq_mul,mul_one] using hp
    simp [ha,haz]
  refine ⟨?_,?_⟩
  · intro x y hxy
    have h := hzero (x-y) (by rw [map_sub,hxy,sub_self])
    exact sub_eq_zero.mp h
  · intro y
    have hy : φ (y-φ y • w) = 0 := by simp [hφ]
    obtain ⟨v,hv⟩ := hrange (y-φ y • w) hy
    refine ⟨v+(φ y-ψ v) • u,?_⟩
    rw [repair_apply,map_add,map_smul,hAu,smul_zero,add_zero,hv,map_add,map_smul,hψ]
    simp only [smul_eq_mul,mul_one,add_sub_cancel]
    abel

theorem repair_isUnit [CompleteSpace E] (A : E →L[ℂ] E) (u w : E) (φ ψ : E →L[ℂ] ℂ)
    (hAu : A u = 0) (hψ : ψ u = 1) (hφ : φ w = 1)
    (hann : ∀ x, φ (A x) = 0)
    (hker : ∀ x, A x = 0 → ∃ a : ℂ, x = a • u)
    (hrange : ∀ y, φ y = 0 → ∃ x, A x = y) : IsUnit (repair A w ψ) :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr (repair_bijective A u w φ ψ hAu hψ hφ hann hker hrange)

theorem repaired_inverse_vector (A : E →L[ℂ] E) (u w : E) (ψ : E →L[ℂ] ℂ)
    (hC : IsUnit (repair A w ψ)) (hAu : A u = 0) (hψ : ψ u = 1) :
    Ring.inverse (repair A w ψ) w = u := by
  have he : repair A w ψ u = w := by simp [repair_apply,hAu,hψ]
  have hh := congrArg (fun L : E →L[ℂ] E => L u) (Ring.inverse_mul_cancel _ hC)
  change Ring.inverse (repair A w ψ) (repair A w ψ u) = u at hh
  rwa [he] at hh

theorem repaired_left_inverse (A : E →L[ℂ] E) (w : E) (φ ψ : E →L[ℂ] ℂ)
    (hC : IsUnit (repair A w ψ)) (hφ : φ w = 1) (hann : ∀ x, φ (A x) = 0) (x : E) :
    ψ (Ring.inverse (repair A w ψ) x) = φ x := by
  have hh := congrArg (fun L : E →L[ℂ] E => φ (L x)) (Ring.mul_inverse_cancel _ hC)
  change φ (repair A w ψ (Ring.inverse (repair A w ψ) x)) = φ x at hh
  simpa only [repair_apply,map_add,map_smul,hann,hφ,smul_eq_mul,mul_one,zero_add] using hh

end OQ14.Packet06RankOneRepair
#print axioms OQ14.Packet06RankOneRepair.repair_apply
#print axioms OQ14.Packet06RankOneRepair.repair_bijective
#print axioms OQ14.Packet06RankOneRepair.repair_isUnit
#print axioms OQ14.Packet06RankOneRepair.repaired_inverse_vector
#print axioms OQ14.Packet06RankOneRepair.repaired_left_inverse
