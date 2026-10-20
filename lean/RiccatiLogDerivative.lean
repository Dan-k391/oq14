import RiccatiBarrier

/-! # Actual regular logarithmic derivative bounds in the radial barrier -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000

namespace OQ14.RiccatiLogDerivative

open Filter Set Metric OQ14.RiccatiBarrier OQ14.HankelRealBasis
open scoped Topology

def weighted (l : ℕ) (β x : ℝ) : ℝ := x^(β-1)*(x*du l x-β*u l x)

theorem weighted_continuous (l : ℕ) (β : ℝ) (hβ : 1 ≤ β) : Continuous (weighted l β) :=
  (Real.continuous_rpow_const (sub_nonneg.mpr hβ)).mul
    ((continuous_id.mul (du_continuous l)).sub (continuous_const.mul (u_continuous l)))

theorem weighted_zero (l : ℕ) (β : ℝ) : weighted l β 0 = 0 := by
  simp [weighted,u_zero]

theorem weighted_hasDerivAt (l : ℕ) (β x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (weighted l β)
      ((x^(β-1)/x)*(ν l-β*(β-1)-x^2)*u l x) x := by
  have h := (Real.hasDerivAt_rpow_const (x := x) (p := β-1) (Or.inl hx)).mul
    (((hasDerivAt_id x).mul (du_hasDerivAt l x hx)).sub ((u_hasDerivAt l x).const_mul β))
  convert h using 1
  dsimp only [id_eq]
  rw [Real.rpow_sub_one hx (β-1)]
  field_simp [hx]
  ring

theorem weighted_nonnegative (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (β : ℝ) (hβ : 1 ≤ β) (hβν : β*(β-1) ≤ ν l-R^2)
    (x : ℝ) (hx : x ∈ Ioc 0 R) : 0 ≤ weighted l β x := by
  have hm : MonotoneOn (weighted l β) (Icc 0 R) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 R) (weighted_continuous l β hβ).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (weighted_hasDerivAt l β t ht.1.ne').differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(weighted_hasDerivAt l β t ht.1.ne').deriv]
      have hu : 0 < u l t := by
        rw [u_eq_regular l t ht.1.ne']
        exact (barrier_positive l R hR hbarrier t ⟨ht.1,ht.2.le⟩).1
      have hs : t^2 ≤ R^2 := (sq_le_sq₀ ht.1.le hR.le).mpr ht.2.le
      exact mul_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg ht.1.le _) ht.1.le)
        (by linarith)) hu.le
  have h := hm ⟨le_rfl,hR.le⟩ ⟨hx.1.le,hx.2⟩ hx.1.le
  rwa [weighted_zero] at h

theorem weighted_nonpositive (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (β : ℝ) (hβ : 1 ≤ β) (hνβ : ν l ≤ β*(β-1))
    (x : ℝ) (hx : x ∈ Ioc 0 R) : weighted l β x ≤ 0 := by
  have hm : AntitoneOn (weighted l β) (Icc 0 R) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 R) (weighted_continuous l β hβ).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (weighted_hasDerivAt l β t ht.1.ne').differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(weighted_hasDerivAt l β t ht.1.ne').deriv]
      have hu : 0 < u l t := by
        rw [u_eq_regular l t ht.1.ne']
        exact (barrier_positive l R hR hbarrier t ⟨ht.1,ht.2.le⟩).1
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (div_nonneg (Real.rpow_nonneg ht.1.le _) ht.1.le)
          (by nlinarith [sq_nonneg t])) hu.le
  have h := hm ⟨le_rfl,hR.le⟩ ⟨hx.1.le,hx.2⟩ hx.1.le
  rwa [weighted_zero] at h

def gamma (l : ℕ) (R : ℝ) : ℝ := (1+Real.sqrt (1+4*(ν l-R^2)))/2

theorem gamma_ge_one (l : ℕ) (R : ℝ) (hbarrier : R^2 < ν l) : 1 ≤ gamma l R := by
  have hs : 1 ≤ Real.sqrt (1+4*(ν l-R^2)) := Real.one_le_sqrt.mpr (by linarith)
  unfold gamma
  linarith

theorem gamma_equation (l : ℕ) (R : ℝ) (hbarrier : R^2 < ν l) :
    gamma l R*(gamma l R-1) = ν l-R^2 := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1+4*(ν l-R^2))
  unfold gamma
  nlinarith

theorem gamma_le_degree (l : ℕ) (R : ℝ) (hbarrier : R^2 < ν l) : gamma l R ≤ l+1 := by
  have hge := gamma_ge_one l R hbarrier
  have he := gamma_equation l R hbarrier
  by_contra hnot
  have hpos : 0 < (gamma l R-(l+1))*(gamma l R+l) :=
    mul_pos (sub_pos.mpr (lt_of_not_ge hnot)) (by positivity)
  unfold ν at he
  nlinarith [sq_nonneg R]

theorem barrier_logDerivative_bounds (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (x : ℝ) (hx : x ∈ Ioc 0 R) :
    gamma l R ≤ x*regularD l x/regular l x ∧ x*regularD l x/regular l x ≤ l+1 := by
  have hu : 0 < u l x := by
    rw [u_eq_regular l x hx.1.ne']
    exact (barrier_positive l R hR hbarrier x hx).1
  have hlo := weighted_nonnegative l R hR hbarrier (gamma l R) (gamma_ge_one l R hbarrier)
    (gamma_equation l R hbarrier).le x hx
  have hhi := weighted_nonpositive l R hR hbarrier (l+1)
    (by have := Nat.cast_nonneg (α := ℝ) l; linarith) (by unfold ν; nlinarith) x hx
  have hlw : 0 < x^(gamma l R-1) := Real.rpow_pos_of_pos hx.1 _
  have hhw : 0 < x^((l+1 : ℝ)-1) := Real.rpow_pos_of_pos hx.1 _
  have hlo' : 0 ≤ x*du l x-gamma l R*u l x := nonneg_of_mul_nonneg_right hlo hlw
  have hhi' : x*du l x-(l+1)*u l x ≤ 0 := nonpos_of_mul_nonpos_right hhi hhw
  have hres : gamma l R ≤ x*du l x/u l x ∧ x*du l x/u l x ≤ l+1 :=
    ⟨(le_div_iff₀ hu).mpr (by linarith),(div_le_iff₀ hu).mpr (by linarith)⟩
  simpa only [u_eq_regular l x hx.1.ne',du_eq_regularD l x hx.1.ne'] using hres

end OQ14.RiccatiLogDerivative

#print axioms OQ14.RiccatiLogDerivative.weighted_continuous
#print axioms OQ14.RiccatiLogDerivative.weighted_zero
#print axioms OQ14.RiccatiLogDerivative.weighted_hasDerivAt
#print axioms OQ14.RiccatiLogDerivative.weighted_nonnegative
#print axioms OQ14.RiccatiLogDerivative.weighted_nonpositive
#print axioms OQ14.RiccatiLogDerivative.gamma_ge_one
#print axioms OQ14.RiccatiLogDerivative.gamma_equation
#print axioms OQ14.RiccatiLogDerivative.gamma_le_degree
#print axioms OQ14.RiccatiLogDerivative.barrier_logDerivative_bounds
