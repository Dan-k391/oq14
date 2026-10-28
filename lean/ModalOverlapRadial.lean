import ModalOrigin
import ModalMatching
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ModalOverlapRadial
open Complex Filter OQ14.ModalAlgebra OQ14.ModalMatching
open scoped Topology

def primitive (a b r : ℂ) : ℂ :=
  (2/3) * (b^2*a*psiD 1 (a*r)*psi 1 (b*r) - a^2*b*psiD 1 (b*r)*psi 1 (a*r)) / (b^2-a^2)

def radialIntegrand (a b r : ℂ) : ℂ :=
  (2/3)*a*b*psiD 1 (a*r)*psiD 1 (b*r) + (4/3)*psi 1 (a*r)*psi 1 (b*r)/r^2

theorem primitive_deriv (a b r : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hr : r ≠ 0)
    (hab : b^2-a^2 ≠ 0) : HasDerivAt (primitive a b) (radialIntegrand a b r) r := by
  have hpa := (psi_hasDerivAt 1 (a*r) (mul_ne_zero ha hr)).comp r ((hasDerivAt_id r).const_mul a)
  have hpb := (psi_hasDerivAt 1 (b*r) (mul_ne_zero hb hr)).comp r ((hasDerivAt_id r).const_mul b)
  have hda := (psiD_hasDerivAt 1 (a*r) (mul_ne_zero ha hr)).comp r ((hasDerivAt_id r).const_mul a)
  have hdb := (psiD_hasDerivAt 1 (b*r) (mul_ne_zero hb hr)).comp r ((hasDerivAt_id r).const_mul b)
  have h := (((hda.const_mul (b^2*a)).mul hpb).sub ((hdb.const_mul (a^2*b)).mul hpa)).const_mul (2/3)
  have h := h.div_const (b^2-a^2)
  convert h using 1
  · simp only [radialIntegrand] 
    apply (eq_div_iff hab).2
    field_simp [mul_pow,ha,hb,hr]
    ring
theorem radial_profile (a b : ℂ) (r : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hr : r ≠ 0) :
    (r : ℂ)^2 * (ModalOrigin.centerA a r * ModalOrigin.centerA b r +
      (r : ℂ)^2/3*(ModalOrigin.centerA a r * ModalOrigin.centerB b r +
        ModalOrigin.centerA b r * ModalOrigin.centerB a r) +
      (r : ℂ)^4/3 * ModalOrigin.centerB a r * ModalOrigin.centerB b r) =
        radialIntegrand a b r := by
  rw [ModalOrigin.centerA_eq a ha r hr, ModalOrigin.centerA_eq b hb r hr,
    ModalOrigin.centerB_eq a ha r hr, ModalOrigin.centerB_eq b hb r hr]
  unfold ModalDipole.electricA ModalDipole.electricB ModalDipole.scaledRadial ModalDipole.scaledRadialD radialIntegrand
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  simp only [div_eq_mul_inv, ← inv_pow]
  field_simp [hr']
  ring_nf
  field_simp [hr']
  ring
def regularizedPrimitive (a b r : ℂ) : ℂ :=
  (2/3) * (b^2*a*(2*(a*r)*ModalOrigin.profile (a*r)+(a*r)^2*deriv ModalOrigin.profile (a*r))*
      ((b*r)^2*ModalOrigin.profile (b*r)) -
    a^2*b*(2*(b*r)*ModalOrigin.profile (b*r)+(b*r)^2*deriv ModalOrigin.profile (b*r))*
      ((a*r)^2*ModalOrigin.profile (a*r))) / (b^2-a^2)

theorem primitive_eq_regularized (a b r : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hr : r ≠ 0) :
    primitive a b r = regularizedPrimitive a b r := by
  unfold primitive regularizedPrimitive
  rw [ModalOrigin.psiD_profile _ (mul_ne_zero ha hr), ModalOrigin.psi_profile _ (mul_ne_zero hb hr),
    ModalOrigin.psiD_profile _ (mul_ne_zero hb hr), ModalOrigin.psi_profile _ (mul_ne_zero ha hr)]

theorem regularized_zero (a b : ℂ) : regularizedPrimitive a b 0 = 0 := by
  simp [regularizedPrimitive]

theorem regularized_continuous (a b : ℂ) : Continuous (regularizedPrimitive a b) := by
  unfold regularizedPrimitive
  have hp := ModalOrigin.profile_differentiable.continuous
  have hd := ModalOrigin.profile_deriv_differentiable.continuous
  fun_prop

theorem primitive_tendsto_zero (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Filter.Tendsto (primitive a b) (𝓝[≠] 0) (𝓝 0) := by
  have h : Tendsto (regularizedPrimitive a b) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa only [regularized_zero] using ((regularized_continuous a b).continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (primitive_eq_regularized a b r ha hb hr).symm
def physicalRadial (a b : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ)^2 * (ModalOrigin.centerA a r * ModalOrigin.centerA b r +
    (r : ℂ)^2/3*(ModalOrigin.centerA a r * ModalOrigin.centerB b r +
      ModalOrigin.centerA b r * ModalOrigin.centerB a r) +
    (r : ℂ)^4/3 * ModalOrigin.centerB a r * ModalOrigin.centerB b r)

theorem physicalRadial_continuous (a b : ℂ) : Continuous (physicalRadial a b) := by
  unfold physicalRadial
  have ha := (ModalOrigin.centerA_differentiable a).continuous
  have hb := (ModalOrigin.centerA_differentiable b).continuous
  have hba := (ModalOrigin.centerB_differentiable a).continuous
  have hbb := (ModalOrigin.centerB_differentiable b).continuous
  fun_prop

theorem physicalRadial_integral (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : b^2-a^2 ≠ 0) :
    (∫ r in (0 : ℝ)..1, physicalRadial a b r) = regularizedPrimitive a b 1 := by
  have hc : Continuous (fun r : ℝ => regularizedPrimitive a b r) :=
    (regularized_continuous a b).comp Complex.continuous_ofReal
  have hd (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => regularizedPrimitive a b t) (physicalRadial a b r) r := by
    have hr0 : r ≠ 0 := ne_of_gt hr.1
    have hc0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0
    have he : primitive a b =ᶠ[𝓝 (r : ℂ)] regularizedPrimitive a b := by
      filter_upwards [isOpen_ne.mem_nhds hc0] with z hz
      exact primitive_eq_regularized a b z ha hb hz
    have h := ((he.hasDerivAt_iff.mp (primitive_deriv a b r ha hb hc0 hab)).comp_ofReal)
    rw [← radial_profile a b r ha hb hr0] at h
    exact h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (show (0 : ℝ) ≤ 1 by norm_num)
    hc.continuousOn hd ((physicalRadial_continuous a b).intervalIntegrable 0 1)
  simpa only [ofReal_zero, ofReal_one, regularized_zero, sub_zero] using h
theorem special_endpoint (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0) (hn2 : n^2-1 ≠ 0) :
    regularizedPrimitive k (n*k) 1 =
      (2/3)*(n*k)/(n^2-1) *
        (n*psi 1 (n*k)*psiD 1 k-psi 1 k*psiD 1 (n*k)) := by
  have hk2 : (n*k)^2-k^2 ≠ 0 := by
    have h : (n*k)^2-k^2 = (n^2-1)*k^2 := by ring
    rw [h]
    exact mul_ne_zero hn2 (pow_ne_zero 2 hk)
  rw [← primitive_eq_regularized k (n*k) 1 hk (mul_ne_zero hn hk) one_ne_zero]
  unfold primitive
  simp only [mul_one]
  have he : (n*k)^2-k^2 = (n^2-1)*k^2 := by ring
  rw [he]
  field_simp [hn2,hk]
  ring
end OQ14.ModalOverlapRadial
#print axioms OQ14.ModalOverlapRadial.primitive_deriv





#print axioms OQ14.ModalOverlapRadial.radial_profile




#print axioms OQ14.ModalOverlapRadial.primitive_tendsto_zero





#print axioms OQ14.ModalOverlapRadial.physicalRadial_integral


#print axioms OQ14.ModalOverlapRadial.special_endpoint

#print axioms OQ14.ModalOverlapRadial.primitive_eq_regularized
#print axioms OQ14.ModalOverlapRadial.regularized_zero
#print axioms OQ14.ModalOverlapRadial.regularized_continuous
#print axioms OQ14.ModalOverlapRadial.physicalRadial_continuous
