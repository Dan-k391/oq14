import SphericalInterfaces
import ModalWeak
import DebyeRadialTrace

/-! A literal radial primitive resolves dielectric normal jumps in weak curls. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.RadialNormalPrimitive
open MeasureTheory Set Filter OQ14.Maxwell OQ14.HarmonicPolynomial
open scoped Topology

def radialDerivative (b : ℝ → ℂ) (r : ℝ) : ℂ := (r : ℂ)*b r
def primitive (b : ℝ → ℂ) (r : ℝ) : ℂ := ∫ s in (0 : ℝ)..r, radialDerivative b s

theorem primitive_continuous (b : ℝ → ℂ)
    (hi : ∀ a c, IntervalIntegrable (radialDerivative b) volume a c) : Continuous (primitive b) :=
  intervalIntegral.continuous_primitive hi 0

theorem primitive_hasDerivAt (b : ℝ → ℂ)
    (hi : ∀ a c, IntervalIntegrable (radialDerivative b) volume a c)
    (hm : StronglyMeasurable (radialDerivative b)) (r : ℝ) (hc : ContinuousAt b r) :
    HasDerivAt (primitive b) ((r : ℂ)*b r) r :=
  intervalIntegral.integral_hasDerivAt_right (hi 0 r) hm.stronglyMeasurableAtFilter
    (Complex.continuous_ofReal.continuousAt.mul hc)

def potential (b : ℝ → ℂ) (p : Poly) (x : Space) : ℂ := primitive b ‖x‖*complexEvaluate p x
def potentialGradient (b : ℝ → ℂ) (p : Poly) : Field := fun x i =>
  primitive b ‖x‖*dcoord (complexEvaluate p) x i+b ‖x‖*(x i : ℂ)*complexEvaluate p x

theorem potential_continuous (b : ℝ → ℂ) (p : Poly)
    (hi : ∀ a c, IntervalIntegrable (radialDerivative b) volume a c) : Continuous (potential b p) :=
  ((primitive_continuous b hi).comp continuous_norm).mul (complexEvaluate_regular p).continuous

theorem potential_differentiableAt (b : ℝ → ℂ) (p : Poly)
    (hi : ∀ a c, IntervalIntegrable (radialDerivative b) volume a c)
    (hm : StronglyMeasurable (radialDerivative b)) (x : Space) (hx : x≠0)
    (hc : ContinuousAt b ‖x‖) : DifferentiableAt ℝ (potential b p) x :=
  ((primitive_hasDerivAt b hi hm ‖x‖ hc).differentiableAt.comp x
    (differentiableAt_id.norm ℝ hx)).mul ((complexEvaluate_regular p).differentiable (by simp) x)

theorem potential_partial (b : ℝ → ℂ) (p : Poly)
    (hi : ∀ a c, IntervalIntegrable (radialDerivative b) volume a c)
    (hm : StronglyMeasurable (radialDerivative b)) (x : Space) (hx : x≠0)
    (hc : ContinuousAt b ‖x‖) (i : Fin 3) :
    dcoord (potential b p) x i=potentialGradient b p x i := by
  have hd := (primitive_hasDerivAt b hi hm ‖x‖ hc).differentiableAt.comp x
    (differentiableAt_id.norm ℝ hx)
  change DifferentiableAt ℝ (fun y : Space => primitive b ‖y‖) x at hd
  unfold potential
  rw [partial_mul hd ((complexEvaluate_regular p).differentiable (by simp) x),
    GreenKernel.radial_composition_partial (primitive b) _ x hx (primitive_hasDerivAt b hi hm ‖x‖ hc)]
  unfold potentialGradient
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  push_cast
  field_simp [hr]
  ring

theorem potentialGradient_locallyIntegrable (b : ℝ → ℂ) (p : Poly)
    (hi : ∀ a c, IntervalIntegrable (radialDerivative b) volume a c)
    (hb : LocallyIntegrable (fun x : Space => b ‖x‖)) (i : Fin 3) :
    LocallyIntegrable (fun x => potentialGradient b p x i) := by
  have hP : Continuous (fun x => dcoord (complexEvaluate p) x i) :=
    ((complexEvaluate_regular p).continuous_fderiv (by simp)).clm_apply continuous_const
  exact ((((primitive_continuous b hi).comp continuous_norm).mul hP).locallyIntegrable).add
    (RadialInterface.locallyIntegrable_mul_continuous _ _
      (RadialInterface.locallyIntegrable_mul_continuous _ _ hb (coordinate i).continuous)
      (complexEvaluate_regular p).continuous)

theorem potentialGradient_weak_curl_zero (b : ℝ → ℂ) (p : Poly) (S : Set ℝ) (hS : S.Countable)
    (hi : ∀ a c, IntervalIntegrable (radialDerivative b) volume a c)
    (hm : StronglyMeasurable (radialDerivative b))
    (hb : LocallyIntegrable (fun x : Space => b ‖x‖))
    (hc : ∀ r, 0 < r → r ∉ S → ContinuousAt b r)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ) :
    weakCurlPairing (potentialGradient b p) φ=0 :=
  SphericalInterfaces.gradient_curl_zero S hS (potential b p) (potentialGradient b p)
    (potential_continuous b p hi)
    (fun x hx0 hx => potential_differentiableAt b p hi hm x hx0 (hc _ (norm_pos_iff.mpr hx0) hx))
    (fun x hx0 hx i => potential_partial b p hi hm x hx0 (hc _ (norm_pos_iff.mpr hx0) hx) i)
    (potentialGradient_locallyIntegrable b p hi hb) φ hφ hcompact

def electric (a b : ℝ → ℂ) (p : Poly) : Field := fun x i =>
  a ‖x‖*dcoord (complexEvaluate p) x i+b ‖x‖*(x i : ℂ)*complexEvaluate p x
def tangentialRemainder (a b : ℝ → ℂ) (p : Poly) : Field := fun x i =>
  (a ‖x‖-primitive b ‖x‖)*dcoord (complexEvaluate p) x i

theorem electric_decomposition (a b : ℝ → ℂ) (p : Poly) (x : Space) (i : Fin 3) :
    electric a b p x i=potentialGradient b p x i+tangentialRemainder a b p x i := by
  unfold electric potentialGradient tangentialRemainder
  ring

theorem tangentialRemainder_continuous (a b : ℝ → ℂ) (p : Poly) (ha : ContinuousOn a (Ici 0))
    (hi : ∀ c d, IntervalIntegrable (radialDerivative b) volume c d) (i : Fin 3) :
    Continuous (fun x => tangentialRemainder a b p x i) :=
  ((ha.comp_continuous continuous_norm (fun x => norm_nonneg x)).sub
    ((primitive_continuous b hi).comp continuous_norm)).mul
    (((complexEvaluate_regular p).continuous_fderiv (by simp)).clm_apply continuous_const)

theorem electric_weakCurl_eq_remainder (a b : ℝ → ℂ) (p : Poly) (S : Set ℝ) (hS : S.Countable)
    (ha : ContinuousOn a (Ici 0))
    (hi : ∀ c d, IntervalIntegrable (radialDerivative b) volume c d)
    (hm : StronglyMeasurable (radialDerivative b))
    (hb : LocallyIntegrable (fun x : Space => b ‖x‖))
    (hc : ∀ r, 0 < r → r ∉ S → ContinuousAt b r)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ) :
    weakCurlPairing (electric a b p) φ=weakCurlPairing (tangentialRemainder a b p) φ := by
  have he : electric a b p=(fun x i => potentialGradient b p x i+tangentialRemainder a b p x i) :=
    funext (fun x => funext (electric_decomposition a b p x))
  rw [he,ModalWeak.weakCurlPairing_add _ _ (potentialGradient_locallyIntegrable b p hi hb)
    (fun i => (tangentialRemainder_continuous a b p ha hi i).locallyIntegrable)
    φ (hφ.of_le (by norm_num)) hcompact,
    potentialGradient_weak_curl_zero b p S hS hi hm hb hc φ hφ hcompact]
  ext i
  simp

end OQ14.RadialNormalPrimitive

#print axioms OQ14.RadialNormalPrimitive.primitive_continuous
#print axioms OQ14.RadialNormalPrimitive.primitive_hasDerivAt
#print axioms OQ14.RadialNormalPrimitive.potential_continuous
#print axioms OQ14.RadialNormalPrimitive.potential_differentiableAt
#print axioms OQ14.RadialNormalPrimitive.potential_partial
#print axioms OQ14.RadialNormalPrimitive.potentialGradient_locallyIntegrable
#print axioms OQ14.RadialNormalPrimitive.potentialGradient_weak_curl_zero
#print axioms OQ14.RadialNormalPrimitive.electric_decomposition
#print axioms OQ14.RadialNormalPrimitive.tangentialRemainder_continuous
#print axioms OQ14.RadialNormalPrimitive.electric_weakCurl_eq_remainder
