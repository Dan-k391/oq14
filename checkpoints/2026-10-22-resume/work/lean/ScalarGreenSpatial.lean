import ScalarGreenPointwise
import NormalizedHarmonicJets

/-! The actual free Green expansion in literal homogeneous spatial polynomials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.ScalarGreenSpatial
open Complex Set OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis
  OQ14.SphereHarmonicHilbert OQ14.ScalarGreenPointwise OQ14.ScalarGreenRadialBound

theorem actual_ray_expansion (k r s : ℝ) (hk : 0 < k) (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s)
    (n m : Sphere) :
    HasSum (fun a : TotalIndex => radialFactor a.1 k (min r s) (max r s)*
      ((angular a.1 a.2 n : ℂ)*(angular a.1 a.2 m : ℂ)))
      (GreenKernel.phi k (r • (n : Space)-s • (m : Space))) := by
  rcases lt_or_gt_of_ne hne with h | h
  · simpa only [min_eq_left h.le,max_eq_right h.le] using actual_pointwise_expansion k r s hk hr h n m
  · have hh := actual_pointwise_expansion k s r hk hs h m n
    rw [← ScalarGreenMoment.phi_sub_swap k (r • (n : Space)) (s • (m : Space))] at hh
    simpa only [min_eq_right h.le,max_eq_left h.le,mul_comm] using hh

def term (a : TotalIndex) (k : ℝ) (x y : Space) : ℂ :=
  I/(k : ℂ)*RiccatiOriginSeries.origin a.1 ((k*min ‖x‖ ‖y‖ : ℝ) : ℂ)*
    ModalAlgebra.xi a.1 ((k*max ‖x‖ ‖y‖ : ℝ) : ℂ)/
    ((‖x‖ : ℂ)^(a.1+1)*(‖y‖ : ℂ)^(a.1+1))*
    complexEvaluate (representative a.1 a.2) x*complexEvaluate (representative a.1 a.2) y

theorem term_on_rays (a : TotalIndex) (k r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n m : Sphere) :
    term a k (r • (n : Space)) (s • (m : Space))=
      radialFactor a.1 k (min r s) (max r s)*
        ((angular a.1 a.2 n : ℂ)*(angular a.1 a.2 m : ℂ)) := by
  by_cases hk : k=0
  · simp only [term,radialFactor,hk,ofReal_zero,div_zero,zero_mul,mul_zero,zero_div]
  have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  simp only [term,source_ray_norm r hr n,source_ray_norm s hs m]
  rw [FischerDecomposition.complexEvaluate_smul _ _ (representative_homogeneous a.1 a.2) r,
    FischerDecomposition.complexEvaluate_smul _ _ (representative_homogeneous a.1 a.2) s]
  simp only [radialFactor,angular,SpherePolynomial.polynomialMap_apply,complexEvaluate,evaluate]
  rcases le_total r s with h | h
  · rw [min_eq_left h,max_eq_right h]
    simp only [pow_succ]
    field_simp [hk0,hr0,hs0]
    ring
  · rw [min_eq_right h,max_eq_left h]
    simp only [pow_succ]
    field_simp [hk0,hr0,hs0]
    ring

theorem actual_spatial_expansion (k : ℝ) (hk : 0 < k) (x y : Space)
    (hx : x ≠ 0) (hy : y ≠ 0) (hne : ‖x‖ ≠ ‖y‖) :
    HasSum (fun a : TotalIndex => term a k x y) (GreenKernel.phi k (x-y)) := by
  obtain ⟨r,n,_,hr,hrep⟩ := NormalizedHarmonicJets.radius_unit_representation x
  obtain ⟨s,m,_,hs,hsrep⟩ := NormalizedHarmonicJets.radius_unit_representation y
  have hrp : 0 < r := hr.symm ▸ norm_pos_iff.mpr hx
  have hsp : 0 < s := hs.symm ▸ norm_pos_iff.mpr hy
  have hne' : r ≠ s := by simpa only [hr,hs] using hne
  rw [hrep,hsrep]
  simpa only [term_on_rays _ k r s hrp hsp n m] using actual_ray_expansion k r s hk hrp hsp hne' n m

end OQ14.ScalarGreenSpatial

#print axioms OQ14.ScalarGreenSpatial.actual_ray_expansion

#print axioms OQ14.ScalarGreenSpatial.term_on_rays

#print axioms OQ14.ScalarGreenSpatial.actual_spatial_expansion
