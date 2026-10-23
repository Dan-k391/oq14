import OutgoingAngularLimit

/-! Actual translated point dyadic and outgoing sum have vanishing difference surface mass. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PointDyadicAngularLimit
open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.SphereHarmonicBasis
open OQ14.OutgoingSpatialSeries OQ14.OutgoingGeometricTail OQ14.OutgoingAngularLimit
open scoped Topology

theorem freeMap_formula (y : Space) (n : Sphere) (i j : Fin 3) :
    FreeFarFieldExpansion.freeMap y i j n=DyadicRadiation.transverse n i j*
      (Complex.exp (-Complex.I*(@inner ℝ Space _ (n : Space) y : ℂ))/(4*Real.pi)) := by
  have hw : SphereReactionKernel.wave (-1) y n=
      Complex.exp (-Complex.I*(@inner ℝ Space _ (n : Space) y : ℂ)) := by
    unfold SphereReactionKernel.wave
    congr 1
    push_cast
    ring_nf
  have ht : DyadicRadiation.transverse (n : Space) i j=SphereReactionKernel.amplitude n i j := by
    simp only [DyadicRadiation.transverse,GreenKernel.unitCoordinate,AngularPower.sphere_norm,
      Complex.ofReal_one,div_one,SphereReactionKernel.amplitude]
  simp only [FreeFarFieldExpansion.freeMap,SphereVectorComponents.complexComponent,
    ContinuousMap.smul_apply,ContinuousMap.coe_mk,TransversePlaneFields.plane,PiLp.smul_apply,
    FreeSourceCoefficients.projected_component,hw,ht,smul_eq_mul]
  ring

theorem ray_factor (r : ℝ) (hr : 0<r) (n : Sphere) :
    factor (r • (n : Space))=MaxwellFarField.factor 1 r := by
  have hn : ‖r • (n : Space)‖=r := by
    simp only [norm_smul,AngularPower.sphere_norm,mul_one,Real.norm_eq_abs,abs_of_pos hr]
  rw [factor,hn]
  simp only [MaxwellFarField.factor,Complex.ofReal_one,mul_one]
  ring

theorem point_limit (y : Space) (n : Sphere) (i j : Fin 3) :
    Tendsto (fun r : ℝ => factor (r • (n : Space))*DyadicKernel.dyadic 1 (r • (n : Space)-y) i j)
      atTop (𝓝 (FreeFarFieldExpansion.freeMap y i j n)) := by
  have h := PointDyadicFarField.electric_limit 1 (n : Space) y (AngularPower.sphere_norm n) i j
  simp only [Complex.ofReal_one,one_pow,one_mul,mul_one,←freeMap_formula y n i j] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [ray_factor r hr n]

def pointBound (y : Space) : ℝ := 4*(‖y‖+2)/Real.pi+1/Real.pi

theorem point_bound (y : Space) (n : Sphere) (i j : Fin 3) (r : ℝ)
    (hr : 2≤r) (hy : 2*‖y‖<r) :
    ‖factor (r • (n : Space))*DyadicKernel.dyadic 1 (r • (n : Space)-y) i j‖≤pointBound y := by
  have hr0 : 0<r := by linarith
  have hn : ‖r • (n : Space)‖=r := by
    simp only [norm_smul,AngularPower.sphere_norm,mul_one,Real.norm_eq_abs,abs_of_pos hr0]
  have hE := DyadicRadiation.dyadic_source_error 1 ‖y‖ (norm_nonneg y) (r • (n : Space)) y
    (by rwa [hn]) (by rwa [hn]) (by simp only [mem_closedBall_zero_iff,le_refl]) i j
  have hP := ScalarRadiation.phi_source_bound 1 ‖y‖ (norm_nonneg y) (r • (n : Space)) y
    (by rwa [hn]) (by simp only [mem_closedBall_zero_iff,le_refl])
  simp only [Complex.ofReal_one,one_pow,one_mul,abs_one,hn] at hE
  rw [hn] at hP
  have hlead : ‖GreenKernel.phi 1 (r • (n : Space)-y)*DyadicRadiation.transverse (r • (n : Space)) i j‖≤
      (4*Real.pi)⁻¹*(2/r)*2 := by
    rw [norm_mul]
    exact mul_le_mul hP (DyadicRadiation.transverse_norm_bound _ i j) (norm_nonneg _) (by positivity)
  have hdy : ‖DyadicKernel.dyadic 1 (r • (n : Space)-y) i j‖≤
      4*(‖y‖+2)/(Real.pi*r^2)+(4*Real.pi)⁻¹*(2/r)*2 := by
    have ht := norm_add_le
      (DyadicKernel.dyadic 1 (r • (n : Space)-y) i j-
        GreenKernel.phi 1 (r • (n : Space)-y)*DyadicRadiation.transverse (r • (n : Space)) i j)
      (GreenKernel.phi 1 (r • (n : Space)-y)*DyadicRadiation.transverse (r • (n : Space)) i j)
    simp only [sub_add_cancel] at ht
    exact ht.trans ((add_le_add hE hlead).trans_eq (by ring))
  rw [norm_mul,factor_norm,hn]
  apply (mul_le_mul_of_nonneg_left hdy hr0.le).trans
  calc
    _ = (4*(‖y‖+2)/Real.pi)/r+1/Real.pi := by field_simp [hr0.ne',Real.pi_ne_zero];ring
    _ ≤ 4*(‖y‖+2)/Real.pi+1/Real.pi := add_le_add_right
      (div_le_self (by positivity) (by linarith : 1≤r)) _
    _ = pointBound y := rfl


theorem difference_angular_limit (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    Tendsto (fun r : ℝ => ∫ n : Sphere,
      ‖factor (r • (n : Space))*electric y j (r • (n : Space)) i-
        factor (r • (n : Space))*DyadicKernel.dyadic 1 (r • (n : Space)-y) i j‖^2 ∂angularMeasure)
      atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := angularMeasure) (l := atTop) (F := fun r : ℝ => fun n : Sphere =>
      ‖factor (r • (n : Space))*electric y j (r • (n : Space)) i-
        factor (r • (n : Space))*DyadicKernel.dyadic 1 (r • (n : Space)-y) i j‖^2)
    (f := fun _ => (0 : ℝ)) (fun _ => ((∑' a,majorant b R a)+pointBound y)^2) ?_ ?_ (integrable_const _) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [eventually_ge_atTop (max R (2*‖y‖+2))] with r hr
    have hrr : R≤r := (le_max_left _ _).trans hr
    have hf : Continuous (fun n : Sphere => factor (r • (n : Space))) := by unfold factor;fun_prop
    have hd : Measurable (fun n : Sphere => DyadicKernel.dyadic 1 (r • (n : Space)-y) i j) :=
      (DyadicRadiation.dyadic_measurable 1 i j).comp
        ((continuous_const.smul continuous_subtype_val).sub continuous_const).measurable
    exact ((weighted_ray_continuous b B R r hb hB hscale hR hBR hrr y hy i j).aestronglyMeasurable.sub
      (hf.measurable.mul hd).aestronglyMeasurable).norm.pow 2
  · filter_upwards [eventually_ge_atTop (max R (2*‖y‖+2))] with r hr
    have hrr : R≤r := (le_max_left _ _).trans hr
    have hyy : 2*‖y‖+2≤r := (le_max_right _ _).trans hr
    filter_upwards with n
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have he := (norm_sub_le _ _).trans (add_le_add
      (weighted_ray_bound b B R r hb hB hscale hR hBR hrr n y hy i j)
      (point_bound y n i j r (by linarith) (by linarith)))
    exact pow_le_pow_left₀ (norm_nonneg _) he 2
  · filter_upwards with n
    have h := ((OutgoingSpatialSeries.actual_free_far_limit b B R hb hB hscale hR hBR n y hy i j).sub
      (point_limit y n i j)).norm.pow 2
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : 2≠0)] using h

theorem difference_surface_mass_zero (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    Tendsto (RadialMoment.sphericalMass (fun x => electric y j x i-DyadicKernel.dyadic 1 (x-y) i j))
      atTop (𝓝 0) := by
  apply (difference_angular_limit b B R hb hB hscale hR hBR y hy i j).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  apply integral_congr_ae
  filter_upwards with n
  rw [←mul_sub,norm_mul,factor_norm]
  have hn : ‖r • (n : Space)‖=r := by
    simp only [norm_smul,AngularPower.sphere_norm,mul_one,Real.norm_eq_abs,abs_of_pos hr]
  rw [hn,mul_pow]
end OQ14.PointDyadicAngularLimit



#print axioms OQ14.PointDyadicAngularLimit.freeMap_formula
#print axioms OQ14.PointDyadicAngularLimit.ray_factor
#print axioms OQ14.PointDyadicAngularLimit.point_limit
#print axioms OQ14.PointDyadicAngularLimit.point_bound
#print axioms OQ14.PointDyadicAngularLimit.difference_angular_limit
#print axioms OQ14.PointDyadicAngularLimit.difference_surface_mass_zero
