import OutgoingFiniteHelmholtz

/-! Actual continuity and angular mean-square convergence of the outgoing spatial sum. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.OutgoingAngularLimit
open MeasureTheory Filter Set OQ14.Maxwell OQ14.SphereHarmonicBasis
open OQ14.VectorHarmonicNormalization OQ14.OutgoingSpatialSeries OQ14.OutgoingGeometricTail
open scoped Topology

theorem norm_tsum_bound {ι : Type*} (f : ι → ℂ) (g : ι → ℝ) (hg : Summable g)
    (hf : ∀ a,‖f a‖≤g a) : ‖∑' a,f a‖≤∑' a,g a := by
  have hs : Summable (fun a => ‖f a‖) := Summable.of_nonneg_of_le (fun a => norm_nonneg _) hf hg
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hf hg)

theorem electric_continuousOn (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    ContinuousOn (fun x => electric y j x i) {x : Space | R≤‖x‖} := by
  apply continuousOn_tsum _ (majorant_summable b R hb)
    (fun a x hx => term_bound a b B R hb hB hscale hR hBR x y hx hy i j)
  intro a x hx
  have hx0 : x≠0 := by
    intro he
    have hn : R≤‖x‖ := hx
    rw [he,norm_zero] at hn
    linarith
  exact (OutgoingFiniteHelmholtz.term_smooth a y i j x hx0).continuousAt.continuousWithinAt

theorem weighted_ray_continuous (b B R r : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R) (hr : R≤r)
    (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    Continuous (fun n : Sphere => factor (r • (n : Space))*electric y j (r • (n : Space)) i) := by
  have he := (electric_continuousOn b B R hb hB hscale hR hBR y hy i j).comp_continuous
    (continuous_const.smul continuous_subtype_val) (fun n : Sphere => by
      change R≤‖r • (n : Space)‖
      simpa only [norm_smul,AngularPower.sphere_norm,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0≤r),mul_one] using hr)
  have hf : Continuous (fun n : Sphere => factor (r • (n : Space))) := by unfold factor;fun_prop
  exact hf.mul he

theorem weighted_ray_bound (b B R r : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R) (hr : R≤r)
    (n : Sphere) (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    ‖factor (r • (n : Space))*electric y j (r • (n : Space)) i‖≤∑' a,majorant b R a := by
  rw [weighted_sum_ray]
  exact norm_tsum_bound _ _ (majorant_summable b R hb)
    (fun a => actual_uniform_bound a b B R r hb hB hscale hR hBR hr n y hy i j)

theorem freeMap_bound (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (n : Sphere) (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    ‖FreeFarFieldExpansion.freeMap y i j n‖≤∑' a,majorant b R a := by
  rw [←(OutgoingFreeFarField.farTerm_hasSum b B R hb hB hscale hR hBR n y hy i j).tsum_eq]
  exact norm_tsum_bound _ _ (majorant_summable b R hb)
    (fun a => OutgoingFarSeries.far_bound b B R hb hB hscale hR hBR a n y hy i j)

theorem angular_mean_square_limit (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    Tendsto (fun r : ℝ => ∫ n : Sphere,
      ‖factor (r • (n : Space))*electric y j (r • (n : Space)) i-FreeFarFieldExpansion.freeMap y i j n‖^2
        ∂angularMeasure) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := angularMeasure) (l := atTop) (F := fun r : ℝ => fun n : Sphere =>
      ‖factor (r • (n : Space))*electric y j (r • (n : Space)) i-FreeFarFieldExpansion.freeMap y i j n‖^2)
    (f := fun _ => (0 : ℝ)) (fun _ => (2*(∑' a,majorant b R a))^2) ?_ ?_ (integrable_const _) ?_
  · simpa only [integral_zero] using h
  · filter_upwards [eventually_ge_atTop R] with r hr
    exact ((weighted_ray_continuous b B R r hb hB hscale hR hBR hr y hy i j).sub
      (FreeFarFieldExpansion.freeMap y i j).continuous).norm.pow 2 |>.aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop R] with r hr
    filter_upwards with n
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have he := (norm_sub_le _ _).trans (add_le_add
      (weighted_ray_bound b B R r hb hB hscale hR hBR hr n y hy i j)
      (freeMap_bound b B R hb hB hscale hR hBR n y hy i j))
    apply pow_le_pow_left₀ (norm_nonneg _) (by linarith :
      ‖factor (r • (n : Space))*electric y j (r • (n : Space)) i-FreeFarFieldExpansion.freeMap y i j n‖≤
        2*(∑' a,majorant b R a))
  · filter_upwards with n
    have h := ((OutgoingSpatialSeries.actual_free_far_limit b B R hb hB hscale hR hBR n y hy i j).sub
      (tendsto_const_nhds (x := FreeFarFieldExpansion.freeMap y i j n))).norm.pow 2
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : 2≠0)] using h

end OQ14.OutgoingAngularLimit


#print axioms OQ14.OutgoingAngularLimit.norm_tsum_bound
#print axioms OQ14.OutgoingAngularLimit.electric_continuousOn
#print axioms OQ14.OutgoingAngularLimit.weighted_ray_continuous
#print axioms OQ14.OutgoingAngularLimit.weighted_ray_bound
#print axioms OQ14.OutgoingAngularLimit.freeMap_bound
#print axioms OQ14.OutgoingAngularLimit.angular_mean_square_limit
