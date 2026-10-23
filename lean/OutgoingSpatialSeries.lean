import OutgoingFreeFarField

/-! The genuine unweighted outgoing spatial series and its uniform exterior convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.OutgoingSpatialSeries
open MeasureTheory Filter OQ14.Maxwell OQ14.SphereHarmonicBasis
open OQ14.OutgoingDyadBounds OQ14.OutgoingGeometricTail OQ14.VectorHarmonicNormalization
open scoped Topology

def factor (x : Space) : ℂ := Complex.exp (-Complex.I*(‖x‖ : ℂ))*(‖x‖ : ℂ)

def term (a : PositiveIndex) (x y : Space) (i j : Fin 3) : ℂ :=
  FreeSourceCoefficients.tmCoefficient a y j*SourceUnclippedMaxwell.electric
      (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i+
    FreeSourceCoefficients.teCoefficient a y j*SourceUnclippedMaxwell.magnetic
      (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i

def electric (y : Space) (j : Fin 3) : Field := fun x i => ∑' a : PositiveIndex,term a x y i j

def direction (x : Space) (hx : x≠0) : Sphere := ⟨‖x‖⁻¹ • x,by
  simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
    abs_inv,abs_of_nonneg (norm_nonneg x),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

theorem direction_ray (x : Space) (hx : x≠0) : ‖x‖ • (direction x hx : Space)=x := by
  change ‖x‖ • (‖x‖⁻¹ • x)=x
  rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx),one_smul]

theorem factor_norm (x : Space) : ‖factor x‖=‖x‖ := by
  simp [factor,norm_mul,Complex.norm_exp]

theorem weighted_term (a : PositiveIndex) (r : ℝ) (n : Sphere) (y : Space) (i j : Fin 3) :
    factor (r • (n : Space))*term a (r • (n : Space)) y i j=
      tmWeighted a r n y i j+teWeighted a r n y i j := by
  simp only [term,tmWeighted,teWeighted,SourceFarAmplitude.electricWeighted,
    SourceFarAmplitude.magneticWeighted,Pi.smul_apply,smul_eq_mul,factor]
  ring

theorem term_bound (a : PositiveIndex) (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (x y : Space) (hx : R≤‖x‖) (hy : ‖y‖≤b) (i j : Fin 3) :
    ‖term a x y i j‖≤majorant b R a := by
  have hx0 : x≠0 := by intro he; simp only [he,norm_zero] at hx;linarith
  have h := actual_uniform_bound a b B R ‖x‖ hb hB hscale hR hBR hx (direction x hx0) y hy i j
  rw [←weighted_term,direction_ray,norm_mul,factor_norm] at h
  exact (le_mul_of_one_le_left (norm_nonneg _) (by linarith : 1≤‖x‖)).trans h

theorem term_summable (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (x y : Space) (hx : R≤‖x‖) (hy : ‖y‖≤b) (i j : Fin 3) :
    Summable (fun a : PositiveIndex => term a x y i j) :=
  Summable.of_norm_bounded (majorant b R) (majorant_summable b R hb)
    (fun a => term_bound a b B R hb hB hscale hR hBR x y hx hy i j)

theorem spatial_uniform_series (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R) (i j : Fin 3) :
    TendstoUniformlyOn
      (fun s : Finset PositiveIndex => fun p : Space × Space => ∑ a∈s,term a p.1 p.2 i j)
      (fun p : Space × Space => electric p.2 j p.1 i) atTop
      {p : Space × Space | R≤‖p.1‖ ∧ ‖p.2‖≤b} :=
  tendstoUniformlyOn_tsum (majorant_summable b R hb) (fun a (p : Space × Space) hp =>
    term_bound a b B R hb hB hscale hR hBR p.1 p.2 hp.1 hp.2 i j)

theorem weighted_sum_ray (r : ℝ) (n : Sphere) (y : Space) (i j : Fin 3) :
    factor (r • (n : Space))*electric y j (r • (n : Space)) i=
      ∑' a : PositiveIndex,(tmWeighted a r n y i j+teWeighted a r n y i j) := by
  rw [electric,←tsum_mul_left]
  congr 1
  funext a
  exact weighted_term a r n y i j

theorem actual_free_far_limit (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (n : Sphere) (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    Tendsto (fun r : ℝ => factor (r • (n : Space))*electric y j (r • (n : Space)) i) atTop
      (𝓝 (FreeFarFieldExpansion.freeMap y i j n)) := by
  apply (OutgoingFreeFarField.actual_free_far_limit b B R hb hB hscale hR hBR n y hy i j).congr'
  apply Filter.Eventually.of_forall
  intro r
  exact (weighted_sum_ray r n y i j).symm

end OQ14.OutgoingSpatialSeries


#print axioms OQ14.OutgoingSpatialSeries.direction_ray
#print axioms OQ14.OutgoingSpatialSeries.factor_norm
#print axioms OQ14.OutgoingSpatialSeries.weighted_term
#print axioms OQ14.OutgoingSpatialSeries.term_bound
#print axioms OQ14.OutgoingSpatialSeries.term_summable
#print axioms OQ14.OutgoingSpatialSeries.spatial_uniform_series
#print axioms OQ14.OutgoingSpatialSeries.weighted_sum_ray
#print axioms OQ14.OutgoingSpatialSeries.actual_free_far_limit
