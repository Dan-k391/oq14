import OutgoingGeometricTail

/-! Genuine far-field limit interchange for the actual signed outgoing vacuum series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.OutgoingFarSeries
open Complex Filter OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open OQ14.FreeSourceCoefficients OQ14.OutgoingDyadBounds OQ14.OutgoingGeometricTail
open scoped Topology

def farTerm (a : PositiveIndex) (n : Sphere) (y : Space) (i j : Fin 3) : ℂ :=
  tmCoefficient a y j*SourceRadiation.phase (a.1+1)*
      HarmonicRadiationFactors.poloidal (representative (a.1+1) a.2) n i+
    teCoefficient a y j*(-SourceRadiation.phase (a.1+1))*
      DebyeRadialTrace.angularToroidal (representative (a.1+1) a.2) n i

theorem actual_term_limit (a : PositiveIndex) (n : Sphere) (y : Space) (i j : Fin 3) :
    Tendsto (fun r : ℝ => tmWeighted a r n y i j+teWeighted a r n y i j) atTop
      (𝓝 (farTerm a n y i j)) := by
  have ht := vacuum_tm_far (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2)
    (representative_homogeneous (a.1+1) a.2) n
  have he := vacuum_te_far (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2)
    (representative_homogeneous (a.1+1) a.2) n
  have ht' := (((continuous_apply i).tendsto _).comp ht).const_mul (tmCoefficient a y j)
  have he' := (((continuous_apply i).tendsto _).comp he).const_mul (teCoefficient a y j)
  simpa only [tmWeighted,teWeighted,farTerm,Pi.smul_apply,smul_eq_mul,mul_assoc] using ht'.add he'

theorem far_bound (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (a : PositiveIndex) (n : Sphere) (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    ‖farTerm a n y i j‖≤majorant b R a := by
  apply le_of_tendsto (actual_term_limit a n y i j).norm
  filter_upwards [eventually_ge_atTop R] with r hr
  exact actual_uniform_bound a b B R r hb hB hscale hR hBR hr n y hy i j

theorem far_summable (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (n : Sphere) (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    Summable (fun a : PositiveIndex => farTerm a n y i j) :=
  Summable.of_norm_bounded (majorant b R) (majorant_summable b R hb)
    (fun a => far_bound b B R hb hB hscale hR hBR a n y hy i j)

theorem actual_series_limit (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (n : Sphere) (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    Tendsto (fun r : ℝ => ∑' a : PositiveIndex,
      (tmWeighted a r n y i j+teWeighted a r n y i j)) atTop
      (𝓝 (∑' a : PositiveIndex,farTerm a n y i j)) := by
  apply tendsto_tsum_of_dominated_convergence
    (f := fun r a => tmWeighted a r n y i j+teWeighted a r n y i j)
    (g := fun a => farTerm a n y i j) (majorant_summable b R hb)
    (fun a => actual_term_limit a n y i j)
  filter_upwards [eventually_ge_atTop R] with r hr
  intro a
  exact actual_uniform_bound a b B R r hb hB hscale hR hBR hr n y hy i j

end OQ14.OutgoingFarSeries

#print axioms OQ14.OutgoingFarSeries.actual_term_limit
#print axioms OQ14.OutgoingFarSeries.far_bound
#print axioms OQ14.OutgoingFarSeries.far_summable
#print axioms OQ14.OutgoingFarSeries.actual_series_limit
