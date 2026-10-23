import FreeFarFieldExpansion

/-! Pointwise genuine free-dyadic amplitude of the actual infinite outgoing source series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.OutgoingFreeFarField
open MeasureTheory Filter OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open OQ14.SphereVectorComponents OQ14.FreeFarFieldExpansion OQ14.OutgoingFarSeries OQ14.OutgoingGeometricTail
open scoped Topology

theorem poloidal_component (a : PositiveIndex) (n : Sphere) (i : Fin 3) :
    realComponent (VectorHarmonicBasisSpan.poloidalField ⟨a.1+1,a.2⟩) i n=
      HarmonicRadiationFactors.poloidal (representative (a.1+1) a.2) n i := by
  change ((restriction (AngularHarmonicEnergy.tangential (representative (a.1+1) a.2) (a.1+1)) n) i : ℂ)=_
  rw [restriction_poloidal_component,HarmonicRadiationFactors.poloidal_formula _ (a.1+1)
    (representative_homogeneous (a.1+1) a.2)]
  dsimp [DebyeRadialTrace.angularPoloidal,HarmonicRadiationFactors.radial]
  ring

theorem toroidal_component (a : PositiveIndex) (n : Sphere) (i : Fin 3) :
    realComponent (VectorHarmonicBasisSpan.toroidalField ⟨a.1+1,a.2⟩) i n=
      DebyeRadialTrace.angularToroidal (representative (a.1+1) a.2) n i :=
  restriction_toroidal_component _ n i

theorem farMap_apply (a : PositiveIndex) (n : Sphere) (y : Space) (i j : Fin 3) :
    farMap a y i j n=farTerm a n y i j := by
  simp only [farMap,ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul,
    poloidal_component,toroidal_component,farTerm]

theorem farMap_summable (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) : Summable (fun a : PositiveIndex => farMap a y i j) := by
  apply Summable.of_norm_bounded (OutgoingGeometricTail.majorant b R) (majorant_summable b R hb)
  intro a
  have hC := prefactor_nonnegative b R hb
  have hbound : 0≤OutgoingGeometricTail.majorant b R a := by dsimp [OutgoingGeometricTail.majorant];positivity
  rw [(farMap a y i j).norm_le hbound]
  intro n
  rw [farMap_apply]
  exact far_bound b B R hb hB hscale hR hBR a n y hy i j

theorem continuous_expansion (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    HasSum (fun a : PositiveIndex => farMap a y i j) (freeMap y i j) :=
  ContinuousMap.hasSum_of_hasSum_Lp (p := 2) (μ := angularMeasure) (𝕜 := ℂ)
    (farMap_summable b B R hb hB hscale hR hBR y hy i j) (Lp_expansion y i j)

theorem farTerm_hasSum (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (n : Sphere) (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    HasSum (fun a : PositiveIndex => farTerm a n y i j) (freeMap y i j n) := by
  have h := (continuous_expansion b B R hb hB hscale hR hBR y hy i j).mapL (ContinuousMap.evalCLM ℂ n)
  simpa only [ContinuousMap.evalCLM_apply,farMap_apply] using h

theorem actual_free_far_limit (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (n : Sphere) (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    Tendsto (fun r : ℝ => ∑' a : PositiveIndex,
      (OutgoingDyadBounds.tmWeighted a r n y i j+OutgoingDyadBounds.teWeighted a r n y i j)) atTop
      (𝓝 (freeMap y i j n)) := by
  have h := actual_series_limit b B R hb hB hscale hR hBR n y hy i j
  rwa [(farTerm_hasSum b B R hb hB hscale hR hBR n y hy i j).tsum_eq] at h

end OQ14.OutgoingFreeFarField

#print axioms OQ14.OutgoingFreeFarField.poloidal_component
#print axioms OQ14.OutgoingFreeFarField.toroidal_component
#print axioms OQ14.OutgoingFreeFarField.farMap_apply
#print axioms OQ14.OutgoingFreeFarField.farMap_summable
#print axioms OQ14.OutgoingFreeFarField.continuous_expansion
#print axioms OQ14.OutgoingFreeFarField.farTerm_hasSum
#print axioms OQ14.OutgoingFreeFarField.actual_free_far_limit
