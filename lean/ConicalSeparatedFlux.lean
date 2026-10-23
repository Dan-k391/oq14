import ConicalSeparatedCorrection
import PolarMomentAE

/-! Actual Maxwell radial flux equation obtained from the angular Gauss test. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ConicalSeparatedFlux
open MeasureTheory Set OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalSeparatedCorrection
  OQ14.ConicalMomentWeights OQ14.PolarMomentTesting
open scoped Topology
abbrev Space := Maxwell.Space

def flux (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (r : ℝ) : ℂ := (r^2 : ℂ)*
  ∑ i : Fin 3, moment (totalCoordinate p a k hai i) (radial p.eigenvalue p.contrast p.threshold i) r

def tangentTotal (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (r : ℝ) : ℂ :=
  ∑ i : Fin 3, moment (totalCoordinate p a k hai i) (tangent p.eigenvalue p.contrast p.threshold i) r

private theorem weighted_angularDerivative (p : Data) (η : ℝ → ℂ) (x : Space) (i : Fin 3) :
    (ConicalSeparatedGauss.epsilon p x : ℂ)*ConicalAnnularTests.angularDerivative p.eigenvalue p.threshold η x i=
    radial p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*deriv η ‖x‖+
      tangent p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*ConicalAnnularTests.radialWeight 1 η ‖x‖ := by
  rw [radial,scalar_unit,tangent_unit]
  simp only [ConicalAnnularTests.angularDerivative,ConicalSeparatedGauss.epsilon,
    ConicalRadialDivergence.spatialWeight,ConicalTangentialDivergence.weightedTangent,
    ConicalAnnularTests.radialWeight,PiLp.smul_apply,smul_eq_mul,Real.rpow_neg_one,
    Complex.ofReal_mul,Complex.ofReal_inv]
  ring

private theorem radial_weight_continuous (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (h0 : 0 ∉ tsupport η) : Continuous (ConicalAnnularTests.radialWeight 1 η) :=
  (ConicalAnnularTests.radialWeight_smooth 1 η hη h0).continuous

private theorem radial_weight_compact (η : ℝ → ℂ) (hc : HasCompactSupport η) :
    HasCompactSupport (ConicalAnnularTests.radialWeight 1 η) := hc.mul_left

theorem flux_weak (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (ha : 0 ≤ a) (hk0 : k≠0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) a) :
    (∫ r in Ioi (0 : ℝ), deriv η r*flux p a k hai r)+
      (∫ r in Ioi (0 : ℝ), (r : ℂ)*η r*tangentTotal p a k hai r)=0 := by
  have h0 : 0 ∉ tsupport η := fun h => (hs h).1.false
  have hδ : Continuous (deriv η) := hη.continuous_deriv (by simp)
  have hτ := radial_weight_continuous η hη h0
  have hcτ := radial_weight_compact η hc
  have hR (i : Fin 3) : Integrable (fun x : Space => totalCoordinate p a k hai i x*
      radial p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*deriv η ‖x‖) := by
    obtain ⟨C,_,hb⟩ := radial_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact weighted_spatial_integrable _ (Lp.memLp _) _
      (radial_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb _ hδ hc.deriv
  have hT (i : Fin 3) : Integrable (fun x : Space => totalCoordinate p a k hai i x*
      tangent p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*ConicalAnnularTests.radialWeight 1 η ‖x‖) := by
    obtain ⟨C,_,hb⟩ := tangent_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact weighted_spatial_integrable _ (Lp.memLp _) _
      (tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb _ hτ hcτ
  have hpair (i : Fin 3) : (∫ x : Space, (ConicalSeparatedGauss.epsilon p x : ℂ)*totalCoordinate p a k hai i x*
      ConicalAnnularTests.angularDerivative p.eigenvalue p.threshold η x i)=
      (∫ x : Space, totalCoordinate p a k hai i x*radial p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*deriv η ‖x‖)+
      (∫ x : Space, totalCoordinate p a k hai i x*tangent p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*ConicalAnnularTests.radialWeight 1 η ‖x‖) := by
    rw [← integral_add (hR i) (hT i)]
    apply integral_congr_ae
    filter_upwards with x
    linear_combination totalCoordinate p a k hai i x*weighted_angularDerivative p η x i
  have hpolR (i : Fin 3) : (∫ x : Space, totalCoordinate p a k hai i x*radial p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*(deriv η) ‖x‖)=
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(deriv η) r*moment (totalCoordinate p a k hai i) (radial p.eigenvalue p.contrast p.threshold i) r := by
    obtain ⟨C,_,hb⟩ := radial_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact integral_weighted_moment (totalCoordinate p a k hai i) (Lp.memLp _) _
      (radial_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb _ hδ hc.deriv
  have hpolT (i : Fin 3) : (∫ x : Space, totalCoordinate p a k hai i x*tangent p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*(ConicalAnnularTests.radialWeight 1 η) ‖x‖)=
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(ConicalAnnularTests.radialWeight 1 η) r*moment (totalCoordinate p a k hai i) (tangent p.eigenvalue p.contrast p.threshold i) r := by
    obtain ⟨C,_,hb⟩ := tangent_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact integral_weighted_moment (totalCoordinate p a k hai i) (Lp.memLp _) _
      (tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb _ hτ hcτ
  have hiR (i : Fin 3) : IntegrableOn (fun r : ℝ => (r^2 : ℂ)*(deriv η) r*moment (totalCoordinate p a k hai i) (radial p.eigenvalue p.contrast p.threshold i) r) (Ioi (0 : ℝ)) := by
    obtain ⟨C,_,hb⟩ := radial_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact integrable_weighted_moment (totalCoordinate p a k hai i) (Lp.memLp _) _
      (radial_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb _ hδ hc.deriv
  have hiT (i : Fin 3) : IntegrableOn (fun r : ℝ => (r^2 : ℂ)*(ConicalAnnularTests.radialWeight 1 η) r*moment (totalCoordinate p a k hai i) (tangent p.eigenvalue p.contrast p.threshold i) r) (Ioi (0 : ℝ)) := by
    obtain ⟨C,_,hb⟩ := tangent_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact integrable_weighted_moment (totalCoordinate p a k hai i) (Lp.memLp _) _
      (tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb _ hτ hcτ
  have hh := actual_gauss_pairing p a k hai ha hk0 hk η hη hc hs
  simp only [hpair,hpolR,hpolT,Finset.sum_add_distrib] at hh
  have hsumR : (∫ r in Ioi (0 : ℝ), deriv η r*flux p a k hai r)=
      ∑ i : Fin 3, ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*deriv η r*moment (totalCoordinate p a k hai i) (radial p.eigenvalue p.contrast p.threshold i) r := by
    rw [← integral_finset_sum _ (fun i _ => hiR i)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    simp only [flux,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsumT : (∫ r in Ioi (0 : ℝ), (r : ℂ)*η r*tangentTotal p a k hai r)=
      ∑ i : Fin 3, ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*ConicalAnnularTests.radialWeight 1 η r*moment (totalCoordinate p a k hai i) (tangent p.eigenvalue p.contrast p.threshold i) r := by
    rw [← integral_finset_sum _ (fun i _ => hiT i)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [← Finset.mul_sum,tangentTotal,ConicalAnnularTests.radialWeight,Real.rpow_neg_one,Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr (show r≠0 from (show 0 < r from hr).ne')]
    ring
  rw [hsumR,hsumT]
  exact hh

private theorem totalMoment_ae (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (σ : Fin 3 → AngularPower.Sphere → ℂ)
    (hσ : ∀ i, MemLp (σ i) 2 AngularPower.angularMeasure) :
    (fun r => ∑ i : Fin 3, moment (totalCoordinate p a k hai i) (σ i) r) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun r => (∑ i : Fin 3, moment ((ConicalGradientGraph.separated p a k hai).gradient i) (σ i) r)+
        ∑ i : Fin 3, moment (cutCorrection p a k i) (σ i) r := by
  have hi (i : Fin 3) : moment (totalCoordinate p a k hai i) (σ i) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun r => moment ((ConicalGradientGraph.separated p a k hai).gradient i) (σ i) r+moment (cutCorrection p a k i) (σ i) r := by
    filter_upwards [PolarMomentAE.moment_congr (Lp.coeFn_add ((ConicalGradientGraph.separated p a k hai).gradient i) (correctionL2 p a k hai i)) (σ i),
      PolarMomentAE.moment_add ((ConicalGradientGraph.separated p a k hai).gradient i) (correctionL2 p a k hai i) (σ i) (hσ i),
      PolarMomentAE.moment_congr (correctionL2_ae p a k hai i) (σ i)] with r hs ha hc
    exact hs.trans (ha.trans (congrArg (fun z : ℂ => moment ((ConicalGradientGraph.separated p a k hai).gradient i) (σ i) r+z) hc))
  filter_upwards [ae_all_iff.mpr hi] with r hr
  simp only [hr,Finset.sum_add_distrib]

theorem tangentTotal_ae (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) :
    tangentTotal p a k hai =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r =>
      ConicalGraphMoments.tangentMoment p (ConicalGradientGraph.separated p a k hai) r+tangentCorrection p a k r :=
  totalMoment_ae p a k hai _ (ConicalGraphEnergy.tangent_weight_memLp p)

theorem flux_ae (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) :
    flux p a k hai =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => (r^2 : ℂ)*
      (ConicalGraphMoments.radialMoment p (ConicalGradientGraph.separated p a k hai) r+radialCorrection p a k r) := by
  have hi (i : Fin 3) : MemLp (radial p.eigenvalue p.contrast p.threshold i) 2 AngularPower.angularMeasure := by
    obtain ⟨C,_,hb⟩ := radial_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact MemLp.of_bound (radial_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i).aestronglyMeasurable
      C (Filter.Eventually.of_forall hb)
  filter_upwards [totalMoment_ae p a k hai _ hi] with r hr
  exact congrArg (fun z : ℂ => (r^2 : ℂ)*z) hr

theorem flux_weak_forced (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (ha : 0 ≤ a) (hk0 : k≠0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) a) :
    (∫ r in Ioi (0 : ℝ), deriv η r*flux p a k hai r)+
      (∫ r in Ioi (0 : ℝ), η r*((p.eigenvalue : ℂ)*ConicalGraphProjection.projected p (ConicalGradientGraph.separated p a k hai) r+
        (r : ℂ)*tangentCorrection p a k r))=0 := by
  have hh := flux_weak p a k hai ha hk0 hk η hη hc hs
  have he : (∫ r in Ioi (0 : ℝ), (r : ℂ)*η r*tangentTotal p a k hai r)=
      ∫ r in Ioi (0 : ℝ), η r*((p.eigenvalue : ℂ)*ConicalGraphProjection.projected p (ConicalGradientGraph.separated p a k hai) r+
        (r : ℂ)*tangentCorrection p a k r) := by
    apply integral_congr_ae
    filter_upwards [tangentTotal_ae p a k hai] with r hr
    rw [hr]
    dsimp only [ConicalGraphProjection.projected]
    field_simp [Complex.ofReal_ne_zero.mpr (ConicalGraphProjection.eigenvalue_pos p).ne']
    ring
  rwa [he] at hh

theorem projected_weak_forced (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (η : ℝ → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) (h0 : 0 ∉ tsupport η) :
    (∫ r in Ioi (0 : ℝ), (η r : ℂ)*(flux p a k hai r/(r^2 : ℂ)-radialCorrection p a k r))+
      (∫ r in Ioi (0 : ℝ), ((deriv η r : ℝ) : ℂ)*ConicalGraphProjection.projected p (ConicalGradientGraph.separated p a k hai) r)=0 := by
  have he : (∫ r in Ioi (0 : ℝ), (η r : ℂ)*(flux p a k hai r/(r^2 : ℂ)-radialCorrection p a k r))=
      ∫ r in Ioi (0 : ℝ), (η r : ℂ)*ConicalGraphMoments.radialMoment p (ConicalGradientGraph.separated p a k hai) r := by
    apply integral_congr_ae
    filter_upwards [flux_ae p a k hai,ae_restrict_mem measurableSet_Ioi] with r hr hp
    rw [hr]
    field_simp [Complex.ofReal_ne_zero.mpr (show r≠0 from (show 0 < r from hp).ne')]
  rw [he]
  exact ConicalGraphProjection.projected_weak_derivative p (ConicalGradientGraph.separated p a k hai) η hη hc h0

theorem flux_locallyIntegrableOn (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) :
    LocallyIntegrableOn (flux p a k hai) (Ioi (0 : ℝ)) := by
  intro r hr
  change 0 < r at hr
  have hi (i : Fin 3) : IntegrableOn (fun s : ℝ => (s^2 : ℂ)*
      moment (totalCoordinate p a k hai i) (radial p.eigenvalue p.contrast p.threshold i) s) (Ioo (0 : ℝ) (r+1)) := by
    obtain ⟨C,_,hb⟩ := radial_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact weighted_moment_integrableOn _ (Lp.memLp _) _
      (radial_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb (r+1)
  refine ⟨Ioo 0 (r+1),mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hr (by linarith)),?_⟩
  have he : flux p a k hai=(fun s : ℝ => (s^2 : ℂ)*moment (totalCoordinate p a k hai 0) (radial p.eigenvalue p.contrast p.threshold 0) s+
      (s^2 : ℂ)*moment (totalCoordinate p a k hai 1) (radial p.eigenvalue p.contrast p.threshold 1) s+
      (s^2 : ℂ)*moment (totalCoordinate p a k hai 2) (radial p.eigenvalue p.contrast p.threshold 2) s) := by
    ext s
    simp only [flux,Fin.sum_univ_three,mul_add]
  rw [he]
  exact ((hi 0).add (hi 1)).add (hi 2)

theorem forcing_locallyIntegrableOn (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) : LocallyIntegrableOn
    (fun r : ℝ => (p.eigenvalue : ℂ)*ConicalGraphProjection.projected p (ConicalGradientGraph.separated p a k hai) r+(r : ℂ)*tangentCorrection p a k r)
    (Ioi (0 : ℝ)) := by
  have hu := (ConicalGraphEnergy.projected_locallyIntegrableOn p (ConicalGradientGraph.separated p a k hai)).continuousOn_mul
    (g := fun _ => (p.eigenvalue : ℂ)) continuousOn_const isOpen_Ioi.isLocallyClosed
  have hb := ((Complex.continuous_ofReal).mul (tangentCorrection_continuous p a k hai)).continuousOn.locallyIntegrableOn
    (μ := volume) (K := Ioi (0 : ℝ)) measurableSet_Ioi
  exact hu.add hb

theorem projected_forcing_locallyIntegrableOn (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) : LocallyIntegrableOn
    (fun r : ℝ => flux p a k hai r/(r^2 : ℂ)-radialCorrection p a k r) (Ioi (0 : ℝ)) := by
  have hi : ContinuousOn (fun r : ℝ => ((r^2 : ℂ))⁻¹) (Ioi (0 : ℝ)) :=
    (Complex.continuous_ofReal.pow 2).continuousOn.inv₀ (fun r hr =>
      pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (show r≠0 from (show 0 < r from hr).ne')))
  have hf := (flux_locallyIntegrableOn p a k hai).mul_continuousOn hi isOpen_Ioi.isLocallyClosed
  have ha := (radialCorrection_continuous p a k hai).continuousOn.locallyIntegrableOn (μ := volume)
    (K := Ioi (0 : ℝ)) measurableSet_Ioi
  simpa only [div_eq_mul_inv] using hf.sub ha

end OQ14.ConicalSeparatedFlux




#print axioms OQ14.ConicalSeparatedFlux.flux_weak
#print axioms OQ14.ConicalSeparatedFlux.tangentTotal_ae
#print axioms OQ14.ConicalSeparatedFlux.flux_ae
#print axioms OQ14.ConicalSeparatedFlux.flux_weak_forced
#print axioms OQ14.ConicalSeparatedFlux.projected_weak_forced
#print axioms OQ14.ConicalSeparatedFlux.flux_locallyIntegrableOn
#print axioms OQ14.ConicalSeparatedFlux.forcing_locallyIntegrableOn
#print axioms OQ14.ConicalSeparatedFlux.projected_forcing_locallyIntegrableOn
