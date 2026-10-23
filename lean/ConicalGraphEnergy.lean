import ConicalGraphProjection
import PolarMomentEnergy

/-! Actual finite radial energy and local integrability for a genuine weak-gradient graph. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ConicalGraphEnergy
open MeasureTheory Set Filter OQ14.ConicalStaticVolume OQ14.ConicalGradientGraph
  OQ14.ConicalGraphMoments OQ14.ConicalGraphProjection OQ14.PolarMomentTesting OQ14.AngularPower
open scoped Topology

theorem tangent_weight_memLp (p : Data) (i : Fin 3) :
    MemLp (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) 2 angularMeasure := by
  obtain ⟨C,hC,hb⟩ := ConicalMomentWeights.tangent_bound _ _ _ p.eigenvalue_bounds
    p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
  exact MemLp.of_bound (ConicalMomentWeights.tangent_measurable _ _ _ p.eigenvalue_bounds
    p.threshold_pos p.threshold_lt_one i).aestronglyMeasurable C (Filter.Eventually.of_forall hb)

theorem projected_memLp (p : Data) (g : Graph) :
    MemLp (projected p g) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hi (i : Fin 3) := PolarMomentEnergy.radial_moment_memLp (g.gradient i)
    (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i)
    (ConicalMomentWeights.tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i)
    (tangent_weight_memLp p i)
  have hs := memLp_finset_sum Finset.univ (fun i _ => hi i)
  convert hs.const_mul (p.eigenvalue : ℂ)⁻¹ using 1
  ext r
  simp only [projected,tangentMoment,div_eq_mul_inv,Finset.mul_sum]
  ring_nf

private theorem moment_locallyIntegrableOn (f : OQ14.PolarMomentEnergy.ScalarL2)
    (σ : Sphere → ℂ) (hσ : Measurable σ) (C : ℝ) (hC : ∀ n, ‖σ n‖ ≤ C) :
    LocallyIntegrableOn (moment f σ) (Ioi (0 : ℝ)) := by
  intro r hr
  change 0 < r at hr
  refine ⟨Ioo (r/2) (r+1), mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith [hr]) (by linarith)), ?_⟩
  exact moment_integrableOn_annulus f (Lp.memLp f) σ hσ C hC _ _ (by linarith [hr])

theorem radialMoment_locallyIntegrableOn (p : Data) (g : Graph) :
    LocallyIntegrableOn (radialMoment p g) (Ioi (0 : ℝ)) := by
  have hi (i : Fin 3) : LocallyIntegrableOn
      (moment (g.gradient i) (ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold i)) (Ioi (0 : ℝ)) := by
    obtain ⟨C,hC,hb⟩ := ConicalMomentWeights.radial_bound _ _ _ p.eigenvalue_bounds
      p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact moment_locallyIntegrableOn _ _ (ConicalMomentWeights.radial_measurable _ _ _ p.eigenvalue_bounds
      p.threshold_pos p.threshold_lt_one i) C hb
  have he : radialMoment p g=(moment (g.gradient 0) (ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold 0)+
      moment (g.gradient 1) (ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold 1)+
      moment (g.gradient 2) (ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold 2)) := by
    ext r
    simp only [radialMoment,Fin.sum_univ_three,Pi.add_apply]
  rw [he]
  exact ((hi 0).add (hi 1)).add (hi 2)

theorem projected_locallyIntegrableOn (p : Data) (g : Graph) :
    LocallyIntegrableOn (projected p g) (Ioi (0 : ℝ)) :=
  locallyIntegrableOn_of_locallyIntegrable_restrict ((projected_memLp p g).locallyIntegrable (by norm_num))

end OQ14.ConicalGraphEnergy

#print axioms OQ14.ConicalGraphEnergy.tangent_weight_memLp
#print axioms OQ14.ConicalGraphEnergy.projected_memLp
#print axioms OQ14.ConicalGraphEnergy.radialMoment_locallyIntegrableOn
#print axioms OQ14.ConicalGraphEnergy.projected_locallyIntegrableOn
