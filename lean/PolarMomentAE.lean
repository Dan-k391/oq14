import PolarMomentEnergy

/-! Actual transfer of almost-everywhere spatial identities to radial angular moments. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.PolarMomentAE
open MeasureTheory Set Filter OQ14.Maxwell OQ14.AngularPower OQ14.PolarIntegration OQ14.PolarMomentTesting
open scoped Topology

theorem polar_ae {P : Space → Prop} (hP : ∀ᵐ x : Space, P x) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ᵐ n : Sphere ∂angularMeasure, P (r • (n : Space)) := by
  have hq : ∀ᵐ x : Punctured ∂volume.comap ((↑) : Punctured → Space), P x :=
    (ae_restrict_iff_subtype (measurableSet_singleton (0 : Space)).compl).mp (ae_restrict_of_ae hP)
  have hp : ∀ᵐ p : Sphere × Radius ∂angularMeasure.prod radialMeasure, P ((p.2 : ℝ) • (p.1 : Space)) := by
    rw [← polar_measurePreserving.map_eq]
    apply (homeomorphUnitSphereProd Space).measurableEmbedding.ae_map_iff.mpr
    simpa only [← homeomorphUnitSphereProd_symm_apply_coe,Homeomorph.symm_apply_apply] using hq
  have hs := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hp)
  have hd : Measurable (fun r : Radius => ENNReal.ofReal ((r : ℝ)^2)) :=
    ENNReal.measurable_ofReal.comp (measurable_subtype_coe.pow_const 2)
  have hb : ∀ᵐ r : Radius ∂(volume.comap ((↑) : Radius → ℝ)), ∀ᵐ n : Sphere ∂angularMeasure, P ((r : ℝ) • (n : Space)) := by
    have hh := (ae_withDensity_iff hd).mp hs
    filter_upwards [hh] with r hr
    exact hr (ENNReal.ofReal_pos.mpr (sq_pos_of_pos r.property)).ne'
  exact (ae_restrict_iff_subtype measurableSet_Ioi).mpr hb

theorem moment_congr {f g : Space → ℂ} (hfg : f =ᵐ[volume] g) (σ : Sphere → ℂ) :
    moment f σ =ᵐ[volume.restrict (Ioi (0 : ℝ))] moment g σ := by
  filter_upwards [polar_ae hfg] with r hr
  exact integral_congr_ae (hr.mono (fun n hn => congrArg (fun z : ℂ => z*σ n) hn))

theorem moment_add (f g : OQ14.PolarMomentEnergy.ScalarL2) (σ : Sphere → ℂ)
    (hσ : MemLp σ 2 angularMeasure) :
    moment (f+g) σ =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => moment f σ r+moment g σ r := by
  have he := moment_congr (Lp.coeFn_add f g) σ
  filter_upwards [he,PolarMomentEnergy.slice_memLp_ae f,PolarMomentEnergy.slice_memLp_ae g] with r hr hf hg
  unfold moment
  simp_rw [Pi.add_apply,add_mul]
  exact integral_add (hf.integrable_mul hσ) (hg.integrable_mul hσ)

end OQ14.PolarMomentAE

#print axioms OQ14.PolarMomentAE.polar_ae
#print axioms OQ14.PolarMomentAE.moment_congr
#print axioms OQ14.PolarMomentAE.moment_add
