import Packet06Laurent

/-! Analytic observation of a simple operator pole, including its regular part. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06LaurentTransport
open Filter
open scoped Topology
variable {H J : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup J] [NormedSpace ℂ J]

theorem analytic_dslope (C : ℂ → H →L[ℂ] J) (z0 : ℂ) (hC : AnalyticAt ℂ C z0) :
    AnalyticAt ℂ (dslope C z0) z0 := by
  obtain ⟨p,hp⟩ := hC
  exact ⟨p.fslope,hp.has_fpower_series_dslope_fslope⟩

theorem observation_expansion (F : ℂ → H →L[ℂ] H) (R : H →L[ℂ] H)
    (B : ℂ → H →L[ℂ] H) (C : ℂ → H →L[ℂ] J) (z0 : ℂ)
    (hB : AnalyticAt ℂ B z0) (hC : AnalyticAt ℂ C z0)
    (he : ∀ᶠ z in 𝓝[≠] z0, F z = (z-z0)⁻¹ • R + B z) :
    ∃ D : ℂ → H →L[ℂ] J, AnalyticAt ℂ D z0 ∧
      (∀ᶠ z in 𝓝[≠] z0, (C z).comp (F z) = (z-z0)⁻¹ • (C z0).comp R + D z) := by
  let D : ℂ → H →L[ℂ] J := fun z => (dslope C z0 z).comp R + (C z).comp (B z)
  have hd : AnalyticAt ℂ (fun z => (dslope C z0 z).comp R) z0 :=
    (((ContinuousLinearMap.compL ℂ H H J).flip R).analyticAt (dslope C z0 z0)).comp
      (analytic_dslope C z0 hC)
  have hcb : AnalyticAt ℂ (fun z => (C z).comp (B z)) z0 :=
    ((ContinuousLinearMap.compL ℂ H H J).analyticAt_bilinear (C z0,B z0)).comp
      (f := fun z : ℂ => (C z,B z)) (hC.prod hB)
  refine ⟨D,hd.add hcb,?_⟩
  filter_upwards [he,self_mem_nhdsWithin] with z hz hn
  rw [hz]
  dsimp only [D]
  rw [dslope_of_ne _ hn,slope_def_module]
  simp only [ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.sub_comp,smul_sub]
  abel

theorem observation_residue_limit (F : ℂ → H →L[ℂ] H) (R : H →L[ℂ] H)
    (C : ℂ → H →L[ℂ] J) (z0 : ℂ) (hC : ContinuousAt C z0)
    (hR : Tendsto (fun z => (z-z0) • F z) (𝓝[≠] z0) (𝓝 R)) :
    Tendsto (fun z => (z-z0) • (C z).comp (F z)) (𝓝[≠] z0) (𝓝 ((C z0).comp R)) := by
  have h := (ContinuousLinearMap.compL ℂ H H J).continuous₂.tendsto (C z0,R) |>.comp
    ((hC.tendsto.mono_left (show 𝓝[≠] z0 ≤ 𝓝 z0 from nhdsWithin_le_nhds)).prodMk_nhds hR)
  change Tendsto (fun z => (C z).comp ((z-z0) • F z)) (𝓝[≠] z0) (𝓝 ((C z0).comp R)) at h
  simpa only [ContinuousLinearMap.comp_smul] using h

theorem observed_residue_form (R : H →L[ℂ] H) (C : H →L[ℂ] J)
    (u : H) (φ : H →L[ℂ] ℂ) (d : ℂ)
    (hr : ∀ x, R x = (φ x/d) • u) :
    ∀ x, (C.comp R) x = (φ x/d) • C u := by
  intro x
  rw [ContinuousLinearMap.comp_apply,hr,map_smul]

theorem observed_residue_nonzero (R : H →L[ℂ] H) (C : H →L[ℂ] J)
    (u : H) (φ : H →L[ℂ] ℂ) (d : ℂ) (hd : d ≠ 0)
    (hr : ∀ x, R x = (φ x/d) • u) (hCu : C u ≠ 0)
    (v : H) (hv : φ v ≠ 0) : C.comp R ≠ 0 := by
  intro hz
  have he := congrArg (fun L : H →L[ℂ] J => L v) hz
  change (C.comp R) v = 0 at he
  rw [observed_residue_form R C u φ d hr v] at he
  exact smul_ne_zero (div_ne_zero hv hd) hCu he

end OQ14.Packet06LaurentTransport
#print axioms OQ14.Packet06LaurentTransport.analytic_dslope
#print axioms OQ14.Packet06LaurentTransport.observation_expansion
#print axioms OQ14.Packet06LaurentTransport.observation_residue_limit
#print axioms OQ14.Packet06LaurentTransport.observed_residue_form
#print axioms OQ14.Packet06LaurentTransport.observed_residue_nonzero
