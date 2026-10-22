import ConicalFluxMoments
import ComplexSmoothRepresentative

/-! Smooth-test weak derivatives of the actual two-coordinate Maxwell projection. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ConicalRadialWeakSystem
open MeasureTheory Set OQ14.ConicalStaticVolume OQ14.ConicalFluxMoments
  OQ14.ConicalCorrectionMoments OQ14.ConicalProjectedDerivative OQ14.SmoothWeakDerivative
open scoped Topology

private theorem test_integral_eq (η : ℝ → ℂ) (hs : tsupport η ⊆ Ioi (0 : ℝ)) (f : ℝ → ℂ) :
    (∫ r in Ioi (0 : ℝ), η r*f r)=∫ r,η r*f r := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  have hn : r ∉ tsupport η := fun h => hr (hs h)
  simp only [image_eq_zero_of_nmem_tsupport hn,zero_mul]

private theorem cast_support (η : ℝ → ℝ) : tsupport (fun r => (η r : ℂ))=tsupport η := by
  have he : Function.support (fun r => (η r : ℂ))=Function.support η := by
    ext r
    exact not_congr Complex.ofReal_eq_zero
  exact congrArg closure he

private theorem cast_deriv (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    deriv (fun r => (η r : ℂ))=(fun r => ((deriv η r : ℝ) : ℂ)) := by
  ext r
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r ((hη.differentiable (by simp) r).hasDerivAt)).deriv

private theorem deriv_tsupport (η : ℝ → ℂ) : tsupport (deriv η) ⊆ tsupport η := by
  exact (closure_mono support_deriv_subset).trans (by simp only [tsupport,isClosed_closure.closure_eq,subset_refl])

theorem projected_weakDerivative (p : Data) (k : ℝ) : WeakDerivative (Ioi (0 : ℝ)) (projected p k)
    (fun r : ℝ => flux p k r/(r^2 : ℂ)-radialCorrection p k r) := by
  intro η hη hc hs
  have h0 : 0 ∉ tsupport η := fun h => (show (0 : ℝ) < 0 from hs h).false
  have h := projected_weak_forced p k η hη hc h0
  have hcs : tsupport (fun r => (η r : ℂ)) ⊆ Ioi (0 : ℝ) := by rwa [cast_support]
  have hds : tsupport (fun r => ((deriv η r : ℝ) : ℂ)) ⊆ Ioi (0 : ℝ) := by
    rw [← cast_deriv η hη]
    exact (deriv_tsupport _).trans hcs
  rw [test_integral_eq _ hcs _,test_integral_eq _ hds _] at h
  simpa only [add_comm] using h

theorem flux_weakDerivative (p : Data) (k : ℝ) (hk0 : k≠0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) :
    WeakDerivative (Ioo (0 : ℝ) p.cutoff.rIn) (flux p k)
      (fun r : ℝ => (p.eigenvalue : ℂ)*projected p k r+(r : ℂ)*tangentCorrection p k r) := by
  intro η hη hc hs
  have hcs : tsupport (fun r => (η r : ℂ)) ⊆ Ioo (0 : ℝ) p.cutoff.rIn := by rwa [cast_support]
  have hh := flux_weak_forced p k hk0 hk (fun r => (η r : ℂ)) (Complex.ofRealCLM.contDiff.comp hη)
    (hc.comp_left (g := Complex.ofReal) (by simp)) hcs
  have hpos := hcs.trans Ioo_subset_Ioi_self
  rw [test_integral_eq _ ((deriv_tsupport _).trans hpos) _,test_integral_eq _ hpos _] at hh
  simpa only [cast_deriv η hη] using hh

theorem exists_classical_system (p : Data) (k : ℝ) (hk0 : k≠0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) :
    ∃ U F : ℝ → ℂ, ContinuousOn U (Ioo (0 : ℝ) p.cutoff.rIn) ∧
      ContinuousOn F (Ioo (0 : ℝ) p.cutoff.rIn) ∧
      projected p k =ᵐ[volume.restrict (Ioo (0 : ℝ) p.cutoff.rIn)] U ∧
      flux p k =ᵐ[volume.restrict (Ioo (0 : ℝ) p.cutoff.rIn)] F ∧
      (∀ r ∈ Ioo (0 : ℝ) p.cutoff.rIn,HasDerivAt U (F r/(r^2 : ℂ)-radialCorrection p k r) r) ∧
      (∀ r ∈ Ioo (0 : ℝ) p.cutoff.rIn,HasDerivAt F ((p.eigenvalue : ℂ)*U r+(r : ℂ)*tangentCorrection p k r) r) ∧
      MemLp U 2 (volume.restrict (Ioo (0 : ℝ) p.cutoff.rIn)) := by
  let Ω := Ioo (0 : ℝ) p.cutoff.rIn
  let gU : ℝ → ℂ := fun r => flux p k r/(r^2 : ℂ)-radialCorrection p k r
  let gF : ℝ → ℂ := fun r => (p.eigenvalue : ℂ)*projected p k r+(r : ℂ)*tangentCorrection p k r
  have hwU : WeakDerivative Ω (projected p k) gU := by
    intro η hη hc hs
    exact projected_weakDerivative p k η hη hc (hs.trans Ioo_subset_Ioi_self)
  obtain ⟨U,hUc,hUa,hUi⟩ := ComplexSmoothRepresentative.representative isOpen_Ioo (projected p k) gU
    ((ConicalProjectedEnergy.projected_locallyIntegrableOn p k).mono_set Ioo_subset_Ioi_self)
    ((projected_forcing_locallyIntegrableOn p k).mono_set Ioo_subset_Ioi_self) hwU
  obtain ⟨F,hFc,hFa,hFi⟩ := ComplexSmoothRepresentative.representative isOpen_Ioo (flux p k) gF
    ((flux_locallyIntegrableOn p k).mono_set Ioo_subset_Ioi_self)
    ((forcing_locallyIntegrableOn p k).mono_set Ioo_subset_Ioi_self) (flux_weakDerivative p k hk0 hk)
  have hgU : gU =ᵐ[volume.restrict Ω] fun r => F r/(r^2 : ℂ)-radialCorrection p k r := by
    filter_upwards [hFa] with r hr
    exact congrArg (fun z : ℂ => z/(r^2 : ℂ)-radialCorrection p k r) hr
  have hgF : gF =ᵐ[volume.restrict Ω] fun r => (p.eigenvalue : ℂ)*U r+(r : ℂ)*tangentCorrection p k r := by
    filter_upwards [hUa] with r hr
    exact congrArg (fun z : ℂ => (p.eigenvalue : ℂ)*z+(r : ℂ)*tangentCorrection p k r) hr
  have hgUc : ContinuousOn (fun r : ℝ => F r/(r^2 : ℂ)-radialCorrection p k r) Ω :=
    (hFc.div (Complex.continuous_ofReal.pow 2).continuousOn (fun r hr =>
      pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (show r≠0 from hr.1.ne')))).sub
      (radialCorrection_continuous p k).continuousOn
  have hgFc : ContinuousOn (fun r : ℝ => (p.eigenvalue : ℂ)*U r+(r : ℂ)*tangentCorrection p k r) Ω :=
    (continuousOn_const.mul hUc).add (Complex.continuous_ofReal.continuousOn.mul (tangentCorrection_continuous p k).continuousOn)
  refine ⟨U,F,hUc,hFc,hUa,hFa,?_,?_,?_⟩
  · intro r hr
    exact ComplexSmoothRepresentative.hasDerivAt_of_increment isOpen_Ioo U gU _ hUi hgU hgUc hr
  · intro r hr
    exact ComplexSmoothRepresentative.hasDerivAt_of_increment isOpen_Ioo F gF _ hFi hgF hgFc hr
  · exact MemLp.ae_eq hUa (MemLp.mono_measure (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl)
      (ConicalProjectedEnergy.projected_memLp p k))

end OQ14.ConicalRadialWeakSystem

#print axioms OQ14.ConicalRadialWeakSystem.projected_weakDerivative
#print axioms OQ14.ConicalRadialWeakSystem.flux_weakDerivative
#print axioms OQ14.ConicalRadialWeakSystem.exists_classical_system

