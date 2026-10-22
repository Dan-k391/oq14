import ConicalSpatialMaxwell
import RegionalMaxwellHelmholtz
import MaterialHCurl

/-! Genuine regional H(curl) and Gauss law for the constructed conical Maxwell fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ConicalInnerMaxwell
open MeasureTheory Metric Set OQ14.Maxwell OQ14.ConicalStaticVolume
open scoped SchwartzMap

abbrev Space := FourierL2.Space
def region (p : Data) : Set Space := ball 0 p.cutoff.rIn
def epsilon (p : Data) : Space → ℝ := ConicalCapField.permittivity p.contrast p.threshold
abbrev E := ConicalSpatialMaxwell.electric
abbrev H := ConicalSpatialMaxwell.magnetic
def D (p : Data) (k : ℝ) : Field := fun x i => (epsilon p x : ℂ)*E p k x i

def globalTest {Ω : Set Space} (f : RegionalMaxwellHelmholtz.Test Ω) : DynamicSource.Test :=
  ⟨FourierL2.compactSmoothSchwartz f.val f.property.1 f.property.2.1,f.property.2.1⟩

theorem regional_maxwell (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (i : Fin 3) (f : RegionalMaxwellHelmholtz.Test (region p)) :
    RegionalMaxwellHelmholtz.curlPair (RegionalMaxwellHelmholtz.fieldPair (E p k)) i f=
      Complex.I*(k : ℂ)*RegionalMaxwellHelmholtz.fieldPair (H p k) i f ∧
    RegionalMaxwellHelmholtz.curlPair (RegionalMaxwellHelmholtz.fieldPair (H p k)) i f=
      -(Complex.I*(k : ℂ))*RegionalMaxwellHelmholtz.fieldPair (D p k) i f := by
  exact ConicalSpatialMaxwell.maxwell_inner p k hk i (globalTest f) f.property.2.2

theorem gauss_test (p : Data) (k : ℝ) (hk0 : k ≠ 0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (f : RegionalMaxwellHelmholtz.Test (region p)) :
    (∑ i : Fin 3, ∫ x, (epsilon p x : ℂ)*E p k x i*dcoord f.val x i)=0 :=
  RegionalMaxwellHelmholtz.divPair_zero_of_curl (RegionalMaxwellHelmholtz.fieldPair (H p k))
    (RegionalMaxwellHelmholtz.fieldPair (D p k)) (-(Complex.I*(k : ℂ)))
    (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk0)))
    (fun i g => (regional_maxwell p k hk i g).2) f

theorem gauss_schwartz (p : Data) (k : ℝ) (hk0 : k ≠ 0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (f : 𝓢(Space,ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ region p) :
    (∑ i : Fin 3, ∫ x, (epsilon p x : ℂ)*E p k x i*dcoord f x i)=0 := by
  have hc : HasCompactSupport (f : Space → ℂ) :=
    (isCompact_closedBall (0 : Space) p.cutoff.rIn).of_isClosed_subset isClosed_closure
      (hf.trans ball_subset_closedBall)
  exact gauss_test p k hk0 hk ⟨f,f.smooth (⊤ : ℕ∞),hc,hf⟩

theorem electric_memLp (p : Data) (k : ℝ) (i : Fin 3) :
    MemLp (fun x => E p k x i) 2 (DomainCurl.regionMeasure (region p)) :=
  (ConicalSpatialMaxwell.electric_memLp p k p.cutoff.rIn i).mono_measure
    (Measure.restrict_mono ball_subset_closedBall le_rfl)

theorem magnetic_memLp (p : Data) (k : ℝ) (i : Fin 3) :
    MemLp (fun x => H p k x i) 2 (DomainCurl.regionMeasure (region p)) :=
  (ConicalSpatialMaxwell.magnetic_memLp p k p.cutoff.rIn i).mono_measure
    (Measure.restrict_mono ball_subset_closedBall le_rfl)

theorem displacement_memLp (p : Data) (k : ℝ) (i : Fin 3) :
    MemLp (fun x => D p k x i) 2 (DomainCurl.regionMeasure (region p)) := by
  apply MaterialHCurl.coefficient_mul_memLp (region p) (epsilon p)
    (ConicalAnnularSource.permittivity_measurable p.contrast p.threshold) (1+p.contrast) _ _
    (electric_memLp p k i)
  intro x
  have h := ConicalStaticField.permittivity_bounds p.contrast p.threshold p.contrast_nonnegative x
  change ‖ConicalCapField.permittivity p.contrast p.threshold x‖ ≤ 1+p.contrast
  rw [Real.norm_eq_abs,abs_of_nonneg (le_trans (by norm_num) h.1)]
  exact h.2

theorem electric_weak_curl (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) :
    DomainCurl.HasWeakCurl (region p)
      (DomainCurl.fieldToL2 (region p) (E p k) (electric_memLp p k))
      (DomainCurl.fieldToL2 (region p) (MaterialHCurl.electricCurl k (H p k))
        (fun j => (magnetic_memLp p k j).const_mul (Complex.I*(k : ℂ)))) := by
  apply RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth isOpen_ball
  intro f hf hc hi j
  let g : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz f hf hc,hc⟩
  have h := (ConicalSpatialMaxwell.maxwell_inner p k hk j g hi).1
  simpa only [MagneticResponse.curlPair,MaterialMaxwell.fieldPair,DynamicSource.testPartial,
    GradientProjection.pderivative_apply,MaterialHCurl.electricCurl,mul_assoc,integral_const_mul] using h.symm

theorem magnetic_weak_curl (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) :
    DomainCurl.HasWeakCurl (region p)
      (DomainCurl.fieldToL2 (region p) (H p k) (magnetic_memLp p k))
      (DomainCurl.fieldToL2 (region p) (MaterialHCurl.magneticCurl k (epsilon p) (E p k))
        (fun j => (displacement_memLp p k j).const_mul (-(Complex.I*(k : ℂ))))) := by
  apply RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth isOpen_ball
  intro f hf hc hi j
  let g : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz f hf hc,hc⟩
  have h := (ConicalSpatialMaxwell.maxwell_inner p k hk j g hi).2
  simpa only [MagneticResponse.curlPair,MaterialMaxwell.fieldPair,DynamicSource.testPartial,
    GradientProjection.pderivative_apply,MaterialHCurl.magneticCurl,mul_assoc,integral_const_mul] using h.symm

theorem exists_regional_fields (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) :
    ∃ e h : DomainCurl.HCurl (region p),
      (∀ j, (e.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (region p)] fun x => E p k x j) ∧
      (∀ j, (h.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (region p)] fun x => H p k x j) ∧
      WeakConservation.WeakMaxwell k (fun _ => 1) (epsilon p) e h := by
  let hCE := fun j => (magnetic_memLp p k j).const_mul (Complex.I*(k : ℂ))
  let hCH := fun j => (displacement_memLp p k j).const_mul (-(Complex.I*(k : ℂ)))
  let e : DomainCurl.HCurl (region p) :=
    ⟨(DomainCurl.fieldToL2 (region p) (E p k) (electric_memLp p k),
      DomainCurl.fieldToL2 (region p) (MaterialHCurl.electricCurl k (H p k)) hCE),electric_weak_curl p k hk⟩
  let h : DomainCurl.HCurl (region p) :=
    ⟨(DomainCurl.fieldToL2 (region p) (H p k) (magnetic_memLp p k),
      DomainCurl.fieldToL2 (region p) (MaterialHCurl.magneticCurl k (epsilon p) (E p k)) hCH),magnetic_weak_curl p k hk⟩
  refine ⟨e,h,fun j => (electric_memLp p k j).coeFn_toLp,fun j => (magnetic_memLp p k j).coeFn_toLp,?_,?_⟩
  · apply ae_all_iff.mpr
    intro j
    filter_upwards [(hCE j).coeFn_toLp,(magnetic_memLp p k j).coeFn_toLp] with x hc hh
    change (hCE j).toLp _ x=Complex.I*(k : ℂ)*(1 : ℂ)*(magnetic_memLp p k j).toLp _ x
    rw [hc,hh]
    simp only [mul_one]
  · apply ae_all_iff.mpr
    intro j
    filter_upwards [(hCH j).coeFn_toLp,(electric_memLp p k j).coeFn_toLp] with x hc he
    change (hCH j).toLp _ x= -Complex.I*(k : ℂ)*(epsilon p x : ℂ)*(electric_memLp p k j).toLp _ x
    rw [hc,he]
    unfold D
    ring

end OQ14.ConicalInnerMaxwell

#print axioms OQ14.ConicalInnerMaxwell.regional_maxwell
#print axioms OQ14.ConicalInnerMaxwell.gauss_test
#print axioms OQ14.ConicalInnerMaxwell.gauss_schwartz
#print axioms OQ14.ConicalInnerMaxwell.electric_memLp
#print axioms OQ14.ConicalInnerMaxwell.magnetic_memLp
#print axioms OQ14.ConicalInnerMaxwell.displacement_memLp
#print axioms OQ14.ConicalInnerMaxwell.electric_weak_curl
#print axioms OQ14.ConicalInnerMaxwell.magnetic_weak_curl
#print axioms OQ14.ConicalInnerMaxwell.exists_regional_fields
