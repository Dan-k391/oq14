import ConicalRoundedMaxwell

/-! Genuine H(curl) representatives for the explicit rounded physical Green fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ConicalRoundedHCurl
open MeasureTheory Metric Set OQ14.Maxwell OQ14.ConicalStaticVolume
  OQ14.ConicalRoundedMaxwell
open scoped SchwartzMap
abbrev Space := FourierL2.Space
abbrev region := ConicalInnerMaxwell.region
abbrev globalTest := @ConicalInnerMaxwell.globalTest
abbrev E := ConicalRoundedMaxwell.electric
abbrev H := ConicalRoundedMaxwell.magnetic
abbrev epsilon := ConicalRoundedPeaks.permittivity

def D (p : Data) (n : ℕ) (k : ℝ) : Field := fun x i => (epsilon p n x : ℂ)*E p n k x i

theorem epsilon_measurable (p : Data) (n : ℕ) : Measurable (epsilon p n) :=
  measurable_const.add ((material p n).measurable.comp VectorFourier.coordinateMap.measurable)

theorem regional_maxwell (p : Data) (n : ℕ) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p n) p.cutoff.rOut)
    (i : Fin 3) (f : RegionalMaxwellHelmholtz.Test (region p)) :
    RegionalMaxwellHelmholtz.curlPair (RegionalMaxwellHelmholtz.fieldPair (E p n k)) i f=
      Complex.I*(k : ℂ)*RegionalMaxwellHelmholtz.fieldPair (H p n k) i f ∧
    RegionalMaxwellHelmholtz.curlPair (RegionalMaxwellHelmholtz.fieldPair (H p n k)) i f=
      -(Complex.I*(k : ℂ))*RegionalMaxwellHelmholtz.fieldPair (D p n k) i f := by
  exact ConicalRoundedMaxwell.maxwell_inner p n k hk i (globalTest f) f.property.2.2

theorem gauss_test (p : Data) (n : ℕ) (k : ℝ) (hk0 : k ≠ 0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p n) p.cutoff.rOut)
    (f : RegionalMaxwellHelmholtz.Test (region p)) :
    (∑ i : Fin 3, ∫ x, (epsilon p n x : ℂ)*E p n k x i*dcoord f.val x i)=0 :=
  RegionalMaxwellHelmholtz.divPair_zero_of_curl (RegionalMaxwellHelmholtz.fieldPair (H p n k))
    (RegionalMaxwellHelmholtz.fieldPair (D p n k)) (-(Complex.I*(k : ℂ)))
    (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk0)))
    (fun i g => (regional_maxwell p n k hk i g).2) f

theorem gauss_schwartz (p : Data) (n : ℕ) (k : ℝ) (hk0 : k ≠ 0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p n) p.cutoff.rOut)
    (f : 𝓢(Space,ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ region p) :
    (∑ i : Fin 3, ∫ x, (epsilon p n x : ℂ)*E p n k x i*dcoord f x i)=0 := by
  have hc : HasCompactSupport (f : Space → ℂ) :=
    (isCompact_closedBall (0 : Space) p.cutoff.rIn).of_isClosed_subset isClosed_closure
      (hf.trans ball_subset_closedBall)
  exact gauss_test p n k hk0 hk ⟨f,f.smooth (⊤ : ℕ∞),hc,hf⟩

theorem electric_memLp (p : Data) (n : ℕ) (k : ℝ) (i : Fin 3) :
    MemLp (fun x => E p n k x i) 2 (DomainCurl.regionMeasure (region p)) :=
  (ConicalRoundedMaxwell.electric_memLp p n k p.cutoff.rIn i).mono_measure
    (Measure.restrict_mono ball_subset_closedBall le_rfl)

theorem magnetic_memLp (p : Data) (n : ℕ) (k : ℝ) (i : Fin 3) :
    MemLp (fun x => H p n k x i) 2 (DomainCurl.regionMeasure (region p)) :=
  (ConicalRoundedMaxwell.magnetic_memLp p n k p.cutoff.rIn i).mono_measure
    (Measure.restrict_mono ball_subset_closedBall le_rfl)

theorem displacement_memLp (p : Data) (n : ℕ) (k : ℝ) (i : Fin 3) :
    MemLp (fun x => D p n k x i) 2 (DomainCurl.regionMeasure (region p)) := by
  apply MaterialHCurl.coefficient_mul_memLp (region p) (epsilon p n)
    (epsilon_measurable p n) (1+p.contrast) _ _
    (electric_memLp p n k i)
  intro x
  have h := ConicalRoundedPeaks.permittivity_bounds p n x
  change ‖epsilon p n x‖ ≤ 1+p.contrast
  rw [Real.norm_eq_abs,abs_of_nonneg (le_trans (by norm_num) h.1)]
  exact h.2

theorem electric_weak_curl (p : Data) (n : ℕ) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p n) p.cutoff.rOut) :
    DomainCurl.HasWeakCurl (region p)
      (DomainCurl.fieldToL2 (region p) (E p n k) (electric_memLp p n k))
      (DomainCurl.fieldToL2 (region p) (MaterialHCurl.electricCurl k (H p n k))
        (fun j => (magnetic_memLp p n k j).const_mul (Complex.I*(k : ℂ)))) := by
  apply RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth isOpen_ball
  intro f hf hc hi j
  let g : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz f hf hc,hc⟩
  have h := (ConicalRoundedMaxwell.maxwell_inner p n k hk j g hi).1
  simpa only [MagneticResponse.curlPair,MaterialMaxwell.fieldPair,DynamicSource.testPartial,
    GradientProjection.pderivative_apply,MaterialHCurl.electricCurl,mul_assoc,integral_const_mul] using h.symm

theorem magnetic_weak_curl (p : Data) (n : ℕ) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p n) p.cutoff.rOut) :
    DomainCurl.HasWeakCurl (region p)
      (DomainCurl.fieldToL2 (region p) (H p n k) (magnetic_memLp p n k))
      (DomainCurl.fieldToL2 (region p) (MaterialHCurl.magneticCurl k (epsilon p n) (E p n k))
        (fun j => (displacement_memLp p n k j).const_mul (-(Complex.I*(k : ℂ))))) := by
  apply RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth isOpen_ball
  intro f hf hc hi j
  let g : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz f hf hc,hc⟩
  have h := (ConicalRoundedMaxwell.maxwell_inner p n k hk j g hi).2
  simpa only [MagneticResponse.curlPair,MaterialMaxwell.fieldPair,DynamicSource.testPartial,
    GradientProjection.pderivative_apply,MaterialHCurl.magneticCurl,mul_assoc,integral_const_mul] using h.symm

theorem exists_regional_fields (p : Data) (n : ℕ) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p n) p.cutoff.rOut) :
    ∃ e h : DomainCurl.HCurl (region p),
      (∀ j, (e.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (region p)] fun x => E p n k x j) ∧
      (∀ j, (h.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (region p)] fun x => H p n k x j) ∧
      WeakConservation.WeakMaxwell k (fun _ => 1) (epsilon p n) e h := by
  let hCE := fun j => (magnetic_memLp p n k j).const_mul (Complex.I*(k : ℂ))
  let hCH := fun j => (displacement_memLp p n k j).const_mul (-(Complex.I*(k : ℂ)))
  let e : DomainCurl.HCurl (region p) :=
    ⟨(DomainCurl.fieldToL2 (region p) (E p n k) (electric_memLp p n k),
      DomainCurl.fieldToL2 (region p) (MaterialHCurl.electricCurl k (H p n k)) hCE),electric_weak_curl p n k hk⟩
  let h : DomainCurl.HCurl (region p) :=
    ⟨(DomainCurl.fieldToL2 (region p) (H p n k) (magnetic_memLp p n k),
      DomainCurl.fieldToL2 (region p) (MaterialHCurl.magneticCurl k (epsilon p n) (E p n k)) hCH),magnetic_weak_curl p n k hk⟩
  refine ⟨e,h,fun j => (electric_memLp p n k j).coeFn_toLp,fun j => (magnetic_memLp p n k j).coeFn_toLp,?_,?_⟩
  · apply ae_all_iff.mpr
    intro j
    filter_upwards [(hCE j).coeFn_toLp,(magnetic_memLp p n k j).coeFn_toLp] with x hc hh
    change (hCE j).toLp _ x=Complex.I*(k : ℂ)*(1 : ℂ)*(magnetic_memLp p n k j).toLp _ x
    rw [hc,hh]
    simp only [mul_one]
  · apply ae_all_iff.mpr
    intro j
    filter_upwards [(hCH j).coeFn_toLp,(electric_memLp p n k j).coeFn_toLp] with x hc he
    change (hCH j).toLp _ x= -Complex.I*(k : ℂ)*(epsilon p n x : ℂ)*(electric_memLp p n k j).toLp _ x
    rw [hc,he]
    unfold D
    ring

end OQ14.ConicalRoundedHCurl

#print axioms OQ14.ConicalRoundedHCurl.epsilon_measurable
#print axioms OQ14.ConicalRoundedHCurl.regional_maxwell
#print axioms OQ14.ConicalRoundedHCurl.gauss_test
#print axioms OQ14.ConicalRoundedHCurl.gauss_schwartz
#print axioms OQ14.ConicalRoundedHCurl.electric_memLp
#print axioms OQ14.ConicalRoundedHCurl.magnetic_memLp
#print axioms OQ14.ConicalRoundedHCurl.displacement_memLp
#print axioms OQ14.ConicalRoundedHCurl.electric_weak_curl
#print axioms OQ14.ConicalRoundedHCurl.magnetic_weak_curl
#print axioms OQ14.ConicalRoundedHCurl.exists_regional_fields
