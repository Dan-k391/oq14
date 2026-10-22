import SmoothLocalRepresentative
import Mathlib.Topology.Compactness.Lindelof

/-! Continuous representatives on open real sets from genuine smooth-test weak derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ComplexSmoothRepresentative
open MeasureTheory Set Filter OQ14.SmoothWeakDerivative OQ14.SmoothLocalRepresentative
open scoped Topology

theorem continuous_gluing (Ω : Set ℝ) (f : ℝ → ℂ)
    (U : Ω → Set ℝ) (C : Ω → ℝ → ℂ)
    (ho : ∀ x,IsOpen (U x)) (hm : ∀ x,(x : ℝ) ∈ U x)
    (hs : ∀ x,U x ⊆ Ω) (hc : ∀ x,Continuous (C x))
    (ha : ∀ x,f =ᵐ[volume.restrict (U x)] C x) :
    ∃ F : ℝ → ℂ,ContinuousOn F Ω ∧ f =ᵐ[volume.restrict Ω] F := by
  classical
  let F : ℝ → ℂ := fun x => if hx : x ∈ Ω then C ⟨x,hx⟩ x else 0
  have he (x : Ω) : EqOn F (C x) (U x) := by
    intro y hy
    have hyΩ := hs x hy
    let z : Ω := ⟨y,hyΩ⟩
    have ha₁ : f =ᵐ[volume.restrict (U x ∩ U z)] C x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (ha x)
    have ha₂ : f =ᵐ[volume.restrict (U x ∩ U z)] C z :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (ha z)
    have heq := Measure.eqOn_open_of_ae_eq (ha₁.symm.trans ha₂)
      ((ho x).inter (ho z)) (hc x).continuousOn (hc z).continuousOn
    have hh := heq ⟨hy,hm z⟩
    simpa only [F,dif_pos hyΩ] using hh.symm
  refine ⟨F,?_,?_⟩
  · intro x hx
    have hevent : F =ᶠ[𝓝 x] C ⟨x,hx⟩ :=
      Filter.eventually_of_mem ((ho ⟨x,hx⟩).mem_nhds (hm ⟨x,hx⟩)) (he ⟨x,hx⟩)
    exact ((hc ⟨x,hx⟩).continuousAt.congr hevent.symm).continuousWithinAt
  · obtain ⟨s,hsc,hcover⟩ := (IsLindelof.of_coe (s := Ω)).elim_countable_subcover U ho
      (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hm ⟨x,hx⟩⟩)
    apply ae_restrict_of_ae_restrict_of_subset hcover
    apply (ae_eq_restrict_biUnion_iff U hsc f F).mpr
    intro x _
    filter_upwards [ha x,ae_restrict_mem (ho x).measurableSet] with y hy hm'
    exact hy.trans (he x hm').symm

theorem representative {Ω : Set ℝ} (hΩ : IsOpen Ω) (f g : ℝ → ℂ)
    (hf : LocallyIntegrableOn f Ω) (hg : LocallyIntegrableOn g Ω) (hw : WeakDerivative Ω f g) :
    ∃ F : ℝ → ℂ,ContinuousOn F Ω ∧ f =ᵐ[volume.restrict Ω] F ∧
      ∀ a b,uIcc a b ⊆ Ω → F b-F a=∫ x in a..b,g x := by
  classical
  have charts (x : Ω) : ∃ a b : ℝ,a<(x : ℝ) ∧ (x : ℝ)<b ∧ Icc a b ⊆ Ω ∧
      ∃ F : ℝ → ℂ,Continuous F ∧ f =ᵐ[volume.restrict (Icc a b)] F := by
    obtain ⟨a,b,_,hnh,hs⟩ := exists_Icc_mem_subset_of_mem_nhds (hΩ.mem_nhds x.property)
    have hab := Icc_mem_nhds_iff.mp hnh
    obtain ⟨F,hF,hae,_⟩ := local_representative hΩ f g hf hg hw hs
    exact ⟨a,b,hab.1,hab.2,hs,F,hF,hae⟩
  choose a b ha hb hs C hc hae using charts
  obtain ⟨F,hF,hfF⟩ := continuous_gluing Ω f (fun x => Ioo (a x) (b x)) C
    (fun _ => isOpen_Ioo) (fun x => ⟨ha x,hb x⟩)
    (fun x => Ioo_subset_Icc_self.trans (hs x)) hc
    (fun x => ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self (hae x))
  refine ⟨F,hF,hfF,?_⟩
  intro c d hcd
  by_cases he : c=d
  · subst d
    simp
  have hlt : min c d<max c d := by
    rcases lt_or_gt_of_ne he with h|h
    · simpa only [min_eq_left h.le,max_eq_right h.le] using h
    · simpa only [min_eq_right h.le,max_eq_left h.le] using h
  obtain ⟨G,hG,hfG,hinc⟩ := local_representative hΩ f g hf hg hw hcd
  have hres : f =ᵐ[volume.restrict (uIcc c d)] F :=
    ae_restrict_of_ae_restrict_of_subset hcd hfF
  have heq : EqOn F G (uIcc c d) := Measure.eqOn_of_ae_eq
    (hres.symm.trans hfG)
    (hF.mono hcd) hG.continuousOn (by
      rw [uIcc,interior_Icc,closure_Ioo hlt.ne])
  rw [heq right_mem_uIcc,heq left_mem_uIcc]
  exact hinc c left_mem_uIcc d right_mem_uIcc

theorem hasDerivAt_of_increment {Ω : Set ℝ} (hΩ : IsOpen Ω) (F g G : ℝ → ℂ)
    (hinc : ∀ a b,uIcc a b ⊆ Ω → F b-F a=∫ x in a..b,g x)
    (hgG : g =ᵐ[volume.restrict Ω] G) (hG : ContinuousOn G Ω) {r : ℝ} (hr : r ∈ Ω) :
    HasDerivAt F (G r) r := by
  obtain ⟨a,b,hrab,hnh,hs⟩ := exists_Icc_mem_subset_of_mem_nhds (hΩ.mem_nhds hr)
  have he : F =ᶠ[𝓝 r] fun x => F r+∫ t in r..x,G t := by
    filter_upwards [hnh] with x hx
    have hsub : uIcc r x ⊆ Ω := (uIcc_subset_Icc hrab hx).trans hs
    have hi : (∫ t in r..x,g t)=∫ t in r..x,G t :=
      intervalIntegral.integral_congr_ae_restrict
        (ae_restrict_of_ae_restrict_of_subset (uIoc_subset_uIcc.trans hsub) hgG)
    have hh := hinc r x hsub
    rw [hi] at hh
    linear_combination hh
  have hd := intervalIntegral.integral_hasDerivAt_right (a := r)
    (show IntervalIntegrable G volume r r from by simp)
    (ContinuousOn.stronglyMeasurableAtFilter hΩ hG r hr) (hG.continuousAt (hΩ.mem_nhds hr))
  simpa only [zero_add] using ((hasDerivAt_const r (F r)).add hd).congr_of_eventuallyEq he

theorem differentiable_representative {Ω : Set ℝ} (hΩ : IsOpen Ω) (f g G : ℝ → ℂ)
    (hf : LocallyIntegrableOn f Ω) (hg : LocallyIntegrableOn g Ω) (hw : WeakDerivative Ω f g)
    (hgG : g =ᵐ[volume.restrict Ω] G) (hG : ContinuousOn G Ω) :
    ∃ F : ℝ → ℂ,ContinuousOn F Ω ∧ f =ᵐ[volume.restrict Ω] F ∧
      (∀ a b,uIcc a b ⊆ Ω → F b-F a=∫ x in a..b,g x) ∧
      ∀ r ∈ Ω,HasDerivAt F (G r) r := by
  obtain ⟨F,hF,ha,hinc⟩ := representative hΩ f g hf hg hw
  exact ⟨F,hF,ha,hinc,fun _ hr => hasDerivAt_of_increment hΩ F g G hinc hgG hG hr⟩

end OQ14.ComplexSmoothRepresentative

#print axioms OQ14.ComplexSmoothRepresentative.continuous_gluing
#print axioms OQ14.ComplexSmoothRepresentative.representative
#print axioms OQ14.ComplexSmoothRepresentative.hasDerivAt_of_increment
#print axioms OQ14.ComplexSmoothRepresentative.differentiable_representative
