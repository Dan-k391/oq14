import BackgroundFluxMajorant
import SourceRemotePlaneSeries
import ForcedMaxwellResponse
import FourierL2

/-! Generic machinery for the radiated-field majorant: plane-flux decompositions of series over a countable
index, and the identification of a magnetic series from an electric one by the weak first Maxwell equation
on an open set (mode-wise weak equations, summable majorant, continuity, and the fundamental lemma). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.CoreWeakSeries
open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.SourceRemotePlaneBand
open scoped Topology ComplexConjugate

/-! ### Decompositions of series over a countable index -/

theorem decomp_tsum_gen {ι : Type*} (F : ι → Vector) (K1 K2 : ι → ℝ) (hK1 : Summable K1) (hK2 : Summable K2)
    (x : Space) (hx : x≠0) (h : ∀ i, Decomp (K1 i) (K2 i) (F i) x) :
    Summable F ∧ Decomp (∑' i, K1 i) (∑' i, K2 i) (∑' i, F i) x := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  choose Et Er hsum hdot hrad hn1 hn2 using h
  choose e he using hrad
  have hn1' : Summable (fun i => ‖Et i‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hn1 (hK1.div_const _)
  have hn2' : Summable (fun i => ‖Er i‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hn2 (hK2.div_const _)
  have hs1 : Summable Et := Summable.of_norm hn1'
  have hs2 : Summable Er := Summable.of_norm hn2'
  have hF : F=fun i => Et i+Er i := funext hsum
  have hsF : Summable F := by rw [hF]; exact hs1.add hs2
  refine ⟨hsF,∑' i, Et i,∑' i, Er i,?_,?_,?_,?_,?_⟩
  · rw [hF]
    exact hs1.tsum_add hs2
  · have hcoord (k : Fin 3) : HasSum (fun i => Et i k) ((∑' i, Et i) k) := (Pi.hasSum.mp hs1.hasSum) k
    have h0 : HasSum (fun i => dotPos x (Et i)) (dotPos x (∑' i, Et i)) :=
      (((hcoord 0).mul_left (x 0 : ℂ)).add ((hcoord 1).mul_left (x 1 : ℂ))).add ((hcoord 2).mul_left (x 2 : ℂ))
    have hz : (fun i => dotPos x (Et i))=fun _ => (0 : ℂ) := funext hdot
    rw [hz] at h0
    exact h0.unique hasSum_zero
  · let V : Submodule ℂ Vector := Submodule.span ℂ {DebyeRadialTrace.position x}
    have hclosed : IsClosed (V : Set Vector) := Submodule.closed_of_finiteDimensional V
    have hmem : ∀ s : Finset ι, ∑ i ∈ s, Er i ∈ (V : Set Vector) := by
      intro s
      apply V.sum_mem
      intro i _
      rw [he i]
      exact V.smul_mem _ (Submodule.mem_span_singleton_self _)
    have := hclosed.mem_of_tendsto hs2.hasSum (Eventually.of_forall hmem)
    obtain ⟨z,hz⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨z,hz.symm⟩
  · calc ‖∑' i, Et i‖ ≤ ∑' i, ‖Et i‖ := norm_tsum_le_tsum_norm hn1'
      _ ≤ ∑' i, K1 i/‖x‖ := Summable.tsum_le_tsum hn1 hn1' (hK1.div_const _)
      _ = (∑' i, K1 i)/‖x‖ := tsum_div_const
  · calc ‖∑' i, Er i‖ ≤ ∑' i, ‖Er i‖ := norm_tsum_le_tsum_norm hn2'
      _ ≤ ∑' i, K2 i/‖x‖^2 := Summable.tsum_le_tsum hn2 hn2' (hK2.div_const _)
      _ = (∑' i, K2 i)/‖x‖^2 := tsum_div_const

/-- A decomposed vector at distance at least `ρ` from the origin is bounded by the constants over `ρ`. -/
theorem norm_le_of_decomp {K1 K2 : ℝ} {F : Vector} {x : Space} (h : Decomp K1 K2 F x) (ρ : ℝ)
    (hρ : 0<ρ) (hx : ρ≤‖x‖) : ‖F‖ ≤ K1/ρ+K2/ρ^2 := by
  obtain ⟨Et,Er,rfl,-,-,h1,h2⟩ := h
  have hr : 0<‖x‖ := hρ.trans_le hx
  have hK1 : 0 ≤ K1 := by
    by_contra hneg
    push_neg at hneg
    have := div_neg_of_neg_of_pos hneg hr
    have := (norm_nonneg Et).trans h1
    linarith
  have hK2 : 0 ≤ K2 := by
    by_contra hneg
    push_neg at hneg
    have := div_neg_of_neg_of_pos hneg (pow_pos hr 2)
    have := (norm_nonneg Er).trans h2
    linarith
  exact (norm_add_le Et Er).trans (add_le_add
    (h1.trans (div_le_div_of_nonneg_left hK1 hρ hx))
    (h2.trans (div_le_div_of_nonneg_left hK2 (pow_pos hρ 2) (pow_le_pow_left₀ hρ.le hx 2))))

/-! ### Weak first Maxwell equation on an open set -/

/-- The weak first Maxwell equation `curl E = I H` tested against Schwartz functions with compact support
inside `Ω`. -/
def WeakOn (Ω : Set Space) (E H : Field) : Prop :=
  ∀ (i : Fin 3) (f : DynamicSource.Test), tsupport (f.val : Space → ℂ) ⊆ Ω →
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair E) i f = Complex.I * MaterialMaxwell.fieldPair H i f

theorem tsupport_dcoord_subset (f : Space → ℂ) (i : Fin 3) :
    tsupport (fun x => dcoord f x i) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  exact hx (by simp only [dcoord,fderiv_of_not_mem_tsupport ℝ hn,ContinuousLinearMap.zero_apply])

theorem tsupport_testPartial_subset (i : Fin 3) (f : DynamicSource.Test) :
    tsupport ((DynamicSource.testPartial i f).val : Space → ℂ) ⊆ tsupport (f.val : Space → ℂ) :=
  tsupport_dcoord_subset f.val i

theorem integrable_mul_test {Ω : Set Space} (g : Space → ℂ) (hg : ContinuousOn g Ω)
    (f : DynamicSource.Test) (hf : tsupport (f.val : Space → ℂ) ⊆ Ω) :
    Integrable (fun x => g x * f.val x) := by
  have hK : IsCompact (tsupport (f.val : Space → ℂ)) := f.property.isCompact
  have hc : ContinuousOn (fun x => g x * f.val x) (tsupport (f.val : Space → ℂ)) :=
    (hg.mono hf).mul f.val.continuous.continuousOn
  have hi : IntegrableOn (fun x => g x * f.val x) (tsupport (f.val : Space → ℂ)) volume :=
    hc.integrableOn_compact hK
  apply hi.integrable_of_forall_not_mem_eq_zero
  intro x hx
  simp [image_eq_zero_of_nmem_tsupport hx]

theorem fieldPair_hasSum {ι : Type*} [Countable ι] {Ω : Set Space} (hΩ : IsOpen Ω) (E : ι → Field)
    (M : ι → ℝ) (hM : Summable M) (hc : ∀ a j, ContinuousOn (fun x => E a x j) Ω)
    (hb : ∀ a, ∀ x ∈ Ω, ∀ j, ‖E a x j‖ ≤ M a) (j : Fin 3) (g : DynamicSource.Test)
    (hg : tsupport (g.val : Space → ℂ) ⊆ Ω) :
    HasSum (fun a => MaterialMaxwell.fieldPair (E a) j g)
      (MaterialMaxwell.fieldPair (fun x i => ∑' a, E a x i) j g) := by
  have hz : ∀ x, x ∉ Ω → g.val x = 0 := fun x hx => image_eq_zero_of_nmem_tsupport (fun h => hx (hg h))
  have hint : Integrable (fun x => ‖g.val x‖) := (g.val.integrable).norm
  have key := hasSum_integral_of_dominated_convergence (μ := volume.restrict Ω)
    (F := fun a x => E a x j * g.val x) (f := fun x => (∑' a, E a x j) * g.val x)
    (fun a x => M a * ‖g.val x‖)
    (fun a => ((hc a j).mul g.val.continuous.continuousOn).aestronglyMeasurable hΩ.measurableSet)
    (fun a => (ae_restrict_iff' hΩ.measurableSet).mpr (Eventually.of_forall fun x hx => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb a x hx j) (norm_nonneg _)))
    (Eventually.of_forall fun x => hM.mul_right _)
    (by
      simp_rw [tsum_mul_right]
      exact (hint.const_mul _).integrableOn)
    ((ae_restrict_iff' hΩ.measurableSet).mpr (Eventually.of_forall fun x hx =>
      ((Summable.of_norm_bounded M hM (fun a => hb a x hx j)).hasSum).mul_right (g.val x)))
  have e1 : ∀ a, (∫ x in Ω, E a x j * g.val x) = MaterialMaxwell.fieldPair (E a) j g := fun a =>
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hz x hx])
  have e2 : (∫ x in Ω, (∑' a, E a x j) * g.val x) =
      MaterialMaxwell.fieldPair (fun x i => ∑' a, E a x i) j g :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hz x hx])
  simpa only [e1,e2] using key

theorem weakOn_tsum {ι : Type*} [Countable ι] {Ω : Set Space} (hΩ : IsOpen Ω) (E H : ι → Field)
    (M : ι → ℝ) (hM : Summable M)
    (hEc : ∀ a j, ContinuousOn (fun x => E a x j) Ω) (hHc : ∀ a j, ContinuousOn (fun x => H a x j) Ω)
    (hEb : ∀ a, ∀ x ∈ Ω, ∀ j, ‖E a x j‖ ≤ M a) (hHb : ∀ a, ∀ x ∈ Ω, ∀ j, ‖H a x j‖ ≤ M a)
    (hw : ∀ a, WeakOn Ω (E a) (H a)) :
    WeakOn Ω (fun x i => ∑' a, E a x i) (fun x i => ∑' a, H a x i) := by
  intro i f hf
  have h1 := fieldPair_hasSum hΩ E M hM hEc hEb (WeakCurl.next i)
    (DynamicSource.testPartial (WeakCurl.previous i) f)
    ((tsupport_testPartial_subset _ f).trans hf)
  have h2 := fieldPair_hasSum hΩ E M hM hEc hEb (WeakCurl.previous i)
    (DynamicSource.testPartial (WeakCurl.next i) f)
    ((tsupport_testPartial_subset _ f).trans hf)
  have h3 := (fieldPair_hasSum hΩ H M hM hHc hHb i f hf).mul_left Complex.I
  have h4 : HasSum (fun a => MagneticResponse.curlPair (MaterialMaxwell.fieldPair (E a)) i f)
      (MagneticResponse.curlPair (MaterialMaxwell.fieldPair (fun x i => ∑' a, E a x i)) i f) :=
    h1.sub h2
  have h5 : (fun a => MagneticResponse.curlPair (MaterialMaxwell.fieldPair (E a)) i f) =
      fun a => Complex.I * MaterialMaxwell.fieldPair (H a) i f := funext fun a => hw a i f hf
  rw [h5] at h4
  exact h4.unique h3

/-- Two continuous magnetic fields with the same electric field and the weak first Maxwell equation on an open
set agree on it. -/
theorem weak_unique {Ω : Set Space} (hΩ : IsOpen Ω) (E H H2 : Field)
    (hH : ∀ i, ContinuousOn (fun x => H x i) Ω) (hH2 : ∀ i, ContinuousOn (fun x => H2 x i) Ω)
    (h1 : WeakOn Ω E H) (h2 : WeakOn Ω E H2) : ∀ x ∈ Ω, ∀ i, H x i = H2 x i := by
  have hcomb : ∀ i, EqOn (fun x => H x i) (fun x => H2 x i) Ω := by
    intro i
    have hg : ContinuousOn (fun x => H x i - H2 x i) Ω := (hH i).sub (hH2 i)
    have hloc : LocallyIntegrableOn (fun x => H x i - H2 x i) Ω volume :=
      hg.locallyIntegrableOn hΩ.measurableSet
    have hz := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
      intro φ hφ hφc hφΩ
      have hφc2 : HasCompactSupport (fun x => (φ x : ℂ)) :=
        hφc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
      let f : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz
        (fun x => (φ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ) hφc2, hφc2⟩
      have hs : tsupport (f.val : Space → ℂ) = tsupport φ := by
        change closure (Function.support (fun x => (φ x : ℂ))) = closure (Function.support φ)
        ext x
        simp [Function.support]
      have hfΩ : tsupport (f.val : Space → ℂ) ⊆ Ω := hs ▸ hφΩ
      have hp : MaterialMaxwell.fieldPair H i f = MaterialMaxwell.fieldPair H2 i f := by
        have := (h1 i f hfΩ).symm.trans (h2 i f hfΩ)
        exact mul_left_cancel₀ Complex.I_ne_zero this
      have iH := integrable_mul_test (fun x => H x i) (hH i) f hfΩ
      have iH2 := integrable_mul_test (fun x => H2 x i) (hH2 i) f hfΩ
      have he : (∫ x, (H x i * f.val x - H2 x i * f.val x)) = 0 := by
        rw [integral_sub iH iH2]
        exact sub_eq_zero.mpr hp
      convert he using 1
      apply integral_congr_ae
      filter_upwards with x
      change (φ x : ℂ) * (H x i - H2 x i) = H x i * (φ x : ℂ) - H2 x i * (φ x : ℂ)
      ring)
    have hae : (fun x => H x i) =ᵐ[volume.restrict Ω] (fun x => H2 x i) :=
      (ae_restrict_iff' hΩ.measurableSet).mpr (hz.mono fun x hx hxΩ => sub_eq_zero.mp (hx hxΩ))
    exact Measure.eqOn_open_of_ae_eq hae hΩ (hH i) (hH2 i)
  intro x hx i
  exact hcomb i hx

end OQ14.CoreWeakSeries

#print axioms OQ14.CoreWeakSeries.decomp_tsum_gen
#print axioms OQ14.CoreWeakSeries.norm_le_of_decomp
#print axioms OQ14.CoreWeakSeries.tsupport_dcoord_subset
#print axioms OQ14.CoreWeakSeries.tsupport_testPartial_subset
#print axioms OQ14.CoreWeakSeries.integrable_mul_test
#print axioms OQ14.CoreWeakSeries.fieldPair_hasSum
#print axioms OQ14.CoreWeakSeries.weakOn_tsum
#print axioms OQ14.CoreWeakSeries.weak_unique
