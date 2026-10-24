import SourceRemotePlaneUniform

/-! From finite bands to all-degree series, abstractly: tangential/radial decompositions with summable
constants pass to the sum of a family; with explicit degree-summable constants supplied as hypotheses, the
absolute plane flux of the paired-shell series outside the core tends to zero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceRemotePlaneSeries
open MeasureTheory Set Metric Filter Complex OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.SourceRemotePlaneBand OQ14.PlaneInverseCube OQ14.SourceAnnulusPlaneFlux
open scoped Topology ComplexConjugate

theorem decomp_tsum (F : ℕ → Vector) (K1 K2 : ℕ → ℝ) (hK1 : Summable K1) (hK2 : Summable K2)
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
    have hlim := hs2.hasSum.tendsto_sum_nat
    have hmem : ∀ N : ℕ, ∑ i ∈ Finset.range N, Er i ∈ (V : Set Vector) := by
      intro N
      apply V.sum_mem
      intro i _
      rw [he i]
      exact V.smul_mem _ (Submodule.mem_span_singleton_self _)
    have := hclosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
    obtain ⟨z,hz⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨z,hz.symm⟩
  · calc ‖∑' i, Et i‖ ≤ ∑' i, ‖Et i‖ := norm_tsum_le_tsum_norm hn1'
      _ ≤ ∑' i, K1 i/‖x‖ := Summable.tsum_le_tsum hn1 hn1' (hK1.div_const _)
      _ = (∑' i, K1 i)/‖x‖ := tsum_div_const
  · calc ‖∑' i, Er i‖ ≤ ∑' i, ‖Er i‖ := norm_tsum_le_tsum_norm hn2'
      _ ≤ ∑' i, K2 i/‖x‖^2 := Summable.tsum_le_tsum hn2 hn2' (hK2.div_const _)
      _ = (∑' i, K2 i)/‖x‖^2 := tsum_div_const

theorem series_flux_bound (E H : ℕ → Vector) (K1 K2 L1 L2 : ℕ → ℝ)
    (hK1 : Summable K1) (hK2 : Summable K2) (hL1 : Summable L1) (hL2 : Summable L2)
    (x : Space) (hx2 : x 2=0) (hx : x≠0)
    (hE : ∀ i, Decomp (K1 i) (K2 i) (E i) x) (hH : ∀ i, Decomp (L1 i) (L2 i) (H i) x) :
    ‖crossProduct (∑' i, E i) (conjugate (∑' j, H j)) 2‖ ≤
      (2*(∑' i, K2 i)*(∑' i, L1 i)+2*(∑' i, K1 i)*(∑' i, L2 i))/‖x‖^3 :=
  flux_bound_of_decomp x hx2 (norm_pos_iff.mpr hx) _ _ _ _ _ _
    (decomp_tsum E K1 K2 hK1 hK2 x hx hE).2 (decomp_tsum H L1 L2 hL1 hL2 x hx hH).2

/-! ### The paired-shell series -/

def seriesElectric (q : ℝ) (hq : 0<q) (n : ℕ) (tm : ℕ → Bool) (l : ℕ → ℕ) (P : ℕ → Poly) (c : ℕ → ℂ)
    (s : ℕ) (x : Space) : Vector :=
  ∑' i, c i • modeElectric (tm i) { SourcePairedGeometry.physicalData q hq n s with l := l i } (P i) x

def seriesMagnetic (q : ℝ) (hq : 0<q) (n : ℕ) (tm : ℕ → Bool) (l : ℕ → ℕ) (P : ℕ → Poly) (c : ℕ → ℂ)
    (s : ℕ) (x : Space) : Vector :=
  ∑' i, c i • modeMagnetic (tm i) { SourcePairedGeometry.physicalData q hq n s with l := l i } (P i) x

def seriesFlux (q : ℝ) (hq : 0<q) (n : ℕ) (tmE : ℕ → Bool) (lE : ℕ → ℕ) (PE : ℕ → Poly) (cE : ℕ → ℂ)
    (tmH : ℕ → Bool) (lH : ℕ → ℕ) (PH : ℕ → Poly) (cH : ℕ → ℂ) (s : ℕ) (u : Plane) : ℂ :=
  crossProduct (seriesElectric q hq n tmE lE PE cE s (MaxwellPlaneTail.planePoint u))
    (conjugate (seriesMagnetic q hq n tmH lH PH cH s (MaxwellPlaneTail.planePoint u))) 2

theorem modeElectric_aesm_outside (tm : Bool) (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    AEStronglyMeasurable (fun u : Plane => modeElectric tm d P (MaxwellPlaneTail.planePoint u))
      (volume.restrict {u : Plane | d.R<‖u‖}) := by
  have hRX : d.R ≤ d.X := RadialStack.chain_ordered d.chain
  have hset : {u : Plane | d.R<‖u‖}=annSection d.R d.X ∪ {u : Plane | d.X<‖u‖} := by
    ext u
    simp only [annSection,mem_setOf_eq,mem_union]
    constructor
    · intro h
      by_cases hX : ‖u‖ ≤ d.X
      · exact Or.inl ⟨h,hX⟩
      · exact Or.inr (not_le.mp hX)
    · rintro (h | h)
      · exact h.1
      · exact lt_of_le_of_lt hRX h
  have hdisj : Disjoint (annSection d.R d.X) {u : Plane | d.X<‖u‖} := by
    rw [Set.disjoint_left]
    intro u h1 h2
    exact absurd h1.2 (not_le.mpr h2)
  have hmaps : MapsTo MaxwellPlaneTail.planePoint {u : Plane | d.X<‖u‖} {x : Space | d.X<‖x‖} := by
    intro u hu
    change d.X<‖MaxwellPlaneTail.planePoint u‖
    rw [MaxwellPlaneTail.planePoint_norm]
    exact hu
  have hext : AEStronglyMeasurable (fun u : Plane => modeElectric tm d P (MaxwellPlaneTail.planePoint u))
      (volume.restrict {u : Plane | d.X<‖u‖}) :=
    ((SourceRemotePlaneBandTail.modeElectric_continuousOn tm d P hp).comp
      MaxwellPlaneTail.planePoint_continuous.continuousOn hmaps).aestronglyMeasurable
      (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [hset,Measure.restrict_union hdisj (isOpen_lt continuous_const continuous_norm).measurableSet]
  exact (modeElectric_aesm tm d P hp).add_measure hext

theorem modeMagnetic_aesm_outside (tm : Bool) (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    AEStronglyMeasurable (fun u : Plane => modeMagnetic tm d P (MaxwellPlaneTail.planePoint u))
      (volume.restrict {u : Plane | d.R<‖u‖}) := by
  have hRX : d.R ≤ d.X := RadialStack.chain_ordered d.chain
  have hset : {u : Plane | d.R<‖u‖}=annSection d.R d.X ∪ {u : Plane | d.X<‖u‖} := by
    ext u
    simp only [annSection,mem_setOf_eq,mem_union]
    constructor
    · intro h
      by_cases hX : ‖u‖ ≤ d.X
      · exact Or.inl ⟨h,hX⟩
      · exact Or.inr (not_le.mp hX)
    · rintro (h | h)
      · exact h.1
      · exact lt_of_le_of_lt hRX h
  have hdisj : Disjoint (annSection d.R d.X) {u : Plane | d.X<‖u‖} := by
    rw [Set.disjoint_left]
    intro u h1 h2
    exact absurd h1.2 (not_le.mpr h2)
  have hmaps : MapsTo MaxwellPlaneTail.planePoint {u : Plane | d.X<‖u‖} {x : Space | d.X<‖x‖} := by
    intro u hu
    change d.X<‖MaxwellPlaneTail.planePoint u‖
    rw [MaxwellPlaneTail.planePoint_norm]
    exact hu
  have hext : AEStronglyMeasurable (fun u : Plane => modeMagnetic tm d P (MaxwellPlaneTail.planePoint u))
      (volume.restrict {u : Plane | d.X<‖u‖}) :=
    ((SourceRemotePlaneBandTail.modeMagnetic_continuousOn tm d P hp).comp
      MaxwellPlaneTail.planePoint_continuous.continuousOn hmaps).aestronglyMeasurable
      (isOpen_lt continuous_const continuous_norm).measurableSet
  rw [hset,Measure.restrict_union hdisj (isOpen_lt continuous_const continuous_norm).measurableSet]
  exact (modeMagnetic_aesm tm d P hp).add_measure hext

theorem series_outside_core_flux_tendsto (q : ℝ) (hq : 0<q) (n : ℕ)
    (tmE : ℕ → Bool) (lE : ℕ → ℕ) (PE : ℕ → Poly) (hPE : ∀ i, (PE i).IsHomogeneous (lE i)) (cE : ℕ → ℂ)
    (tmH : ℕ → Bool) (lH : ℕ → ℕ) (PH : ℕ → Poly) (hPH : ∀ i, (PH i).IsHomogeneous (lH i)) (cH : ℕ → ℂ)
    (K1 K2 L1 L2 : ℕ → ℝ) (hK1 : Summable K1) (hK2 : Summable K2) (hL1 : Summable L1) (hL2 : Summable L2)
    (s1 : ℕ)
    (hE : ∀ (i s : ℕ) (x : Space), s1 ≤ s → (SourcePairedGeometry.physicalData q hq n s).R<‖x‖ →
      Decomp (K1 i) (K2 i) (cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i }
        (PE i) x) x)
    (hH : ∀ (i s : ℕ) (x : Space), s1 ≤ s → (SourcePairedGeometry.physicalData q hq n s).R<‖x‖ →
      Decomp (L1 i) (L2 i) (cH i • modeMagnetic (tmH i) { SourcePairedGeometry.physicalData q hq n s with l := lH i }
        (PH i) x) x) :
    Tendsto (fun s : ℕ => ∫ u : Plane in {u : Plane | (SourcePairedGeometry.physicalData q hq n s).R<‖u‖},
      ‖seriesFlux q hq n tmE lE PE cE tmH lH PH cH s u‖) atTop (𝓝 0) := by
  let C : ℝ := 2*(∑' i, K2 i)*(∑' i, L1 i)+2*(∑' i, K1 i)*(∑' i, L2 i)
  have hup : Tendsto (fun s : ℕ => C*diskConstant/(SourcePairedGeometry.physicalData q hq n s).R) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := C*diskConstant)).div_atTop RadialPhaseLimit.radius_tendsto
  apply squeeze_zero' (Eventually.of_forall (fun s => integral_nonneg (fun u => norm_nonneg _))) _ hup
  filter_upwards [eventually_ge_atTop s1] with s hs
  let S : Set Plane := {u : Plane | (SourcePairedGeometry.physicalData q hq n s).R<‖u‖}
  have hSm : MeasurableSet S := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hT : 0<(SourcePairedGeometry.physicalData q hq n s).R := (SourcePairedGeometry.physicalData q hq n s).hR
  have hpt : ∀ u : Plane, u ∈ S → MaxwellPlaneTail.planePoint u≠0 ∧
      (SourcePairedGeometry.physicalData q hq n s).R<‖MaxwellPlaneTail.planePoint u‖ := by
    intro u hu
    have hu' : (SourcePairedGeometry.physicalData q hq n s).R<‖u‖ := hu
    have hn : (SourcePairedGeometry.physicalData q hq n s).R<‖MaxwellPlaneTail.planePoint u‖ := by
      rw [MaxwellPlaneTail.planePoint_norm]; exact hu'
    exact ⟨norm_pos_iff.mp (hT.trans hn),hn⟩
  -- measurability of the two series on the outside-core section
  have hEs : AEStronglyMeasurable (fun u : Plane =>
      seriesElectric q hq n tmE lE PE cE s (MaxwellPlaneTail.planePoint u)) (volume.restrict S) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (N : ℕ) (u : Plane) => ∑ i ∈ Finset.range N, cE i • modeElectric (tmE i)
        { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i) (MaxwellPlaneTail.planePoint u))
    · intro N
      exact Finset.aestronglyMeasurable_sum (Finset.range N)
        (fun i _ => (modeElectric_aesm_outside (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i }
          (PE i) (hPE i)).const_smul (cE i))
    · apply ae_restrict_of_forall_mem hSm
      intro u hu
      obtain ⟨hx0,hxR⟩ := hpt u hu
      exact (decomp_tsum _ K1 K2 hK1 hK2 _ hx0 (fun i => hE i s _ hs hxR)).1.hasSum.tendsto_sum_nat
  have hHs : AEStronglyMeasurable (fun u : Plane =>
      seriesMagnetic q hq n tmH lH PH cH s (MaxwellPlaneTail.planePoint u)) (volume.restrict S) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (N : ℕ) (u : Plane) => ∑ i ∈ Finset.range N, cH i • modeMagnetic (tmH i)
        { SourcePairedGeometry.physicalData q hq n s with l := lH i } (PH i) (MaxwellPlaneTail.planePoint u))
    · intro N
      exact Finset.aestronglyMeasurable_sum (Finset.range N)
        (fun i _ => (modeMagnetic_aesm_outside (tmH i) { SourcePairedGeometry.physicalData q hq n s with l := lH i }
          (PH i) (hPH i)).const_smul (cH i))
    · apply ae_restrict_of_forall_mem hSm
      intro u hu
      obtain ⟨hx0,hxR⟩ := hpt u hu
      exact (decomp_tsum _ L1 L2 hL1 hL2 _ hx0 (fun i => hH i s _ hs hxR)).1.hasSum.tendsto_sum_nat
  have hF : AEStronglyMeasurable (seriesFlux q hq n tmE lE PE cE tmH lH PH cH s) (volume.restrict S) := by
    unfold seriesFlux
    simp only [SourceRemotePlaneFlux.cross_two,conjugate]
    have hEi (i : Fin 3) := (continuous_apply i).comp_aestronglyMeasurable hEs
    have hHi (i : Fin 3) := Complex.continuous_conj.comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hHs)
    exact ((hEi 0).mul (hHi 1)).sub ((hEi 1).mul (hHi 0))
  have hb : ∀ u : Plane, (SourcePairedGeometry.physicalData q hq n s).R<‖u‖ →
      ‖seriesFlux q hq n tmE lE PE cE tmH lH PH cH s u‖ ≤ C/‖u‖^3 := by
    intro u hu
    obtain ⟨hx0,hxR⟩ := hpt u hu
    have hDE := (decomp_tsum _ K1 K2 hK1 hK2 _ hx0 (fun i => hE i s _ hs hxR)).2
    have hDH := (decomp_tsum _ L1 L2 hL1 hL2 _ hx0 (fun i => hH i s _ hs hxR)).2
    have := flux_bound_of_decomp (MaxwellPlaneTail.planePoint u) (SourceRemotePlaneTail.planePoint_two u)
      (norm_pos_iff.mpr hx0) _ _ _ _ _ _ hDE hDH
    rw [MaxwellPlaneTail.planePoint_norm] at this
    exact this
  exact tail_integral_bound _ C hT hF hb

end OQ14.SourceRemotePlaneSeries
#print axioms OQ14.SourceRemotePlaneSeries.decomp_tsum
#print axioms OQ14.SourceRemotePlaneSeries.series_flux_bound
#print axioms OQ14.SourceRemotePlaneSeries.modeElectric_aesm_outside
#print axioms OQ14.SourceRemotePlaneSeries.modeMagnetic_aesm_outside
#print axioms OQ14.SourceRemotePlaneSeries.series_outside_core_flux_tendsto
