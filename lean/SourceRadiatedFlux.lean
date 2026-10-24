import SourceRadiatedSeries
import SourceRadiatedMagnetic
import BarrierDegreeSeriesFlux

/-! The all-degree flux theorem for the radiated mode series of the paired shells.  The abstract series theorem
of `SourceRemotePlaneSeries` is generalized to modes with mode-dependent data, an arbitrary
countable index set and shell-dependent coefficients; the physical decomposition of the paired shells
is supplied for the TE chain (the layers with `σ = 1`) as well as for the TM chain; the moments of an
inclusion source bounded in mass are normalized at the inner scale for the degrees above its barrier and at
scale one for the finitely many degrees below it.  This gives the absolute plane flux theorem for the
series of the radiated field outside the core, and the identification of this series with the electric
and magnetic fields radiated by the inclusion outside the shell. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.SourceRadiatedFlux
open MeasureTheory Set Metric Filter Complex OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.SourceRemotePlaneBand OQ14.PlaneInverseCube OQ14.SourceAnnulusPlaneFlux
  OQ14.SourceRemotePlaneSeries OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open scoped Topology ComplexConjugate

/-! ### Series of layered modes with mode-dependent data, shell-dependent coefficients -/

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
    have hlim := hs2.hasSum
    have hmem : ∀ N : Finset ι, ∑ i ∈ N, Er i ∈ (V : Set Vector) := by
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


/-- The electric series at shell index `s` of a family of modes with data `D i s`, polarization flags
`tm i`, polynomials `P i` and coefficients `c s i`. -/
def genElectric {ι : Type*} (D : ι → ℕ → Data) (tm : ι → Bool) (P : ι → Poly) (c : ℕ → ι → ℂ) (s : ℕ)
    (x : Space) : Vector :=
  ∑' i, c s i • modeElectric (tm i) (D i s) (P i) x

/-- The magnetic series at shell index `s` of the same family. -/
def genMagnetic {ι : Type*} (D : ι → ℕ → Data) (tm : ι → Bool) (P : ι → Poly) (c : ℕ → ι → ℂ) (s : ℕ)
    (x : Space) : Vector :=
  ∑' i, c s i • modeMagnetic (tm i) (D i s) (P i) x

/-- The plane flux density of the series at shell index `s`. -/
def genFlux {ι : Type*} (D : ι → ℕ → Data) (tm : ι → Bool) (P : ι → Poly) (c : ℕ → ι → ℂ) (s : ℕ)
    (u : Plane) : ℂ :=
  crossProduct (genElectric D tm P c s (MaxwellPlaneTail.planePoint u))
    (conjugate (genMagnetic D tm P c s (MaxwellPlaneTail.planePoint u))) 2

/-- The measurability and the inverse-cube bound of the series flux at a fixed shell index. -/
theorem gen_series_flux_data {ι : Type*} [Countable ι] (D : ι → ℕ → Data) (tm : ι → Bool)
    (P : ι → Poly) (hP : ∀ i s, (P i).IsHomogeneous (D i s).l)
    (hDR : ∀ i s, (D i s).R = RadialPhaseLimit.radius s) (c : ℕ → ι → ℂ)
    (K1 K2 L1 L2 : ι → ℝ) (hK1 : Summable K1) (hK2 : Summable K2) (hL1 : Summable L1)
    (hL2 : Summable L2) (s1 : ℕ)
    (s : ℕ) (hs : s1 ≤ s)
    (hE : ∀ (i : ι) (s : ℕ) (x : Space), s1 ≤ s → RadialPhaseLimit.radius s < ‖x‖ →
      Decomp (K1 i) (K2 i) (c s i • modeElectric (tm i) (D i s) (P i) x) x)
    (hH : ∀ (i : ι) (s : ℕ) (x : Space), s1 ≤ s → RadialPhaseLimit.radius s < ‖x‖ →
      Decomp (L1 i) (L2 i) (c s i • modeMagnetic (tm i) (D i s) (P i) x) x) :
    AEStronglyMeasurable (genFlux D tm P c s) (volume.restrict {u : Plane | RadialPhaseLimit.radius s < ‖u‖}) ∧
    ∀ u : Plane, RadialPhaseLimit.radius s < ‖u‖ → ‖genFlux D tm P c s u‖ ≤
      (2*(∑' i, K2 i)*(∑' i, L1 i)+2*(∑' i, K1 i)*(∑' i, L2 i))/‖u‖^3 := by
  let C : ℝ := 2*(∑' i, K2 i)*(∑' i, L1 i)+2*(∑' i, K1 i)*(∑' i, L2 i)
  let S : Set Plane := {u : Plane | RadialPhaseLimit.radius s < ‖u‖}
  have hSm : MeasurableSet S := (isOpen_lt continuous_const continuous_norm).measurableSet
  have hT : 0 < RadialPhaseLimit.radius s := RadialPhaseLimit.radius_pos s
  have hpt : ∀ u : Plane, u ∈ S → MaxwellPlaneTail.planePoint u ≠ 0 ∧
      RadialPhaseLimit.radius s < ‖MaxwellPlaneTail.planePoint u‖ := by
    intro u hu
    have hu' : RadialPhaseLimit.radius s < ‖u‖ := hu
    have hn : RadialPhaseLimit.radius s < ‖MaxwellPlaneTail.planePoint u‖ := by
      rw [MaxwellPlaneTail.planePoint_norm]; exact hu'
    exact ⟨norm_pos_iff.mp (hT.trans hn), hn⟩
  have hEs : AEStronglyMeasurable (fun u : Plane =>
      genElectric D tm P c s (MaxwellPlaneTail.planePoint u)) (volume.restrict S) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (N : Finset ι) (u : Plane) => ∑ i ∈ N, c s i • modeElectric (tm i) (D i s) (P i)
        (MaxwellPlaneTail.planePoint u))
    · intro N
      refine Finset.aestronglyMeasurable_sum N (fun i _ => ?_)
      have h := (modeElectric_aesm_outside (tm i) (D i s) (P i) (hP i s)).const_smul (c s i)
      rw [hDR i s] at h
      exact h
    · apply ae_restrict_of_forall_mem hSm
      intro u hu
      obtain ⟨hx0, hxR⟩ := hpt u hu
      exact (decomp_tsum_gen _ K1 K2 hK1 hK2 _ hx0 (fun i => hE i s _ hs hxR)).1.hasSum
  have hHs : AEStronglyMeasurable (fun u : Plane =>
      genMagnetic D tm P c s (MaxwellPlaneTail.planePoint u)) (volume.restrict S) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (N : Finset ι) (u : Plane) => ∑ i ∈ N, c s i • modeMagnetic (tm i) (D i s) (P i)
        (MaxwellPlaneTail.planePoint u))
    · intro N
      refine Finset.aestronglyMeasurable_sum N (fun i _ => ?_)
      have h := (modeMagnetic_aesm_outside (tm i) (D i s) (P i) (hP i s)).const_smul (c s i)
      rw [hDR i s] at h
      exact h
    · apply ae_restrict_of_forall_mem hSm
      intro u hu
      obtain ⟨hx0, hxR⟩ := hpt u hu
      exact (decomp_tsum_gen _ L1 L2 hL1 hL2 _ hx0 (fun i => hH i s _ hs hxR)).1.hasSum
  have hF : AEStronglyMeasurable (genFlux D tm P c s) (volume.restrict S) := by
    unfold genFlux
    simp only [SourceRemotePlaneFlux.cross_two, conjugate]
    have hEi (i : Fin 3) := (continuous_apply i).comp_aestronglyMeasurable hEs
    have hHi (i : Fin 3) := Complex.continuous_conj.comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hHs)
    exact ((hEi 0).mul (hHi 1)).sub ((hEi 1).mul (hHi 0))
  have hb : ∀ u : Plane, RadialPhaseLimit.radius s < ‖u‖ → ‖genFlux D tm P c s u‖ ≤ C/‖u‖^3 := by
    intro u hu
    obtain ⟨hx0, hxR⟩ := hpt u hu
    have hDE := (decomp_tsum_gen _ K1 K2 hK1 hK2 _ hx0 (fun i => hE i s _ hs hxR)).2
    have hDH := (decomp_tsum_gen _ L1 L2 hL1 hL2 _ hx0 (fun i => hH i s _ hs hxR)).2
    have := flux_bound_of_decomp (MaxwellPlaneTail.planePoint u)
      (SourceRemotePlaneTail.planePoint_two u) (norm_pos_iff.mpr hx0) _ _ _ _ _ _ hDE hDH
    rw [MaxwellPlaneTail.planePoint_norm] at this
    exact this
  exact ⟨hF, hb⟩

/-- **Plane flux of a series of layered modes with mode-dependent data and shell-dependent
coefficients.**  If for every mode `i` and every shell index `s ≥ s1` the electric and magnetic
fields `c s i • mode` decompose at every point outside the inner radius with shell-independent
degree-summable constants, the absolute plane flux of the series over `{radius s < ‖u‖}` tends to zero
with the shell index. -/
theorem gen_series_flux_tendsto {ι : Type*} [Countable ι] (D : ι → ℕ → Data) (tm : ι → Bool)
    (P : ι → Poly) (hP : ∀ i s, (P i).IsHomogeneous (D i s).l)
    (hDR : ∀ i s, (D i s).R = RadialPhaseLimit.radius s) (c : ℕ → ι → ℂ)
    (K1 K2 L1 L2 : ι → ℝ) (hK1 : Summable K1) (hK2 : Summable K2) (hL1 : Summable L1)
    (hL2 : Summable L2) (s1 : ℕ)
    (hE : ∀ (i : ι) (s : ℕ) (x : Space), s1 ≤ s → RadialPhaseLimit.radius s < ‖x‖ →
      Decomp (K1 i) (K2 i) (c s i • modeElectric (tm i) (D i s) (P i) x) x)
    (hH : ∀ (i : ι) (s : ℕ) (x : Space), s1 ≤ s → RadialPhaseLimit.radius s < ‖x‖ →
      Decomp (L1 i) (L2 i) (c s i • modeMagnetic (tm i) (D i s) (P i) x) x) :
    Tendsto (fun s : ℕ => ∫ u : Plane in {u : Plane | RadialPhaseLimit.radius s < ‖u‖},
      ‖genFlux D tm P c s u‖) atTop (𝓝 0) := by
  let C : ℝ := 2*(∑' i, K2 i)*(∑' i, L1 i)+2*(∑' i, K1 i)*(∑' i, L2 i)
  have hup : Tendsto (fun s : ℕ => C*diskConstant/RadialPhaseLimit.radius s) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := C*diskConstant)).div_atTop RadialPhaseLimit.radius_tendsto
  apply squeeze_zero' (Eventually.of_forall (fun s => integral_nonneg (fun u => norm_nonneg _))) _ hup
  filter_upwards [eventually_ge_atTop s1] with s hs
  obtain ⟨hF, hb⟩ := gen_series_flux_data D tm P hP hDR c K1 K2 L1 L2 hK1 hK2 hL1 hL2 s1 s hs hE hH
  exact tail_integral_bound _ C (RadialPhaseLimit.radius_pos s) hF hb

/-! ### The decomposition of the physical TE mode of the TE chain of the paired shells -/

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- **Per-mode decomposition for the physical TE mode.**  The TE chain of the paired shell data
(the layers with `σ = 1`) satisfies the same parameter bounds as the TM chain, so the normalized TE electric
and magnetic modes of the TE chain decompose exactly as in `paired_mode_decomp`. -/
theorem paired_mode_decomp_te (q : ℝ) (hq : 0<q) (hq1 : 1 ≤ q) (n : ℕ) (s0 : ℝ) (hs0 : 0<s0)
    (l : ℕ) (m : Index l) (s : ℕ) (x : Space) (hs : s1pair q hq n s0 ≤ s)
    (hx : (OQ14.SourcePairedGeometry.physicalData q hq n s).R<‖x‖) :
    Decomp (mK1 false q (Wpair q hq n) s0 (R1pair q hq n s0) l)
      (mK2 false q (Wpair q hq n) s0 (R1pair q hq n s0) l)
      (((HankelRealBasis.regular l s0 : ℝ) : ℂ) •
        modeElectric false (SourceDielectricModes.teData
          (OQ14.SourcePairedGeometry.physicalData q hq n s) l) (representative l m) x) x ∧
    Decomp (mL1 false q (Wpair q hq n) s0 (R1pair q hq n s0) l)
      (mL2 false q (Wpair q hq n) s0 (R1pair q hq n s0) l)
      (((HankelRealBasis.regular l s0 : ℝ) : ℂ) •
        modeMagnetic false (SourceDielectricModes.teData
          (OQ14.SourcePairedGeometry.physicalData q hq n s) l) (representative l m) x) x := by
  have hrad := radius_ge_R1pair q hq n s0 s hs
  have hmax := R1pair_max_le q hq n s0
  have hWR : Wpair q hq n ≤ R1pair q hq n s0 :=
    le_trans (le_trans (le_max_left (Wpair q hq n) s0) (le_max_right 1 _)) hmax
  have hpar := OQ14.SourcePairedGeometry.physical_parameters q hq hq1 n s
  have hW : (OQ14.SourcePairedGeometry.physicalData q hq n s).X-
      (OQ14.SourcePairedGeometry.physicalData q hq n s).R ≤ Wpair q hq n :=
    le_of_eq (by
      show OQ14.RadialPhaseLimit.radius s+OQ14.RadialFiniteLimit.width (OQ14.RadialPairedFamily.tm q hq n)-
        OQ14.RadialPhaseLimit.radius s=Wpair q hq n
      unfold Wpair; ring)
  have hX : (OQ14.SourcePairedGeometry.physicalData q hq n s).X ≤
      2*(OQ14.SourcePairedGeometry.physicalData q hq n s).R := by
    show OQ14.RadialPhaseLimit.radius s+OQ14.RadialFiniteLimit.width (OQ14.RadialPairedFamily.tm q hq n) ≤
      2*OQ14.RadialPhaseLimit.radius s
    have : Wpair q hq n ≤ OQ14.RadialPhaseLimit.radius s := hWR.trans hrad
    unfold Wpair at this
    linarith
  have hq2 : 1 ≤ q^2 := by nlinarith
  have hTE (g : RadialStack.Layer) (hg : g ∈ (SourceDielectricModes.teData
      (OQ14.SourcePairedGeometry.physicalData q hq n s) l).gs) :
      1 ≤ g.σ ∧ g.σ ≤ q^2 ∧ g.q^2 ≤ q^2 ∧ g.q ≤ q := by
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have h0 := hpar g0 hg0
    exact ⟨le_rfl, hq2, h0.2.2.1, h0.2.2.2⟩
  obtain ⟨hE, hH⟩ := mode_decomp_uniform (SourceDielectricModes.teData
    (OQ14.SourcePairedGeometry.physicalData q hq n s) l) m
    q (Wpair q hq n) s0 (R1pair q hq n s0) hq1 hW hmax hrad hX
    (fun g hg => ⟨(hTE g hg).1, (hTE g hg).2.1, (hTE g hg).2.2.1⟩)
    (fun g hg => (hTE g hg).2.2.2) hs0 x hx
  have hE' := decomp_smul (-1 : ℂ) hE
  have hn : ‖(-1 : ℂ)‖=1 := by simp
  rw [hn, one_mul, one_mul] at hE'
  have heq : ((HankelRealBasis.regular l s0 : ℝ) : ℂ) •
      SourceGeneralMaxwell.teMagnetic (SourceDielectricModes.teData
        (OQ14.SourcePairedGeometry.physicalData q hq n s) l) (representative l m) x =
      (-1 : ℂ) • (((HankelRealBasis.regular l s0 : ℝ) : ℂ) • SourceUnclippedMaxwell.electric
        (SourceDielectricModes.teData (OQ14.SourcePairedGeometry.physicalData q hq n s) l)
        (representative l m) x) := by
    funext i
    simp [SourceGeneralMaxwell.teMagnetic]
  simp only [modeElectric, modeMagnetic, Bool.false_eq_true, if_false, SourceGeneralMaxwell.teElectric,
    mK1, mK2, mL1, mL2, heq]
  exact ⟨hH, hE'⟩

/-! ### Bookkeeping for the all-degree series of the radiated field -/

/-- The two-sorted mode index: `inl a` is the TM mode and `inr a` the TE mode of degree `a.1+1`. -/
abbrev ModeIdx := PositiveIndex ⊕ PositiveIndex

/-- The layered data of the mode index `i` at shell index `s`: the TM chain for `inl` and the TE chain
(layers with `σ = 1`) for `inr`. -/
def dataFam (q : ℝ) (hq : 0 < q) (n : ℕ) : ModeIdx → ℕ → Data
  | Sum.inl a, s => SourceDielectricModes.tmData (OQ14.SourcePairedGeometry.physicalData q hq n s) (a.1+1)
  | Sum.inr a, s => SourceDielectricModes.teData (OQ14.SourcePairedGeometry.physicalData q hq n s) (a.1+1)

/-- The polarization flag of the mode index (`true` for TM). -/
def tmFlag : ModeIdx → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

/-- The harmonic polynomial of the mode index. -/
def polyFam : ModeIdx → Poly
  | Sum.inl a => (representative (a.1+1) a.2 : Poly)
  | Sum.inr a => (representative (a.1+1) a.2 : Poly)

/-- The degree of the mode index. -/
def degFam : ModeIdx → ℕ
  | Sum.inl a => a.1+1
  | Sum.inr a => a.1+1

/-- The moment coefficients of the shell-indexed family of current densities. -/
def coeffFam (ρ : ℕ → Fin 3 → Space → ℂ) : ℕ → ModeIdx → ℂ
  | s, Sum.inl a => SourceRadiatedSeries.tmMoment a (ρ s)
  | s, Sum.inr a => SourceRadiatedSeries.teMoment a (ρ s)

theorem dataFam_R (q : ℝ) (hq : 0 < q) (n : ℕ) (i : ModeIdx) (s : ℕ) :
    (dataFam q hq n i s).R = RadialPhaseLimit.radius s := by
  cases i <;> rfl

theorem polyFam_hom (q : ℝ) (hq : 0 < q) (n : ℕ) (i : ModeIdx) (s : ℕ) :
    (polyFam i).IsHomogeneous (dataFam q hq n i s).l := by
  cases i with
  | inl a => exact representative_homogeneous (a.1+1) a.2
  | inr a => exact representative_homogeneous (a.1+1) a.2

/-- Degrees whose barrier lies above the inner scale are treated at the inner scale; the finitely many
others at scale one. -/
def innerScale (s0 : ℝ) (l : ℕ) : ℝ := by
  classical
  exact if s0^2 < RiccatiBarrier.ν l then s0 else 1

theorem regular_pos_of_barrier (σ : ℝ) (hσ : 0 < σ) (l : ℕ) (hbar : σ^2 < RiccatiBarrier.ν l) :
    0 < HankelRealBasis.regular l σ := by
  have hlow := RiccatiGaussianBound.regular_gaussian_lower l σ hσ hbar σ ⟨hσ, le_rfl⟩
  have hamp := RiccatiSeriesCoefficients.amplitude_pos l 0
  refine lt_of_lt_of_le ?_ hlow
  positivity

theorem one_lt_barrier (l : ℕ) (hl : 1 ≤ l) : (1 : ℝ)^2 < RiccatiBarrier.ν l := by
  unfold RiccatiBarrier.ν
  have : (1 : ℝ) ≤ l := by exact_mod_cast hl
  nlinarith

theorem innerScale_pos (s0 : ℝ) (hs0 : 0 < s0) (l : ℕ) : 0 < innerScale s0 l := by
  unfold innerScale
  split_ifs <;> first | exact hs0 | exact one_pos

theorem innerScale_barrier (s0 : ℝ) (l : ℕ) (hl : 1 ≤ l) :
    (innerScale s0 l)^2 < RiccatiBarrier.ν l := by
  unfold innerScale
  split_ifs with h
  · exact h
  · exact one_lt_barrier l hl

theorem finite_low_degrees (s0 : ℝ) :
    Set.Finite {a : PositiveIndex | ¬ s0^2 < RiccatiBarrier.ν (a.1+1)} := by
  have hN : ∃ N : ℕ, s0^2 ≤ N := exists_nat_ge _
  obtain ⟨N, hN⟩ := hN
  refine Set.Finite.subset (((Finset.range (N+1)).sigma (fun l => (Finset.univ : Finset (Index (l+1))))).finite_toSet) ?_
  intro a ha
  simp only [Set.mem_setOf_eq, not_lt, RiccatiBarrier.ν] at ha
  simp only [Finset.coe_sigma, Finset.coe_range, Finset.coe_univ, Set.mem_sigma_iff, Set.mem_Iio,
    Set.mem_univ, and_true]
  have h1 : ((a.1 : ℝ)+1)*((a.1 : ℝ)+1+1) ≤ N := by
    have := ha
    push_cast at this
    linarith
  have h2 : (a.1 : ℝ) < N+1 := by
    have : (0 : ℝ) ≤ a.1 := Nat.cast_nonneg _
    nlinarith
  exact_mod_cast h2

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- The decomposition of the normalized mode of any index at any positive scale, for the TM and the TE
chains alike. -/
theorem index_decomp (q : ℝ) (hq : 0 < q) (hq1 : 1 ≤ q) (n : ℕ) (σ : ℝ) (hσ : 0 < σ) (i : ModeIdx)
    (s : ℕ) (x : Space) (hs : s1pair q hq n σ ≤ s) (hx : RadialPhaseLimit.radius s < ‖x‖) :
    Decomp (mK1 (tmFlag i) q (Wpair q hq n) σ (R1pair q hq n σ) (degFam i))
      (mK2 (tmFlag i) q (Wpair q hq n) σ (R1pair q hq n σ) (degFam i))
      (((HankelRealBasis.regular (degFam i) σ : ℝ) : ℂ) •
        modeElectric (tmFlag i) (dataFam q hq n i s) (polyFam i) x) x ∧
    Decomp (mL1 (tmFlag i) q (Wpair q hq n) σ (R1pair q hq n σ) (degFam i))
      (mL2 (tmFlag i) q (Wpair q hq n) σ (R1pair q hq n σ) (degFam i))
      (((HankelRealBasis.regular (degFam i) σ : ℝ) : ℂ) •
        modeMagnetic (tmFlag i) (dataFam q hq n i s) (polyFam i) x) x := by
  cases i with
  | inl a => exact paired_mode_decomp true q hq hq1 n σ hσ (a.1+1) a.2 s x hs hx
  | inr a => exact paired_mode_decomp_te q hq hq1 n σ hσ (a.1+1) a.2 s x hs hx

/-- The index of the positive-degree mode underlying a two-sorted mode index. -/
def idxOf : ModeIdx → PositiveIndex
  | Sum.inl a => a
  | Sum.inr a => a

theorem degFam_eq (i : ModeIdx) : degFam i = (idxOf i).1 + 1 := by cases i <;> rfl

/-- Bound of the moments of a family of current densities with `L¹` masses at most `M`, relative to the
regular Riccati value at the inner scale of the degree: above the barrier it is the explicit constant of
`moment_barrier_bound`, at the finitely many low degrees the crude Taylor constant divided by the regular
value at scale one. -/
def momentRat (b B s0 M : ℝ) (a : PositiveIndex) : ℝ :=
  if s0^2 < RiccatiBarrier.ν (a.1+1) then
    M * DebyeJetBounds.scale 0 b * (6/(1-B/s0)^4) * Real.exp (s0^2/8) / s0
  else M * SourceRadiatedSeries.momentConst b B a / HankelRealBasis.regular (a.1+1) 1

theorem momentRat_nonneg (b B s0 M : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B) (hBs : B < s0) (hs0 : 0 < s0)
    (hM : 0 ≤ M) (a : PositiveIndex) : 0 ≤ momentRat b B s0 M a := by
  unfold momentRat
  split_ifs with h
  · have hS := DebyeJetBounds.scale_nonnegative 0 b hb
    have hr1 : B / s0 < 1 := (div_lt_one hs0).mpr hBs
    have h6 : 0 < 6 / (1 - B/s0)^4 := by
      have : 0 < 1 - B/s0 := by linarith
      positivity
    positivity
  · have hreg := regular_pos_of_barrier 1 one_pos (a.1+1) (one_lt_barrier (a.1+1) (Nat.succ_le_succ (Nat.zero_le _)))
    have hmc : 0 ≤ SourceRadiatedSeries.momentConst b B a := by
      unfold SourceRadiatedSeries.momentConst
      have hS := DebyeJetBounds.scale_nonnegative 0 b hb
      have hA := (RiccatiSeriesCoefficients.amplitude_pos (a.1+1) 0).le
      positivity
    positivity

theorem moment_le_rat (b B s0 M : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0) (hs0 : 0 < s0)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (hmass : SourceRadiatedSeries.mass ρ ≤ M) (a : PositiveIndex) :
    ‖SourceRadiatedSeries.tmMoment a ρ‖ ≤ momentRat b B s0 M a *
        HankelRealBasis.regular (a.1+1) (innerScale s0 (a.1+1)) ∧
      ‖SourceRadiatedSeries.teMoment a ρ‖ ≤ momentRat b B s0 M a *
        HankelRealBasis.regular (a.1+1) (innerScale s0 (a.1+1)) := by
  have hl1 : 1 ≤ a.1+1 := Nat.succ_le_succ (Nat.zero_le _)
  have hmass0 := SourceRadiatedSeries.mass_nonneg ρ
  by_cases h : s0^2 < RiccatiBarrier.ν (a.1+1)
  · have hsc : innerScale s0 (a.1+1) = s0 := by unfold innerScale; simp [h]
    have hrat : momentRat b B s0 M a = M * DebyeJetBounds.scale 0 b * (6/(1-B/s0)^4) *
        Real.exp (s0^2/8) / s0 := by unfold momentRat; simp [h]
    rw [hsc, hrat]
    have hb' := SourceRadiatedSeries.moment_barrier_bound b B s0 hb hB hscale hBs hs0 ρ hρ hsupp a h
    have hreg0 := (regular_pos_of_barrier s0 hs0 (a.1+1) h).le
    have hS := DebyeJetBounds.scale_nonnegative 0 b hb
    have hr1 : B / s0 < 1 := (div_lt_one hs0).mpr hBs
    have h6 : 0 < 6 / (1 - B/s0)^4 := by
      have : 0 < 1 - B/s0 := by linarith
      positivity
    have hA : SourceRadiatedSeries.momentA b B s0 ρ ≤ M * DebyeJetBounds.scale 0 b * (6/(1-B/s0)^4) *
        Real.exp (s0^2/8) / s0 := by
      unfold SourceRadiatedSeries.momentA
      apply div_le_div_of_nonneg_right _ hs0.le
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_right _ h6.le
      exact mul_le_mul_of_nonneg_right hmass hS
    exact ⟨hb'.1.trans (mul_le_mul_of_nonneg_right hA hreg0),
      hb'.2.trans (mul_le_mul_of_nonneg_right hA hreg0)⟩
  · have hsc : innerScale s0 (a.1+1) = 1 := by unfold innerScale; simp [h]
    have hrat : momentRat b B s0 M a = M * SourceRadiatedSeries.momentConst b B a /
        HankelRealBasis.regular (a.1+1) 1 := by unfold momentRat; simp [h]
    rw [hsc, hrat]
    have hreg := regular_pos_of_barrier 1 one_pos (a.1+1) (one_lt_barrier (a.1+1) hl1)
    have hm := SourceRadiatedSeries.moment_norm_le b B hb hB hscale ρ hρ hsupp a
    have hmc : 0 ≤ SourceRadiatedSeries.momentConst b B a := by
      unfold SourceRadiatedSeries.momentConst
      have hS := DebyeJetBounds.scale_nonnegative 0 b hb
      have hA := (RiccatiSeriesCoefficients.amplitude_pos (a.1+1) 0).le
      positivity
    have e : M * SourceRadiatedSeries.momentConst b B a / HankelRealBasis.regular (a.1+1) 1 *
        HankelRealBasis.regular (a.1+1) 1 = SourceRadiatedSeries.momentConst b B a * M := by
      field_simp
      ring
    rw [e]
    exact ⟨hm.1.trans (mul_le_mul_of_nonneg_left hmass hmc),
      hm.2.trans (mul_le_mul_of_nonneg_left hmass hmc)⟩

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- The constants of the decomposition of the shell-indexed radiated series: the bound of the moments
relative to the regular value at the inner scale of the degree, times the constants of the normalized
mode at that scale. -/
def Kc (G : Bool → ℝ → ℝ → ℝ → ℝ → ℕ → ℝ) (q : ℝ) (hq : 0 < q) (n : ℕ) (b B s0 M : ℝ)
    (i : ModeIdx) : ℝ :=
  momentRat b B s0 M (idxOf i) * G (tmFlag i) q (Wpair q hq n) (innerScale s0 (degFam i))
    (R1pair q hq n (innerScale s0 (degFam i))) (degFam i)

theorem s1_le_inner (q : ℝ) (hq : 0 < q) (n : ℕ) (s0 : ℝ) (l : ℕ) (s : ℕ)
    (hs : max (OQ14.BarrierDegreeDecomp.s1pair q hq n s0) (OQ14.BarrierDegreeDecomp.s1pair q hq n 1) ≤ s) :
    OQ14.BarrierDegreeDecomp.s1pair q hq n (innerScale s0 l) ≤ s := by
  unfold innerScale
  split_ifs
  · exact (le_max_left _ _).trans hs
  · exact (le_max_right _ _).trans hs

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
theorem scaled_decomp (q : ℝ) (hq : 0 < q) (hq1 : 1 ≤ q) (n : ℕ) (b B s0 M : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0) (hs0 : 0 < s0)
    (ρ : ℕ → Fin 3 → Space → ℂ) (hρ : ∀ s j, Integrable (ρ s j) volume)
    (hsupp : ∀ s j y, b < ‖y‖ → ρ s j y = 0) (hmass : ∀ s, SourceRadiatedSeries.mass (ρ s) ≤ M)
    (i : ModeIdx) (s : ℕ) (x : Space)
    (hs : max (s1pair q hq n s0) (s1pair q hq n 1) ≤ s) (hx : RadialPhaseLimit.radius s < ‖x‖) :
    Decomp (Kc mK1 q hq n b B s0 M i) (Kc mK2 q hq n b B s0 M i)
      (coeffFam ρ s i • modeElectric (tmFlag i) (dataFam q hq n i s) (polyFam i) x) x ∧
    Decomp (Kc mL1 q hq n b B s0 M i) (Kc mL2 q hq n b B s0 M i)
      (coeffFam ρ s i • modeMagnetic (tmFlag i) (dataFam q hq n i s) (polyFam i) x) x := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp ((RadialPhaseLimit.radius_pos s).trans hx)
  have hl1 : 1 ≤ degFam i := by cases i <;> exact Nat.succ_le_succ (Nat.zero_le _)
  set σ := innerScale s0 (degFam i) with hσdef
  have hσ : 0 < σ := innerScale_pos s0 hs0 _
  have hbar : σ^2 < RiccatiBarrier.ν (degFam i) := innerScale_barrier s0 _ hl1
  have hreg : 0 < HankelRealBasis.regular (degFam i) σ := regular_pos_of_barrier σ hσ _ hbar
  have hs1 := s1_le_inner q hq n s0 (degFam i) s hs
  obtain ⟨hE, hH⟩ := index_decomp q hq hq1 n σ hσ i s x hs1 hx
  have hc : ‖coeffFam ρ s i‖ ≤ momentRat b B s0 M (idxOf i) * HankelRealBasis.regular (degFam i) σ := by
    have h := moment_le_rat b B s0 M hb hB hscale hBs hs0 (ρ s) (hρ s) (hsupp s) (hmass s) (idxOf i)
    rw [degFam_eq i]
    cases i with
    | inl a => exact h.1
    | inr a => exact h.2
  have hM0 : 0 ≤ M := (SourceRadiatedSeries.mass_nonneg (ρ 0)).trans (hmass 0)
  have hrat0 := momentRat_nonneg b B s0 M hb hB hBs hs0 hM0 (idxOf i)
  have hR1pos := R1pair_pos q hq n σ
  have hnn := mode_constants_nonneg (tmFlag i) q (Wpair q hq n) σ (R1pair q hq n σ) hq1 hσ.le hR1pos
    (degFam i)
  have hratio : ‖coeffFam ρ s i / ((HankelRealBasis.regular (degFam i) σ : ℝ) : ℂ)‖ ≤
      momentRat b B s0 M (idxOf i) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hreg]
    exact (div_le_iff₀ hreg).mpr hc
  have hsm (F : Vector) : coeffFam ρ s i • F = (coeffFam ρ s i /
      ((HankelRealBasis.regular (degFam i) σ : ℝ) : ℂ)) •
      (((HankelRealBasis.regular (degFam i) σ : ℝ) : ℂ) • F) := by
    rw [smul_smul, div_mul_cancel₀]
    exact_mod_cast hreg.ne'
  constructor
  · rw [hsm]
    exact decomp_mono hx0 (decomp_smul _ hE) (mul_le_mul_of_nonneg_right hratio hnn.1)
      (mul_le_mul_of_nonneg_right hratio hnn.2.1)
  · rw [hsm]
    exact decomp_mono hx0 (decomp_smul _ hH) (mul_le_mul_of_nonneg_right hratio hnn.2.2.1)
      (mul_le_mul_of_nonneg_right hratio hnn.2.2.2)

theorem succ_mode_injective : Function.Injective
    (fun a : PositiveIndex => (⟨a.1+1, a.2⟩ : OQ14.BarrierDegreeSeriesFlux.Mode)) := by
  rintro ⟨l, m⟩ ⟨l', m'⟩ h
  simp only [Sigma.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hl : l = l' := Nat.succ.inj h1
  subst hl
  have := eq_of_heq h2
  subst this
  rfl

theorem summable_piecewise (s0 : ℝ) (Gh Gl : ℕ → ℝ) (hGh0 : ∀ l, 0 ≤ Gh l)
    (hGh : Summable (fun l : ℕ => ((l : ℝ)+1)^3 * Gh l)) (Ahi : ℝ) (hA : 0 ≤ Ahi)
    (Rlow : PositiveIndex → ℝ) :
    Summable (fun a : PositiveIndex =>
      if s0^2 < RiccatiBarrier.ν (a.1+1) then Ahi * Gh (a.1+1) else Rlow a * Gl (a.1+1)) := by
  have hsig := OQ14.BarrierDegreeSeriesFlux.summable_mode_sigma Gh hGh0 hGh Ahi hA
  have hsum : Summable (fun a : PositiveIndex => Ahi * Gh (a.1+1)) :=
    hsig.comp_injective succ_mode_injective
  have hhi : Summable (fun a : PositiveIndex =>
      if s0^2 < RiccatiBarrier.ν (a.1+1) then Ahi * Gh (a.1+1) else 0) := by
    refine Summable.of_nonneg_of_le (fun a => ?_) (fun a => ?_) hsum
    · split_ifs
      · exact mul_nonneg hA (hGh0 _)
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact mul_nonneg hA (hGh0 _)
  have hlo : Summable (fun a : PositiveIndex =>
      if s0^2 < RiccatiBarrier.ν (a.1+1) then 0 else Rlow a * Gl (a.1+1)) := by
    apply summable_of_finite_support
    refine (finite_low_degrees s0).subset ?_
    intro a ha
    simp only [Function.mem_support, ne_eq] at ha
    by_contra hn
    exact ha (by simp [show ¬ ¬ s0^2 < RiccatiBarrier.ν (a.1+1) from hn])
  convert hhi.add hlo using 1
  funext a
  split_ifs <;> simp

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
theorem summable_Kc (G : Bool → ℝ → ℝ → ℝ → ℝ → ℕ → ℝ) (q : ℝ) (hq : 0 < q) (n : ℕ)
    (b B s0 M : ℝ) (hb : 0 ≤ b) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hGnn : ∀ t σ R1, 0 ≤ σ → 0 < R1 → ∀ l, 0 ≤ G t q (Wpair q hq n) σ R1 l)
    (hGs : ∀ t σ R1, 0 < σ → 0 < R1 → AngularExteriorBounds.base*Real.exp (1/(4*q))*σ < R1 →
      Summable (fun l : ℕ => ((l : ℝ)+1)^3 * G t q (Wpair q hq n) σ R1 l)) :
    Summable (Kc G q hq n b B s0 M) := by
  have hS := DebyeJetBounds.scale_nonnegative 0 b hb
  have hAhi : 0 ≤ M * DebyeJetBounds.scale 0 b * (6/(1-B/s0)^4) * Real.exp (s0^2/8) / s0 := by
    positivity
  have key : ∀ t : Bool, Summable (fun a : PositiveIndex => momentRat b B s0 M a *
      G t q (Wpair q hq n) (innerScale s0 (a.1+1)) (R1pair q hq n (innerScale s0 (a.1+1))) (a.1+1)) := by
    intro t
    have h := summable_piecewise s0 (fun l => G t q (Wpair q hq n) s0 (R1pair q hq n s0) l)
      (fun l => G t q (Wpair q hq n) 1 (R1pair q hq n 1) l)
      (fun l => hGnn t s0 _ hs0.le (R1pair_pos q hq n s0) l)
      (hGs t s0 _ hs0 (R1pair_pos q hq n s0) (R1pair_rate q hq n s0 hs0)) _ hAhi
      (fun a => M * SourceRadiatedSeries.momentConst b B a / HankelRealBasis.regular (a.1+1) 1)
    convert h using 1
    funext a
    by_cases hh : s0^2 < RiccatiBarrier.ν (a.1+1)
    · have hsc : innerScale s0 (a.1+1) = s0 := by unfold innerScale; simp [hh]
      simp only [hsc, if_pos hh, momentRat]
    · have hsc : innerScale s0 (a.1+1) = 1 := by unfold innerScale; simp [hh]
      simp only [hsc, if_neg hh, momentRat]
  exact Summable.sum _ (key true) (key false)


open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
theorem Kc_summable (q : ℝ) (hq : 0 < q) (hq1 : 1 ≤ q) (n : ℕ) (b B s0 M : ℝ) (hb : 0 ≤ b)
    (hs0 : 0 < s0) (hM : 0 ≤ M) :
    Summable (Kc mK1 q hq n b B s0 M) ∧ Summable (Kc mK2 q hq n b B s0 M) ∧
      Summable (Kc mL1 q hq n b B s0 M) ∧ Summable (Kc mL2 q hq n b B s0 M) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact summable_Kc mK1 q hq n b B s0 M hb hs0 hM
      (fun t σ R1 hσ hR1 l => (mode_constants_nonneg t q (Wpair q hq n) σ R1 hq1 hσ hR1 l).1)
      (fun t σ R1 hσ hR1 hρ' => (OQ14.BarrierDegreeSeriesFlux.mode_cubic t q (Wpair q hq n) σ R1 hq1 hσ
        hR1 hρ').1)
  · exact summable_Kc mK2 q hq n b B s0 M hb hs0 hM
      (fun t σ R1 hσ hR1 l => (mode_constants_nonneg t q (Wpair q hq n) σ R1 hq1 hσ hR1 l).2.1)
      (fun t σ R1 hσ hR1 hρ' => (OQ14.BarrierDegreeSeriesFlux.mode_cubic t q (Wpair q hq n) σ R1 hq1 hσ
        hR1 hρ').2.1)
  · exact summable_Kc mL1 q hq n b B s0 M hb hs0 hM
      (fun t σ R1 hσ hR1 l => (mode_constants_nonneg t q (Wpair q hq n) σ R1 hq1 hσ hR1 l).2.2.1)
      (fun t σ R1 hσ hR1 hρ' => (OQ14.BarrierDegreeSeriesFlux.mode_cubic t q (Wpair q hq n) σ R1 hq1 hσ
        hR1 hρ').2.2.1)
  · exact summable_Kc mL2 q hq n b B s0 M hb hs0 hM
      (fun t σ R1 hσ hR1 l => (mode_constants_nonneg t q (Wpair q hq n) σ R1 hq1 hσ hR1 l).2.2.2)
      (fun t σ R1 hσ hR1 hρ' => (OQ14.BarrierDegreeSeriesFlux.mode_cubic t q (Wpair q hq n) σ R1 hq1 hσ
        hR1 hρ').2.2.2)

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- **The absolute plane flux of the radiated mode series tends to zero.**  Let `ρ s` be the shell-indexed
current densities (the inclusion source of the combined solution at shell index `s`), supported in the
ball of radius `b`, with `L¹` masses at most `M`, and let `B ≥ degreeScale 2 b` and an inner scale
`s0 > B`.  The series over the positive degrees and real modes of the TM moments times the layered TM
modes of the paired TM chain and the TE moments times the layered TE modes of the TE chain (the paired
layers with `σ = 1`) has absolute plane flux over `{radius s < ‖u‖}` tending to zero with the shell
index.  The degrees below the barrier of the inner scale (finitely many) are normalized at scale one. -/
theorem radiated_series_flux_tendsto (q : ℝ) (hq : 0 < q) (hq1 : 1 ≤ q) (n : ℕ) (b B s0 M : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0)
    (hs0 : 0 < s0) (ρ : ℕ → Fin 3 → Space → ℂ) (hρ : ∀ s j, Integrable (ρ s j) volume)
    (hsupp : ∀ s j y, b < ‖y‖ → ρ s j y = 0) (hmass : ∀ s, SourceRadiatedSeries.mass (ρ s) ≤ M) :
    Tendsto (fun s : ℕ => ∫ u : Plane in {u : Plane | RadialPhaseLimit.radius s < ‖u‖},
      ‖genFlux (dataFam q hq n) tmFlag polyFam (coeffFam ρ) s u‖) atTop (𝓝 0) := by
  have hM : 0 ≤ M := (SourceRadiatedSeries.mass_nonneg (ρ 0)).trans (hmass 0)
  obtain ⟨h1, h2, h3, h4⟩ := Kc_summable q hq hq1 n b B s0 M hb hs0 hM
  exact gen_series_flux_tendsto (dataFam q hq n) tmFlag polyFam (polyFam_hom q hq n)
    (dataFam_R q hq n) (coeffFam ρ)
    (Kc mK1 q hq n b B s0 M) (Kc mK2 q hq n b B s0 M) (Kc mL1 q hq n b B s0 M) (Kc mL2 q hq n b B s0 M)
    h1 h2 h3 h4 (max (s1pair q hq n s0) (s1pair q hq n 1))
    (fun i s x hs hx => (scaled_decomp q hq hq1 n b B s0 M hb hB hscale hBs hs0 ρ hρ hsupp hmass i s x hs hx).1)
    (fun i s x hs hx => (scaled_decomp q hq hq1 n b B s0 M hb hB hscale hBs hs0 ρ hρ hsupp hmass i s x hs hx).2)

/-! ### Identification of the series with the radiated fields outside the shell -/

theorem genElectric_apply {q : ℝ} {hq : 0 < q} {n : ℕ} (ρ : ℕ → Fin 3 → Space → ℂ) (s : ℕ) (x : Space)
    (i : Fin 3)
    (hsum : Summable (fun k : ModeIdx => coeffFam ρ s k •
      modeElectric (tmFlag k) (dataFam q hq n k s) (polyFam k) x)) :
    genElectric (dataFam q hq n) tmFlag polyFam (coeffFam ρ) s x i =
      ∑' a : PositiveIndex,
        (SourceRadiatedSeries.tmMoment a (ρ s) * SourceUnclippedMaxwell.electric
            (SourceDielectricModes.tmData (OQ14.SourcePairedGeometry.physicalData q hq n s) (a.1+1))
            (representative (a.1+1) a.2) x i +
          SourceRadiatedSeries.teMoment a (ρ s) * SourceGeneralMaxwell.teElectric
            (SourceDielectricModes.teData (OQ14.SourcePairedGeometry.physicalData q hq n s) (a.1+1))
            (representative (a.1+1) a.2) x i) := by
  unfold genElectric
  rw [tsum_apply hsum]
  have h := Pi.summable.mp hsum i
  have h1 : Summable (fun a : PositiveIndex => (coeffFam ρ s (Sum.inl a) •
      modeElectric (tmFlag (Sum.inl a)) (dataFam q hq n (Sum.inl a) s) (polyFam (Sum.inl a)) x) i) :=
    h.comp_injective Sum.inl_injective
  have h2 : Summable (fun a : PositiveIndex => (coeffFam ρ s (Sum.inr a) •
      modeElectric (tmFlag (Sum.inr a)) (dataFam q hq n (Sum.inr a) s) (polyFam (Sum.inr a)) x) i) :=
    h.comp_injective Sum.inr_injective
  rw [Summable.tsum_sum h1 h2, ← Summable.tsum_add h1 h2]
  apply tsum_congr
  intro a
  rfl

theorem genMagnetic_apply {q : ℝ} {hq : 0 < q} {n : ℕ} (ρ : ℕ → Fin 3 → Space → ℂ) (s : ℕ) (x : Space)
    (i : Fin 3)
    (hsum : Summable (fun k : ModeIdx => coeffFam ρ s k •
      modeMagnetic (tmFlag k) (dataFam q hq n k s) (polyFam k) x)) :
    genMagnetic (dataFam q hq n) tmFlag polyFam (coeffFam ρ) s x i =
      ∑' a : PositiveIndex,
        (SourceRadiatedSeries.tmMoment a (ρ s) * SourceUnclippedMaxwell.magnetic
            (SourceDielectricModes.tmData (OQ14.SourcePairedGeometry.physicalData q hq n s) (a.1+1))
            (representative (a.1+1) a.2) x i +
          SourceRadiatedSeries.teMoment a (ρ s) * SourceGeneralMaxwell.teMagnetic
            (SourceDielectricModes.teData (OQ14.SourcePairedGeometry.physicalData q hq n s) (a.1+1))
            (representative (a.1+1) a.2) x i) := by
  unfold genMagnetic
  rw [tsum_apply hsum]
  have h := Pi.summable.mp hsum i
  have h1 : Summable (fun a : PositiveIndex => (coeffFam ρ s (Sum.inl a) •
      modeMagnetic (tmFlag (Sum.inl a)) (dataFam q hq n (Sum.inl a) s) (polyFam (Sum.inl a)) x) i) :=
    h.comp_injective Sum.inl_injective
  have h2 : Summable (fun a : PositiveIndex => (coeffFam ρ s (Sum.inr a) •
      modeMagnetic (tmFlag (Sum.inr a)) (dataFam q hq n (Sum.inr a) s) (polyFam (Sum.inr a)) x) i) :=
    h.comp_injective Sum.inr_injective
  rw [Summable.tsum_sum h1 h2, ← Summable.tsum_add h1 h2]
  apply tsum_congr
  intro a
  rfl

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- **The radiated electric and magnetic fields of the inclusion outside the paired shell are the
all-degree layered mode series.**  For all large shell indices `s`, at every point outside the shell,
the electric field radiated by the inclusion source `v s` (the free field of the inclusion source plus
the field of the shell polarization driven by `Ss T Si (v s)`) is the electric component of the series
`genElectric` of the TM and TE layered modes of the paired data with the moments of the inclusion source
as coefficients, and the same holds for the magnetic fields and `genMagnetic`. -/
theorem paired_radiated_series_outside (q : ℝ) (hq : 1 ≤ q) (n : ℕ)
    (ci : SourceRadiatedSeries.Coefficient) (b B s0 M : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0)
    (hs0 : 0 < s0) (v : ℕ → SourceRadiatedSeries.VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (hmass : ∀ s, SourceRadiatedSeries.mass (fun j => DynamicVolume.source ci (v s) j) ≤ M) :
    ∀ᶠ s : ℕ in atTop, ∀ x : Space, (OQ14.SourcePairedInclusion.data q hq n s).X < ‖x‖ → ∀ i : Fin 3,
      (ExteriorContinuity.electric 1 (fun j => DynamicVolume.source ci (v s) j) x i +
        ExteriorContinuity.electric 1 (DynamicVolume.source (OQ14.SourcePairedInclusion.shell q hq n s)
          (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
            (OQ14.SourcePairedInclusion.data q hq n s).X (StaticCoefficient.sqrtMultiplier
              (OQ14.SourcePairedInclusion.shell q hq n s)
              (ShellInclusionVolume.kernel 1 (OQ14.SourcePairedInclusion.data q hq n s).X
                (StaticCoefficient.sqrtMultiplier ci (v s)))))) x i =
        genElectric (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
          (coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s x i) ∧
      (MagneticResponse.magnetic 1 (fun j => DynamicVolume.source ci (v s) j) x i +
        MagneticResponse.magnetic 1 (DynamicVolume.source (OQ14.SourcePairedInclusion.shell q hq n s)
          (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
            (OQ14.SourcePairedInclusion.data q hq n s).X (StaticCoefficient.sqrtMultiplier
              (OQ14.SourcePairedInclusion.shell q hq n s)
              (ShellInclusionVolume.kernel 1 (OQ14.SourcePairedInclusion.data q hq n s).X
                (StaticCoefficient.sqrtMultiplier ci (v s)))))) x i =
        genMagnetic (dataFam q (zero_lt_one.trans_le hq) n) tmFlag polyFam
          (coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s x i) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hM : 0 ≤ M := (SourceRadiatedSeries.mass_nonneg _).trans (hmass 0)
  set T : ℝ := max 2 (2*(B*AngularExteriorBounds.base)) with hTdef
  have hρ : ∀ s j, Integrable (DynamicVolume.source ci (v s) j) volume := fun s j =>
    DynamicVolume.source_integrable ci (v s) b hci j
  have hsupp : ∀ s j y, b < ‖y‖ → DynamicVolume.source ci (v s) j y = 0 := fun s j y hy =>
    DynamicVolume.source_zero ci (v s) b hci j y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy)
  obtain ⟨h1, h2, h3, h4⟩ := Kc_summable q hq0 hq n b B s0 M hb hs0 hM
  have e1 : ∀ᶠ s : ℕ in atTop, max (s1pair q hq0 n s0) (s1pair q hq0 n 1) ≤ s := eventually_ge_atTop _
  have e2 : ∀ᶠ s : ℕ in atTop, max T b < RadialPhaseLimit.radius s :=
    RadialPhaseLimit.radius_tendsto.eventually_gt_atTop _
  filter_upwards [e1, e2] with s hs hsR
  intro x hx i
  have hTR : T < (OQ14.SourcePairedInclusion.data q hq n s).R := (le_max_left T b).trans_lt hsR
  have hbR : b < (OQ14.SourcePairedInclusion.data q hq n s).R := (le_max_right T b).trans_lt hsR
  have hx0 : x ≠ 0 := SourceRadiatedMagnetic.exterior_ne_zero _ x hx
  have hxR : RadialPhaseLimit.radius s < ‖x‖ :=
    (OQ14.SourcePairedInclusion.radii_ordered q hq n s).trans_lt hx
  have hm : ∀ z : Space, (((OQ14.SourcePairedInclusion.shell q hq n s).value
      (VectorFourier.coordinateMap z) : ℝ) : ℂ) =
      SourceRadialSystem.sigma (OQ14.SourcePairedInclusion.data q hq n s) ‖z‖ - 1 := fun z =>
    SourceMaterialCoefficient.value_complex (OQ14.SourcePairedGeometry.physicalData q hq0 n s) (q^2)
      (by nlinarith) (OQ14.SourcePairedGeometry.physical_material_bounds q hq0 hq n s) z
  have hdisp := OQ14.SourcePairedGeometry.physical_dispersion q hq0 n s
  have hu := OQ14.SourcePairedInclusion.shell_isUnit q hq n s
  have hc : ∀ z : Space, z ∉ closedBall (0 : Space) (OQ14.SourcePairedInclusion.data q hq n s).X →
      (OQ14.SourcePairedInclusion.shell q hq n s).value (VectorFourier.coordinateMap z) = 0 :=
    fun z hz => OQ14.SourcePairedInclusion.shell_support q hq n s z hz
  have hi : ∀ z : Space, ‖z‖ ≤ (OQ14.SourcePairedInclusion.data q hq n s).R →
      (OQ14.SourcePairedInclusion.shell q hq n s).value (VectorFourier.coordinateMap z) = 0 :=
    fun z hz => OQ14.SourcePairedInclusion.shell_inner q hq n s z hz
  have hsumE : Summable (fun k : ModeIdx => coeffFam (fun s j => DynamicVolume.source ci (v s) j) s k •
      modeElectric (tmFlag k) (dataFam q hq0 n k s) (polyFam k) x) :=
    (decomp_tsum_gen _ _ _ h1 h2 x hx0 (fun k => (scaled_decomp q hq0 hq n b B s0 M hb hB hscale hBs hs0
      (fun s j => DynamicVolume.source ci (v s) j) hρ hsupp hmass k s x hs hxR).1)).1
  have hsumH : Summable (fun k : ModeIdx => coeffFam (fun s j => DynamicVolume.source ci (v s) j) s k •
      modeMagnetic (tmFlag k) (dataFam q hq0 n k s) (polyFam k) x) :=
    (decomp_tsum_gen _ _ _ h3 h4 x hx0 (fun k => (scaled_decomp q hq0 hq n b B s0 M hb hB hscale hBs hs0
      (fun s j => DynamicVolume.source ci (v s) j) hρ hsupp hmass k s x hs hxR).2)).1
  constructor
  · rw [genElectric_apply _ s x i hsumE]
    exact (SourceRadiatedSeries.radiated_field_series_outside _ ci _ b B T hb hB hscale (le_max_left _ _)
      (le_max_right _ _) hTR hbR hm hdisp hu hc hi hci (v s) x hx i).tsum_eq.symm
  · rw [genMagnetic_apply _ s x i hsumH]
    exact (SourceRadiatedMagnetic.radiated_magnetic_series_outside _ ci _ b B T hb hB hscale
      (le_max_left _ _) (le_max_right _ _) hTR hbR hm hdisp hu hc hi hci (v s) x hx i).tsum_eq.symm

/-! ### Mass bound from the `L²` norm of the inclusion vector -/

theorem mass_le_norm (ci : SourceRadiatedSeries.Coefficient) (b : ℝ)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (w : SourceRadiatedSeries.VectorL2) :
    SourceRadiatedSeries.mass (fun j => DynamicVolume.source ci w j) ≤
      3 * ((Real.sqrt ci.bound * Real.sqrt (volume.real (closedBall (0 : Space) b))) * ‖w‖) := by
  unfold SourceRadiatedSeries.mass
  have h (j : Fin 3) := SourcePairedReactionField.source_mass' ci
    (SourcePairedPlaneIdentification.ballSupportData ci b hci) w j
  calc ∑ j : Fin 3, ∫ y, ‖DynamicVolume.source ci w j y‖ ≤
        ∑ j : Fin 3, ((Real.sqrt ci.bound * Real.sqrt (volume.real (closedBall (0 : Space) b))) * ‖w‖) :=
        Finset.sum_le_sum fun j _ => h j
    _ = 3 * ((Real.sqrt ci.bound * Real.sqrt (volume.real (closedBall (0 : Space) b))) * ‖w‖) := by
        simp [Finset.sum_const]

/-- **Flux of the radiated series for inclusion vectors bounded in `L²`.** -/
theorem radiated_series_flux_tendsto_of_norm_bound (q : ℝ) (hq : 0 < q) (hq1 : 1 ≤ q) (n : ℕ)
    (ci : SourceRadiatedSeries.Coefficient) (b B s0 N : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0)
    (hs0 : 0 < s0) (v : ℕ → SourceRadiatedSeries.VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (hN : ∀ s, ‖v s‖ ≤ N) :
    Tendsto (fun s : ℕ => ∫ u : Plane in {u : Plane | RadialPhaseLimit.radius s < ‖u‖},
      ‖genFlux (dataFam q hq n) tmFlag polyFam
        (coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s u‖) atTop (𝓝 0) := by
  refine radiated_series_flux_tendsto q hq hq1 n b B s0
    (3 * ((Real.sqrt ci.bound * Real.sqrt (volume.real (closedBall (0 : Space) b))) * N)) hb hB hscale
    hBs hs0 (fun s j => DynamicVolume.source ci (v s) j)
    (fun s j => DynamicVolume.source_integrable ci (v s) b hci j)
    (fun s j y hy => DynamicVolume.source_zero ci (v s) b hci j y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy))
    (fun s => (mass_le_norm ci b hci (v s)).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hN s) (by positivity)) (by norm_num)))

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- **The exterior plane flux of the actual radiated field of the inclusion tends to zero.**  With the
hypotheses of `paired_radiated_series_outside`, the absolute plane flux density of the field radiated by
the inclusion source `v s` (electric field `E_s`, magnetic field `H_s`: the free field of the inclusion
source plus the field of the shell polarization driven by `Ss T Si (v s)`), integrated over the part
`{X_s < ‖u‖}` of the plane outside the shell, tends to zero with the shell index. -/
theorem paired_radiated_exterior_flux_tendsto (q : ℝ) (hq : 1 ≤ q) (n : ℕ)
    (ci : SourceRadiatedSeries.Coefficient) (b B s0 N : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0)
    (hs0 : 0 < s0) (v : ℕ → SourceRadiatedSeries.VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (hN : ∀ s, ‖v s‖ ≤ N) :
    Tendsto (fun s : ℕ => ∫ u : Plane in {u : Plane | (OQ14.SourcePairedInclusion.data q hq n s).X < ‖u‖},
      ‖crossProduct
        (fun i => ExteriorContinuity.electric 1 (fun j => DynamicVolume.source ci (v s) j)
            (MaxwellPlaneTail.planePoint u) i +
          ExteriorContinuity.electric 1 (DynamicVolume.source (OQ14.SourcePairedInclusion.shell q hq n s)
            (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
              (OQ14.SourcePairedInclusion.data q hq n s).X (StaticCoefficient.sqrtMultiplier
                (OQ14.SourcePairedInclusion.shell q hq n s)
                (ShellInclusionVolume.kernel 1 (OQ14.SourcePairedInclusion.data q hq n s).X
                  (StaticCoefficient.sqrtMultiplier ci (v s))))))
            (MaxwellPlaneTail.planePoint u) i)
        (conjugate (fun i => MagneticResponse.magnetic 1 (fun j => DynamicVolume.source ci (v s) j)
            (MaxwellPlaneTail.planePoint u) i +
          MagneticResponse.magnetic 1 (DynamicVolume.source (OQ14.SourcePairedInclusion.shell q hq n s)
            (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
              (OQ14.SourcePairedInclusion.data q hq n s).X (StaticCoefficient.sqrtMultiplier
                (OQ14.SourcePairedInclusion.shell q hq n s)
                (ShellInclusionVolume.kernel 1 (OQ14.SourcePairedInclusion.data q hq n s).X
                  (StaticCoefficient.sqrtMultiplier ci (v s))))))
            (MaxwellPlaneTail.planePoint u) i)) 2‖) atTop (𝓝 0) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  set M : ℝ := 3 * ((Real.sqrt ci.bound * Real.sqrt (volume.real (closedBall (0 : Space) b))) * N) with hMdef
  have hmass : ∀ s, SourceRadiatedSeries.mass (fun j => DynamicVolume.source ci (v s) j) ≤ M := fun s =>
    (mass_le_norm ci b hci (v s)).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hN s) (by positivity)) (by norm_num))
  have hM : 0 ≤ M := (SourceRadiatedSeries.mass_nonneg _).trans (hmass 0)
  have hρ : ∀ s j, Integrable (DynamicVolume.source ci (v s) j) volume := fun s j =>
    DynamicVolume.source_integrable ci (v s) b hci j
  have hsupp : ∀ s j y, b < ‖y‖ → DynamicVolume.source ci (v s) j y = 0 := fun s j y hy =>
    DynamicVolume.source_zero ci (v s) b hci j y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy)
  obtain ⟨h1, h2, h3, h4⟩ := Kc_summable q hq0 hq n b B s0 M hb hs0 hM
  set C : ℝ := 2*(∑' i, Kc mK2 q hq0 n b B s0 M i)*(∑' i, Kc mL1 q hq0 n b B s0 M i) +
    2*(∑' i, Kc mK1 q hq0 n b B s0 M i)*(∑' i, Kc mL2 q hq0 n b B s0 M i) with hCdef
  have hXtop : Tendsto (fun s : ℕ => (OQ14.SourcePairedInclusion.data q hq n s).X) atTop atTop := by
    refine tendsto_atTop_mono (fun s => ?_) RadialPhaseLimit.radius_tendsto
    exact OQ14.SourcePairedInclusion.radii_ordered q hq n s
  have hup : Tendsto (fun s : ℕ => C*diskConstant/(OQ14.SourcePairedInclusion.data q hq n s).X) atTop
      (𝓝 0) := (tendsto_const_nhds (x := C*diskConstant)).div_atTop hXtop
  apply squeeze_zero' (Eventually.of_forall (fun s => integral_nonneg (fun u => norm_nonneg _))) _ hup
  have hid := paired_radiated_series_outside q hq n ci b B s0 M hb hB hscale hBs hs0 v hci hmass
  filter_upwards [hid, eventually_ge_atTop (max (s1pair q hq0 n s0) (s1pair q hq0 n 1))] with s hids hs
  have hR : RadialPhaseLimit.radius s ≤ (OQ14.SourcePairedInclusion.data q hq n s).X :=
    OQ14.SourcePairedInclusion.radii_ordered q hq n s
  have hXpos : 0 < (OQ14.SourcePairedInclusion.data q hq n s).X :=
    (RadialPhaseLimit.radius_pos s).trans_le hR
  obtain ⟨hF, hbd⟩ := gen_series_flux_data (dataFam q hq0 n) tmFlag polyFam (polyFam_hom q hq0 n)
    (dataFam_R q hq0 n) (coeffFam (fun s j => DynamicVolume.source ci (v s) j))
    (Kc mK1 q hq0 n b B s0 M) (Kc mK2 q hq0 n b B s0 M) (Kc mL1 q hq0 n b B s0 M) (Kc mL2 q hq0 n b B s0 M)
    h1 h2 h3 h4 (max (s1pair q hq0 n s0) (s1pair q hq0 n 1)) s hs
    (fun i s x hs hx => (scaled_decomp q hq0 hq n b B s0 M hb hB hscale hBs hs0
      (fun s j => DynamicVolume.source ci (v s) j) hρ hsupp hmass i s x hs hx).1)
    (fun i s x hs hx => (scaled_decomp q hq0 hq n b B s0 M hb hB hscale hBs hs0
      (fun s j => DynamicVolume.source ci (v s) j) hρ hsupp hmass i s x hs hx).2)
  have hsub : {u : Plane | (OQ14.SourcePairedInclusion.data q hq n s).X < ‖u‖} ⊆
      {u : Plane | RadialPhaseLimit.radius s < ‖u‖} := fun u hu => hR.trans_lt hu
  have hmeas : MeasurableSet {u : Plane | (OQ14.SourcePairedInclusion.data q hq n s).X < ‖u‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hFX : AEStronglyMeasurable (genFlux (dataFam q hq0 n) tmFlag polyFam
      (coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s)
      (volume.restrict {u : Plane | (OQ14.SourcePairedInclusion.data q hq n s).X < ‖u‖}) :=
    hF.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hbX : ∀ u : Plane, (OQ14.SourcePairedInclusion.data q hq n s).X < ‖u‖ →
      ‖genFlux (dataFam q hq0 n) tmFlag polyFam
        (coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s u‖ ≤ C/‖u‖^3 := fun u hu =>
    hbd u (hR.trans_lt hu)
  have htail := tail_integral_bound _ C hXpos hFX hbX
  refine le_trans (le_of_eq ?_) htail
  apply setIntegral_congr_fun hmeas
  intro u hu
  have hu2 : (OQ14.SourcePairedInclusion.data q hq n s).X < ‖MaxwellPlaneTail.planePoint u‖ := by
    rw [MaxwellPlaneTail.planePoint_norm]; exact hu
  have hE : (fun i => ExteriorContinuity.electric 1 (fun j => DynamicVolume.source ci (v s) j)
        (MaxwellPlaneTail.planePoint u) i +
      ExteriorContinuity.electric 1 (DynamicVolume.source (OQ14.SourcePairedInclusion.shell q hq n s)
        (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
          (OQ14.SourcePairedInclusion.data q hq n s).X (StaticCoefficient.sqrtMultiplier
            (OQ14.SourcePairedInclusion.shell q hq n s)
            (ShellInclusionVolume.kernel 1 (OQ14.SourcePairedInclusion.data q hq n s).X
              (StaticCoefficient.sqrtMultiplier ci (v s))))))
        (MaxwellPlaneTail.planePoint u) i) =
      genElectric (dataFam q hq0 n) tmFlag polyFam
        (coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s (MaxwellPlaneTail.planePoint u) :=
    funext fun i => (hids _ hu2 i).1
  have hH : (fun i => MagneticResponse.magnetic 1 (fun j => DynamicVolume.source ci (v s) j)
        (MaxwellPlaneTail.planePoint u) i +
      MagneticResponse.magnetic 1 (DynamicVolume.source (OQ14.SourcePairedInclusion.shell q hq n s)
        (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
          (OQ14.SourcePairedInclusion.data q hq n s).X (StaticCoefficient.sqrtMultiplier
            (OQ14.SourcePairedInclusion.shell q hq n s)
            (ShellInclusionVolume.kernel 1 (OQ14.SourcePairedInclusion.data q hq n s).X
              (StaticCoefficient.sqrtMultiplier ci (v s))))))
        (MaxwellPlaneTail.planePoint u) i) =
      genMagnetic (dataFam q hq0 n) tmFlag polyFam
        (coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s (MaxwellPlaneTail.planePoint u) :=
    funext fun i => (hids _ hu2 i).2
  simp only []
  rw [hE, hH]
  rfl

end OQ14.SourceRadiatedFlux

#print axioms OQ14.SourceRadiatedFlux.decomp_tsum_gen
#print axioms OQ14.SourceRadiatedFlux.gen_series_flux_data
#print axioms OQ14.SourceRadiatedFlux.gen_series_flux_tendsto
#print axioms OQ14.SourceRadiatedFlux.paired_mode_decomp_te
#print axioms OQ14.SourceRadiatedFlux.dataFam_R
#print axioms OQ14.SourceRadiatedFlux.polyFam_hom
#print axioms OQ14.SourceRadiatedFlux.regular_pos_of_barrier
#print axioms OQ14.SourceRadiatedFlux.one_lt_barrier
#print axioms OQ14.SourceRadiatedFlux.innerScale_pos
#print axioms OQ14.SourceRadiatedFlux.innerScale_barrier
#print axioms OQ14.SourceRadiatedFlux.finite_low_degrees
#print axioms OQ14.SourceRadiatedFlux.index_decomp
#print axioms OQ14.SourceRadiatedFlux.degFam_eq
#print axioms OQ14.SourceRadiatedFlux.momentRat_nonneg
#print axioms OQ14.SourceRadiatedFlux.moment_le_rat
#print axioms OQ14.SourceRadiatedFlux.s1_le_inner
#print axioms OQ14.SourceRadiatedFlux.scaled_decomp
#print axioms OQ14.SourceRadiatedFlux.succ_mode_injective
#print axioms OQ14.SourceRadiatedFlux.summable_piecewise
#print axioms OQ14.SourceRadiatedFlux.summable_Kc
#print axioms OQ14.SourceRadiatedFlux.Kc_summable
#print axioms OQ14.SourceRadiatedFlux.radiated_series_flux_tendsto
#print axioms OQ14.SourceRadiatedFlux.genElectric_apply
#print axioms OQ14.SourceRadiatedFlux.genMagnetic_apply
#print axioms OQ14.SourceRadiatedFlux.paired_radiated_series_outside
#print axioms OQ14.SourceRadiatedFlux.mass_le_norm
#print axioms OQ14.SourceRadiatedFlux.radiated_series_flux_tendsto_of_norm_bound
#print axioms OQ14.SourceRadiatedFlux.paired_radiated_exterior_flux_tendsto
