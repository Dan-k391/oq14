import SourceAnnulusPlaneFlux

/-! Uniform-in-shell-index exterior bounds for the paired-shell source modes: beyond the outer stack radius
the states are controlled by the amplitude (bounded through the uniform gamma bounds) and the vacuum Hankel
energy; the exterior plane flux of a fixed finite band therefore tends to zero, and combined with the
annulus estimate so does the absolute plane flux outside the core. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceRemotePlaneUniform
open MeasureTheory Set Metric Filter Complex OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.RadialStack OQ14.RadialPropagation OQ14.RadialLayer OQ14.RadialSource OQ14.HankelRealBasis
  OQ14.SourceRemotePlaneBand OQ14.PlaneInverseCube OQ14.SourceAnnulusPlaneFlux
  OQ14.SourceAnnulusStateBounds
open scoped Topology ComplexConjugate

theorem point_decomp (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) (B M0 M1 M2 : ℝ) (x : Space) (hx0 : x≠0)
    (hB1 : ‖(raw d ‖x‖).1‖ ≤ B) (hB2 : ‖(raw d ‖x‖).2‖ ≤ B) (hσn : ‖inverseSigma d ‖x‖‖ ≤ 1)
    (h0 : ∀ x : Space, x≠0 → ‖(((‖x‖ : ℂ)^(d.l+1))⁻¹) • HarmonicRadiationFactors.poloidal P x‖ ≤ M0)
    (h1 : ∀ x : Space, x≠0 → ‖(((‖x‖ : ℂ)^(d.l+1))⁻¹) • HarmonicRadiationFactors.radial P x‖ ≤ M1)
    (h2 : ∀ x : Space, x≠0 → ‖(((‖x‖ : ℂ)^d.l)⁻¹) • DebyeRadialTrace.angularToroidal P x‖ ≤ M2)
    :
    Decomp (B*M0) (B*((d.l : ℝ)*(d.l+1))*M1) (SourceUnclippedMaxwell.electric d P x) x ∧
      Decomp (B*M2) 0 (SourceUnclippedMaxwell.magnetic d P x) x := by
  have hrpos : 0<‖x‖ := norm_pos_iff.mpr hx0
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB1
  have hrn : ‖(‖x‖ : ℂ)‖=‖x‖ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hrpos]
  have hL0 : 0 ≤ (d.l : ℝ)*(d.l+1) := by positivity
  have hL : ‖((d.l : ℂ)*(d.l+1))‖=(d.l : ℝ)*(d.l+1) := by
    rw [show ((d.l : ℂ)*(d.l+1))=(((d.l : ℝ)*(d.l+1) : ℝ) : ℂ) by push_cast; ring,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hL0]
  have ca : (raw d ‖x‖).2/(‖x‖ : ℂ)^(d.l+2)=(raw d ‖x‖).2/(‖x‖ : ℂ)*(((‖x‖ : ℂ)^(d.l+1))⁻¹) := by
    field_simp
    first | done | (left; ring)
  have cb : inverseSigma d ‖x‖*((d.l : ℂ)*(d.l+1)*(raw d ‖x‖).1/(‖x‖ : ℂ)^(d.l+3))=
      (inverseSigma d ‖x‖*((d.l : ℂ)*(d.l+1))*(raw d ‖x‖).1/(‖x‖ : ℂ)^2)*(((‖x‖ : ℂ)^(d.l+1))⁻¹) := by
    field_simp
    ring
  constructor
  · refine ⟨((raw d ‖x‖).2/(‖x‖ : ℂ)) • ((((‖x‖ : ℂ)^(d.l+1))⁻¹) • HarmonicRadiationFactors.poloidal P x),
      ((inverseSigma d ‖x‖*((d.l : ℂ)*(d.l+1))*(raw d ‖x‖).1/(‖x‖ : ℂ)^2) •
        ((((‖x‖ : ℂ)^(d.l+1))⁻¹) • HarmonicRadiationFactors.radial P x)),?_,?_,?_,?_,?_⟩
    · rw [electric_pol_rad d P hp x hx0,ca,cb]
      simp only [smul_smul]
    · unfold dotPos
      simp only [Pi.smul_apply,smul_eq_mul]
      have := pol_dot P x
      unfold dotPos at this
      linear_combination ((raw d ‖x‖).2/(‖x‖ : ℂ))*(((‖x‖ : ℂ)^(d.l+1))⁻¹)*this
    · refine ⟨(inverseSigma d ‖x‖*((d.l : ℂ)*(d.l+1))*(raw d ‖x‖).1/(‖x‖ : ℂ)^2)*
        ((((‖x‖ : ℂ)^(d.l+1))⁻¹)*complexEvaluate P x),?_⟩
      rw [radial_eq_smul]
      simp only [smul_smul,mul_assoc]
    · rw [norm_smul,norm_div,hrn]
      have hb := h0 x hx0
      calc _ ≤ B/‖x‖*M0 := mul_le_mul (div_le_div_of_nonneg_right hB2 hrpos.le) hb (norm_nonneg _)
            (div_nonneg hB0 hrpos.le)
        _ = _ := by ring
    · rw [norm_smul,norm_div,norm_mul,norm_mul,norm_pow,hrn,hL]
      have hb := h1 x hx0
      have hnum : ‖inverseSigma d ‖x‖‖*((d.l : ℝ)*(d.l+1))*‖(raw d ‖x‖).1‖ ≤ 1*((d.l : ℝ)*(d.l+1))*B :=
        mul_le_mul (mul_le_mul_of_nonneg_right hσn hL0) hB1 (norm_nonneg _) (by positivity)
      calc _ ≤ 1*((d.l : ℝ)*(d.l+1))*B/‖x‖^2*M1 :=
            mul_le_mul (div_le_div_of_nonneg_right hnum (by positivity)) hb (norm_nonneg _)
              (div_nonneg (by positivity) (by positivity))
        _ = _ := by ring
  · refine ⟨((-I*(raw d ‖x‖).1/(‖x‖ : ℂ)) • ((((‖x‖ : ℂ)^d.l)⁻¹) • DebyeRadialTrace.angularToroidal P x)),0,
      ?_,?_,⟨0,by simp⟩,?_,by simp⟩
    · rw [magnetic_tor d P x hx0,add_zero]
    · unfold dotPos
      simp only [Pi.smul_apply,smul_eq_mul]
      have := tor_dot P x
      unfold dotPos at this
      linear_combination ((-I*(raw d ‖x‖).1/(‖x‖ : ℂ)))*(((‖x‖ : ℂ)^d.l)⁻¹)*this
    · rw [norm_smul,norm_div,norm_mul,norm_neg,Complex.norm_I,hrn]
      have hb := h2 x hx0
      calc _ ≤ B/‖x‖*M2 := by
            rw [one_mul]
            exact mul_le_mul (div_le_div_of_nonneg_right hB1 hrpos.le) hb (norm_nonneg _)
              (div_nonneg hB0 hrpos.le)
        _ = _ := by ring

theorem inverseSigma_ext (d : Data) (r : ℝ) (hr : d.X<r) : inverseSigma d r=1 := by
  have hR : d.R<r := lt_of_le_of_lt (chain_ordered d.chain) hr
  simp only [SourceRadialSystem.inverseSigma,SourceRadialSystem.extend,if_neg (not_le.mpr hR),
    if_neg (not_le.mpr hr)]

theorem raw_energy_ext_le (d : Data) (x : ℝ) (hXx : d.X<x) :
    RadialPropagation.energy (raw d x).1 (raw d x).2 ≤
      ‖gamma d.l d.gs d.R d.X d.hR‖*frobeniusSq d.l x := by
  have hX : 0<d.X := d.hR.trans_le (chain_ordered d.chain)
  have hRx : d.R<x := lt_of_le_of_lt (chain_ordered d.chain) hXx
  have hraw : raw d x=((coefficients d.l d.gs d.R d.X d.hR).2)⁻¹ • outgoing d.l x := by
    simp only [raw,RadialGluing.sourceState,if_neg (not_le.mpr hRx),RadialGluing.outerMatched,if_neg (not_le.mpr hXx)]
  have hβ : (coefficients d.l d.gs d.R d.X d.hR).2≠0 := coefficients_second_ne_zero d.l d.gs d.R d.X d.hR hX
  have hn : Complex.normSq ((coefficients d.l d.gs d.R d.X d.hR).2⁻¹) ≤ ‖gamma d.l d.gs d.R d.X d.hR‖ := by
    have him := gamma_im d.l d.gs d.R d.X d.hR hX
    have hpos : 0<Complex.normSq (coefficients d.l d.gs d.R d.X d.hR).2 := Complex.normSq_pos.mpr hβ
    have habs := Complex.abs_im_le_norm (gamma d.l d.gs d.R d.X d.hR)
    rw [him,abs_div,abs_neg,abs_one,abs_of_pos hpos] at habs
    rw [map_inv₀]
    simpa only [one_div] using habs
  have hF : RadialPropagation.energy (outgoing d.l x).1 (outgoing d.l x).2=frobeniusSq d.l x :=
    (frobeniusSq_eq d.l x).symm
  rw [hraw]
  have hE : RadialPropagation.energy ((coefficients d.l d.gs d.R d.X d.hR).2⁻¹ • outgoing d.l x).1
      ((coefficients d.l d.gs d.R d.X d.hR).2⁻¹ • outgoing d.l x).2=
      Complex.normSq ((coefficients d.l d.gs d.R d.X d.hR).2⁻¹)*
        RadialPropagation.energy (outgoing d.l x).1 (outgoing d.l x).2 := by
    simp only [RadialPropagation.energy,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,map_mul]
    ring
  rw [hE,hF]
  have hfr : 0 ≤ frobeniusSq d.l x := by
    rw [frobeniusSq_eq]; exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact mul_le_mul_of_nonneg_right hn hfr

theorem physical_raw_energy_ext_uniform (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n l : ℕ) :
    ∃ s1 : ℕ, ∃ E0 : ℝ, 0 ≤ E0 ∧ ∀ s : ℕ, s1 ≤ s → ∀ x : ℝ,
      (SourcePairedGeometry.physicalData q hq n s).X<x →
      RadialPropagation.energy (raw { SourcePairedGeometry.physicalData q hq n s with l := l } x).1
        (raw { SourcePairedGeometry.physicalData q hq n s with l := l } x).2 ≤ E0 := by
  let W := RadialFiniteLimit.width (RadialPairedFamily.tm q hq n)
  let C1 : ℝ := 4/(1-(1/2 : ℝ)^2)
  let K : ℝ := 2*q^2+(1/2 : ℝ)^2
  obtain ⟨s1,hs1⟩ := eventually_atTop.mp
    (RadialPhaseLimit.radius_tendsto.eventually (eventually_ge_atTop (4*OQ14.HankelEnergy.angular l+1)))
  refine ⟨s1,C1^2*Real.exp (K*W)*C1,by positivity,?_⟩
  intro s hs x hXx
  have hA : 0 ≤ OQ14.HankelEnergy.angular l := by unfold OQ14.HankelEnergy.angular; positivity
  have hR4 := hs1 s hs
  have hRpos : 1 ≤ RadialPhaseLimit.radius s := by linarith
  have hν : OQ14.HankelEnergy.angular l ≤ (1/2 : ℝ)^2*(RadialPhaseLimit.radius s)^2 := by
    nlinarith
  have hc : (1/2 : ℝ)^2<1 := by norm_num
  have hpar : ∀ g ∈ (SourcePairedGeometry.physicalData q hq n s).gs,
      1 ≤ g.σ ∧ g.σ ≤ q^2 ∧ g.q^2 ≤ q^2 := fun g hg => by
    have h := SourcePairedGeometry.physical_parameters q hq hq1 n s g hg
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  set d : Data := { SourcePairedGeometry.physicalData q hq n s with l := l } with hd
  have hXR : d.X-d.R=W := by
    show RadialPhaseLimit.radius s+W-RadialPhaseLimit.radius s=W
    ring
  have hRx : d.R<x := lt_of_le_of_lt (chain_ordered d.chain) hXx
  have hγ := gamma_low_range d.l d.chain (q^2) (1/2) d.hR hc hν hpar
  have hF := low_range_frobeniusSq d.l (1/2) d.R x hc d.hR hRx.le hν
  rw [hXR] at hγ
  have hraw := raw_energy_ext_le d x hXx
  have h1 : ‖gamma d.l d.gs d.R d.X d.hR‖ ≤ C1^2*Real.exp (K*W) := hγ
  have h3 : frobeniusSq d.l x ≤ C1 := hF
  have hfr : 0 ≤ frobeniusSq d.l x := by
    rw [frobeniusSq_eq]; exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact hraw.trans (mul_le_mul h1 h3 hfr (by positivity))

theorem paired_exterior_decomp (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n l : ℕ) (P : Poly)
    (hp : P.IsHomogeneous l) :
    ∃ s1 : ℕ, ∃ K1 K2 L1 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ L1 ∧ ∀ s : ℕ, s1 ≤ s → ∀ x : Space,
      (SourcePairedGeometry.physicalData q hq n s).X<‖x‖ →
      Decomp K1 K2 (SourceUnclippedMaxwell.electric { SourcePairedGeometry.physicalData q hq n s with l := l } P x) x ∧
      Decomp L1 0 (SourceUnclippedMaxwell.magnetic { SourcePairedGeometry.physicalData q hq n s with l := l } P x) x := by
  obtain ⟨s1,E0,hE0,hE⟩ := physical_raw_energy_ext_uniform q hq hq1 n l
  obtain ⟨M0,hM0,h0⟩ := HarmonicRadiationFactors.poloidal_bound P l hp
  obtain ⟨M1,hM1,h1⟩ := HarmonicRadiationFactors.radial_bound P l hp
  obtain ⟨M2,hM2,h2⟩ := HarmonicRadiationGeometry.normalized_toroidal_bound P l hp
  have hBn : ∀ u p : ℂ, RadialPropagation.energy u p ≤ E0 → ‖u‖ ≤ Real.sqrt E0 ∧ ‖p‖ ≤ Real.sqrt E0 := by
    intro u p h
    have hu : ‖u‖^2 ≤ E0 := by
      simp only [RadialPropagation.energy,Complex.normSq_eq_norm_sq] at h
      nlinarith [sq_nonneg ‖p‖]
    have hp' : ‖p‖^2 ≤ E0 := by
      simp only [RadialPropagation.energy,Complex.normSq_eq_norm_sq] at h
      nlinarith [sq_nonneg ‖u‖]
    exact ⟨by simpa using Real.abs_le_sqrt hu,by simpa using Real.abs_le_sqrt hp'⟩
  refine ⟨s1,Real.sqrt E0*M0,Real.sqrt E0*((l : ℝ)*(l+1))*M1,Real.sqrt E0*M2,by positivity,by positivity,
    by positivity,?_⟩
  intro s hs x hXx
  have hx0 : x≠0 := by
    apply norm_pos_iff.mp
    exact (SourcePairedGeometry.physicalData q hq n s).hR.trans
      (lt_of_le_of_lt (chain_ordered (SourcePairedGeometry.physicalData q hq n s).chain) hXx)
  have hbn := hBn _ _ (hE s hs ‖x‖ hXx)
  have hσ1 := inverseSigma_ext { SourcePairedGeometry.physicalData q hq n s with l := l } ‖x‖ hXx
  exact point_decomp { SourcePairedGeometry.physicalData q hq n s with l := l } P hp (Real.sqrt E0) M0 M1 M2 x hx0
    hbn.1 hbn.2 (by rw [hσ1]; simp) h0 h1 h2

theorem paired_mode_exterior_decomp (tm : Bool) (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n l : ℕ) (P : Poly)
    (hp : P.IsHomogeneous l) :
    ∃ s1 : ℕ, ∃ K1 K2 L1 L2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ L1 ∧ 0 ≤ L2 ∧ ∀ s : ℕ, s1 ≤ s → ∀ x : Space,
      (SourcePairedGeometry.physicalData q hq n s).X<‖x‖ →
      Decomp K1 K2 (modeElectric tm { SourcePairedGeometry.physicalData q hq n s with l := l } P x) x ∧
      Decomp L1 L2 (modeMagnetic tm { SourcePairedGeometry.physicalData q hq n s with l := l } P x) x := by
  obtain ⟨s1,K1,K2,L1,hK1,hK2,hL1,h⟩ := paired_exterior_decomp q hq hq1 n l P hp
  cases tm
  · refine ⟨s1,L1,0,‖(-1 : ℂ)‖*K1,‖(-1 : ℂ)‖*K2,hL1,le_rfl,by positivity,by positivity,?_⟩
    intro s hs x hXx
    obtain ⟨hE,hH⟩ := h s hs x hXx
    have : SourceGeneralMaxwell.teMagnetic { SourcePairedGeometry.physicalData q hq n s with l := l } P x=
        (-1 : ℂ) • SourceUnclippedMaxwell.electric { SourcePairedGeometry.physicalData q hq n s with l := l } P x := by
      funext i
      simp [SourceGeneralMaxwell.teMagnetic]
    simp only [modeElectric,modeMagnetic,Bool.false_eq_true,if_false,SourceGeneralMaxwell.teElectric,this]
    exact ⟨hH,decomp_smul (-1) hE⟩
  · refine ⟨s1,K1,K2,L1,0,hK1,hK2,hL1,le_rfl,?_⟩
    intro s hs x hXx
    simpa only [modeElectric,modeMagnetic,if_true] using h s hs x hXx

theorem band_exterior_flux_bound_uniform {ι κ : Type*} [Fintype ι] [Fintype κ] (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n : ℕ)
    (tmE : ι → Bool) (lE : ι → ℕ) (PE : ι → Poly) (hE : ∀ i, (PE i).IsHomogeneous (lE i)) (cE : ι → ℂ)
    (tmH : κ → Bool) (lH : κ → ℕ) (PH : κ → Poly) (hH : ∀ j, (PH j).IsHomogeneous (lH j)) (cH : κ → ℂ) :
    ∃ s1 : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℕ, s1 ≤ s → ∀ x : Space, x 2=0 →
      (SourcePairedGeometry.physicalData q hq n s).X<‖x‖ →
      ‖crossProduct
        (∑ i, cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i) x)
        (conjugate (∑ j, cH j • modeMagnetic (tmH j)
          { SourcePairedGeometry.physicalData q hq n s with l := lH j } (PH j) x)) 2‖ ≤ C/‖x‖^3 := by
  choose s0 K1 K2 L1 L2 hK1 hK2 hL1 hL2 hdec using
    fun i => paired_mode_exterior_decomp (tmE i) q hq hq1 n (lE i) (PE i) (hE i)
  choose t0 M1 M2 N1 N2 hM1 hM2 hN1 hN2 hdec2 using
    fun j => paired_mode_exterior_decomp (tmH j) q hq hq1 n (lH j) (PH j) (hH j)
  obtain ⟨S1,hS1⟩ := (Set.finite_range s0).bddAbove
  obtain ⟨S2,hS2⟩ := (Set.finite_range t0).bddAbove
  have hS1' : ∀ i, s0 i ≤ S1 := fun i => hS1 (Set.mem_range_self i)
  have hS2' : ∀ j, t0 j ≤ S2 := fun j => hS2 (Set.mem_range_self j)
  refine ⟨max S1 S2,2*(∑ i, ‖cE i‖*K2 i)*(∑ j, ‖cH j‖*N1 j)+2*(∑ i, ‖cE i‖*K1 i)*(∑ j, ‖cH j‖*N2 j),?_,?_⟩
  · have h1 : 0 ≤ ∑ i, ‖cE i‖*K2 i := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hK2 i))
    have h2 : 0 ≤ ∑ j, ‖cH j‖*N1 j := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hN1 j))
    have h3 : 0 ≤ ∑ i, ‖cE i‖*K1 i := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hK1 i))
    have h4 : 0 ≤ ∑ j, ‖cH j‖*N2 j := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hN2 j))
    positivity
  · intro s hs x hx2 hXx
    have hrpos : 0<‖x‖ := (SourcePairedGeometry.physicalData q hq n s).hR.trans
      (lt_of_le_of_lt (chain_ordered (SourcePairedGeometry.physicalData q hq n s).chain) hXx)
    have hDE : Decomp (∑ i, ‖cE i‖*K1 i) (∑ i, ‖cE i‖*K2 i)
        (∑ i, cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i) x) x := by
      apply decomp_sum Finset.univ
        (fun i => cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i) x)
        (fun i => ‖cE i‖*K1 i) (fun i => ‖cE i‖*K2 i) x
      intro i _
      apply decomp_smul
      exact (hdec i s ((hS1' i).trans ((le_max_left _ _).trans hs)) x hXx).1
    have hDH : Decomp (∑ j, ‖cH j‖*N1 j) (∑ j, ‖cH j‖*N2 j)
        (∑ j, cH j • modeMagnetic (tmH j) { SourcePairedGeometry.physicalData q hq n s with l := lH j } (PH j) x) x := by
      apply decomp_sum Finset.univ
        (fun j => cH j • modeMagnetic (tmH j) { SourcePairedGeometry.physicalData q hq n s with l := lH j } (PH j) x)
        (fun j => ‖cH j‖*N1 j) (fun j => ‖cH j‖*N2 j) x
      intro j _
      apply decomp_smul
      exact (hdec2 j s ((hS2' j).trans ((le_max_right _ _).trans hs)) x hXx).2
    exact flux_bound_of_decomp x hx2 hrpos _ _ _ _ _ _ hDE hDH

/-- The plane flux density of the band: electric sum crossed with the conjugate magnetic sum, third component,
at the plane point `u`, for shell index `s`. -/
def bandFlux {ι κ : Type*} [Fintype ι] [Fintype κ] (q : ℝ) (hq : 0<q) (n : ℕ)
    (tmE : ι → Bool) (lE : ι → ℕ) (PE : ι → Poly) (cE : ι → ℂ)
    (tmH : κ → Bool) (lH : κ → ℕ) (PH : κ → Poly) (cH : κ → ℂ) (s : ℕ) (u : Plane) : ℂ :=
  crossProduct
    (∑ i, cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i)
      (MaxwellPlaneTail.planePoint u))
    (conjugate (∑ j, cH j • modeMagnetic (tmH j) { SourcePairedGeometry.physicalData q hq n s with l := lH j }
      (PH j) (MaxwellPlaneTail.planePoint u))) 2

theorem bandFlux_continuousOn_ext {ι κ : Type*} [Fintype ι] [Fintype κ] (q : ℝ) (hq : 0<q) (n : ℕ)
    (tmE : ι → Bool) (lE : ι → ℕ) (PE : ι → Poly) (hE : ∀ i, (PE i).IsHomogeneous (lE i)) (cE : ι → ℂ)
    (tmH : κ → Bool) (lH : κ → ℕ) (PH : κ → Poly) (hH : ∀ j, (PH j).IsHomogeneous (lH j)) (cH : κ → ℂ)
    (s : ℕ) :
    ContinuousOn (bandFlux q hq n tmE lE PE cE tmH lH PH cH s)
      {u : Plane | (SourcePairedGeometry.physicalData q hq n s).X<‖u‖} := by
  have hmaps : MapsTo MaxwellPlaneTail.planePoint
      {u : Plane | (SourcePairedGeometry.physicalData q hq n s).X<‖u‖}
      {x : Space | (SourcePairedGeometry.physicalData q hq n s).X<‖x‖} := by
    intro u hu
    change (SourcePairedGeometry.physicalData q hq n s).X<‖MaxwellPlaneTail.planePoint u‖
    rw [MaxwellPlaneTail.planePoint_norm]
    exact hu
  have hEc : ContinuousOn (fun x : Space => ∑ i, cE i • modeElectric (tmE i)
      { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i) x)
      {x : Space | (SourcePairedGeometry.physicalData q hq n s).X<‖x‖} := by
    apply continuousOn_finset_sum
    intro i _
    apply ContinuousOn.const_smul
    exact SourceRemotePlaneBandTail.modeElectric_continuousOn (tmE i)
      { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i) (hE i)
  have hHc : ContinuousOn (fun x : Space => ∑ j, cH j • modeMagnetic (tmH j)
      { SourcePairedGeometry.physicalData q hq n s with l := lH j } (PH j) x)
      {x : Space | (SourcePairedGeometry.physicalData q hq n s).X<‖x‖} := by
    apply continuousOn_finset_sum
    intro j _
    apply ContinuousOn.const_smul
    exact SourceRemotePlaneBandTail.modeMagnetic_continuousOn (tmH j)
      { SourcePairedGeometry.physicalData q hq n s with l := lH j } (PH j) (hH j)
  have hE' := hEc.comp MaxwellPlaneTail.planePoint_continuous.continuousOn hmaps
  have hH' := hHc.comp MaxwellPlaneTail.planePoint_continuous.continuousOn hmaps
  have hEi (i : Fin 3) := continuousOn_pi.mp hE' i
  have hHi (i : Fin 3) := Complex.continuous_conj.comp_continuousOn (continuousOn_pi.mp hH' i)
  unfold bandFlux
  simp only [SourceRemotePlaneFlux.cross_two,conjugate]
  exact ((hEi 0).mul (hHi 1)).sub ((hEi 1).mul (hHi 0))

theorem bandFlux_aesm_section {ι κ : Type*} [Fintype ι] [Fintype κ] (q : ℝ) (hq : 0<q) (n : ℕ)
    (tmE : ι → Bool) (lE : ι → ℕ) (PE : ι → Poly) (hE : ∀ i, (PE i).IsHomogeneous (lE i)) (cE : ι → ℂ)
    (tmH : κ → Bool) (lH : κ → ℕ) (PH : κ → Poly) (hH : ∀ j, (PH j).IsHomogeneous (lH j)) (cH : κ → ℂ)
    (s : ℕ) :
    AEStronglyMeasurable (bandFlux q hq n tmE lE PE cE tmH lH PH cH s)
      (volume.restrict (annSection (SourcePairedGeometry.physicalData q hq n s).R
        (SourcePairedGeometry.physicalData q hq n s).X)) := by
  have hEm : AEStronglyMeasurable (fun u : Plane =>
      ∑ i, cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i)
        (MaxwellPlaneTail.planePoint u)) (volume.restrict (annSection (SourcePairedGeometry.physicalData q hq n s).R
        (SourcePairedGeometry.physicalData q hq n s).X)) := by
    have : ∀ i, AEStronglyMeasurable (fun u : Plane => cE i • modeElectric (tmE i)
        { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i) (MaxwellPlaneTail.planePoint u))
        (volume.restrict (annSection (SourcePairedGeometry.physicalData q hq n s).R
        (SourcePairedGeometry.physicalData q hq n s).X)) :=
      fun i => (modeElectric_aesm (tmE i) _ (PE i) (hE i)).const_smul (cE i)
    exact Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => this i)
  have hHm : AEStronglyMeasurable (fun u : Plane =>
      ∑ j, cH j • modeMagnetic (tmH j) { SourcePairedGeometry.physicalData q hq n s with l := lH j } (PH j)
        (MaxwellPlaneTail.planePoint u)) (volume.restrict (annSection (SourcePairedGeometry.physicalData q hq n s).R
        (SourcePairedGeometry.physicalData q hq n s).X)) := by
    have : ∀ j, AEStronglyMeasurable (fun u : Plane => cH j • modeMagnetic (tmH j)
        { SourcePairedGeometry.physicalData q hq n s with l := lH j } (PH j) (MaxwellPlaneTail.planePoint u))
        (volume.restrict (annSection (SourcePairedGeometry.physicalData q hq n s).R
        (SourcePairedGeometry.physicalData q hq n s).X)) :=
      fun j => (modeMagnetic_aesm (tmH j) _ (PH j) (hH j)).const_smul (cH j)
    exact Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => this j)
  unfold bandFlux
  simp only [SourceRemotePlaneFlux.cross_two,conjugate]
  have hEi (i : Fin 3) := (continuous_apply i).comp_aestronglyMeasurable hEm
  have hHi (i : Fin 3) := Complex.continuous_conj.comp_aestronglyMeasurable
    ((continuous_apply i).comp_aestronglyMeasurable hHm)
  exact ((hEi 0).mul (hHi 1)).sub ((hEi 1).mul (hHi 0))

theorem band_exterior_tail_tendsto {ι κ : Type*} [Fintype ι] [Fintype κ] (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n : ℕ)
    (tmE : ι → Bool) (lE : ι → ℕ) (PE : ι → Poly) (hE : ∀ i, (PE i).IsHomogeneous (lE i)) (cE : ι → ℂ)
    (tmH : κ → Bool) (lH : κ → ℕ) (PH : κ → Poly) (hH : ∀ j, (PH j).IsHomogeneous (lH j)) (cH : κ → ℂ) :
    Tendsto (fun s : ℕ => ∫ u : Plane in {u : Plane | (SourcePairedGeometry.physicalData q hq n s).X<‖u‖},
      ‖bandFlux q hq n tmE lE PE cE tmH lH PH cH s u‖) atTop (𝓝 0) := by
  obtain ⟨s1,C,hC,hb⟩ := band_exterior_flux_bound_uniform q hq hq1 n tmE lE PE hE cE tmH lH PH hH cH
  let W := RadialFiniteLimit.width (RadialPairedFamily.tm q hq n)
  have hXs : Tendsto (fun s : ℕ => (SourcePairedGeometry.physicalData q hq n s).X) atTop atTop := by
    have h := RadialPhaseLimit.radius_tendsto.atTop_add (tendsto_const_nhds (x := W))
    exact h
  have hup : Tendsto (fun s : ℕ => C*diskConstant/(SourcePairedGeometry.physicalData q hq n s).X) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := C*diskConstant)).div_atTop hXs
  apply squeeze_zero' (Eventually.of_forall (fun s => integral_nonneg (fun u => norm_nonneg _))) _ hup
  filter_upwards [eventually_ge_atTop s1] with s hs
  have hT : 0<(SourcePairedGeometry.physicalData q hq n s).X :=
    (SourcePairedGeometry.physicalData q hq n s).hR.trans_le
      (chain_ordered (SourcePairedGeometry.physicalData q hq n s).chain)
  have hf : AEStronglyMeasurable (bandFlux q hq n tmE lE PE cE tmH lH PH cH s)
      (volume.restrict {u : Plane | (SourcePairedGeometry.physicalData q hq n s).X<‖u‖}) :=
    (bandFlux_continuousOn_ext q hq n tmE lE PE hE cE tmH lH PH hH cH s).aestronglyMeasurable
      (isOpen_lt continuous_const continuous_norm).measurableSet
  have hb' : ∀ u : Plane, (SourcePairedGeometry.physicalData q hq n s).X<‖u‖ →
      ‖bandFlux q hq n tmE lE PE cE tmH lH PH cH s u‖ ≤ C/‖u‖^3 := by
    intro u hu
    have := hb s hs (MaxwellPlaneTail.planePoint u) (SourceRemotePlaneTail.planePoint_two u)
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact hu)
    rwa [MaxwellPlaneTail.planePoint_norm] at this
  exact tail_integral_bound _ C hT hf hb'

theorem band_outside_core_flux_tendsto {ι κ : Type*} [Fintype ι] [Fintype κ] (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n : ℕ)
    (tmE : ι → Bool) (lE : ι → ℕ) (PE : ι → Poly) (hE : ∀ i, (PE i).IsHomogeneous (lE i)) (cE : ι → ℂ)
    (tmH : κ → Bool) (lH : κ → ℕ) (PH : κ → Poly) (hH : ∀ j, (PH j).IsHomogeneous (lH j)) (cH : κ → ℂ) :
    Tendsto (fun s : ℕ => ∫ u : Plane in {u : Plane | (SourcePairedGeometry.physicalData q hq n s).R<‖u‖},
      ‖bandFlux q hq n tmE lE PE cE tmH lH PH cH s u‖) atTop (𝓝 0) := by
  obtain ⟨sa,Ca,hCa,hba⟩ := SourceAnnulusStateBounds.band_annulus_flux_bound q hq hq1 n tmE lE PE hE cE tmH lH PH hH cH
  obtain ⟨se,Ce,hCe,hbe⟩ := band_exterior_flux_bound_uniform q hq hq1 n tmE lE PE hE cE tmH lH PH hH cH
  have hA : Tendsto (fun s : ℕ => ∫ u : Plane in annSection (SourcePairedGeometry.physicalData q hq n s).R
      (SourcePairedGeometry.physicalData q hq n s).X, ‖bandFlux q hq n tmE lE PE cE tmH lH PH cH s u‖) atTop (𝓝 0) :=
    band_annulus_flux_tendsto q hq hq1 n tmE lE PE hE cE tmH lH PH hH cH
  have hE' := band_exterior_tail_tendsto q hq hq1 n tmE lE PE hE cE tmH lH PH hH cH
  have hsum := hA.add hE'
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (max sa se)] with s hs
  let R := (SourcePairedGeometry.physicalData q hq n s).R
  let X := (SourcePairedGeometry.physicalData q hq n s).X
  have hRpos : 0<R := (SourcePairedGeometry.physicalData q hq n s).hR
  have hRX : R ≤ X := chain_ordered (SourcePairedGeometry.physicalData q hq n s).chain
  have hXpos : 0<X := hRpos.trans_le hRX
  have hsa : sa ≤ s := (le_max_left _ _).trans hs
  have hse : se ≤ s := (le_max_right _ _).trans hs
  have hFa := bandFlux_aesm_section q hq n tmE lE PE hE cE tmH lH PH hH cH s
  have hba' : ∀ u : Plane, R<‖u‖ → ‖u‖ ≤ X →
      ‖bandFlux q hq n tmE lE PE cE tmH lH PH cH s u‖ ≤ Ca/‖u‖^3 := by
    intro u hu1 hu2
    have := hba s hsa (MaxwellPlaneTail.planePoint u) (SourceRemotePlaneTail.planePoint_two u)
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact hu1)
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact hu2)
    rwa [MaxwellPlaneTail.planePoint_norm] at this
  have hIa := (annulus_integral_le _ Ca R X hCa hRpos hRX hFa hba').1
  have hf : AEStronglyMeasurable (bandFlux q hq n tmE lE PE cE tmH lH PH cH s)
      (volume.restrict {u : Plane | X<‖u‖}) :=
    (bandFlux_continuousOn_ext q hq n tmE lE PE hE cE tmH lH PH hH cH s).aestronglyMeasurable
      (isOpen_lt continuous_const continuous_norm).measurableSet
  have hbe' : ∀ u : Plane, X<‖u‖ → ‖bandFlux q hq n tmE lE PE cE tmH lH PH cH s u‖ ≤ Ce/‖u‖^3 := by
    intro u hu
    have := hbe s hse (MaxwellPlaneTail.planePoint u) (SourceRemotePlaneTail.planePoint_two u)
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact hu)
    rwa [MaxwellPlaneTail.planePoint_norm] at this
  have hIe : IntegrableOn (fun u => ‖bandFlux q hq n tmE lE PE cE tmH lH PH cH s u‖) {u : Plane | X<‖u‖} :=
    (tail_integrable X Ce hXpos hf hbe').norm
  have hset : {u : Plane | R<‖u‖}=annSection R X ∪ {u : Plane | X<‖u‖} := by
    ext u
    simp only [annSection,mem_setOf_eq,mem_union]
    constructor
    · intro h
      by_cases hX : ‖u‖ ≤ X
      · exact Or.inl ⟨h,hX⟩
      · exact Or.inr (not_le.mp hX)
    · rintro (h | h)
      · exact h.1
      · exact lt_of_le_of_lt hRX h
  have hdisj : Disjoint (annSection R X) {u : Plane | X<‖u‖} := by
    rw [Set.disjoint_left]
    intro u h1 h2
    exact absurd h1.2 (not_le.mpr h2)
  show (∫ u : Plane in annSection R X, ‖bandFlux q hq n tmE lE PE cE tmH lH PH cH s u‖)+
      (∫ u : Plane in {u : Plane | X<‖u‖}, ‖bandFlux q hq n tmE lE PE cE tmH lH PH cH s u‖)=
      ∫ u : Plane in {u : Plane | R<‖u‖}, ‖bandFlux q hq n tmE lE PE cE tmH lH PH cH s u‖
  rw [hset]
  exact (setIntegral_union hdisj (isOpen_lt continuous_const continuous_norm).measurableSet hIa hIe).symm

end OQ14.SourceRemotePlaneUniform
#print axioms OQ14.SourceRemotePlaneUniform.point_decomp
#print axioms OQ14.SourceRemotePlaneUniform.inverseSigma_ext
#print axioms OQ14.SourceRemotePlaneUniform.raw_energy_ext_le
#print axioms OQ14.SourceRemotePlaneUniform.physical_raw_energy_ext_uniform
#print axioms OQ14.SourceRemotePlaneUniform.paired_exterior_decomp
#print axioms OQ14.SourceRemotePlaneUniform.paired_mode_exterior_decomp
#print axioms OQ14.SourceRemotePlaneUniform.band_exterior_flux_bound_uniform
#print axioms OQ14.SourceRemotePlaneUniform.bandFlux_continuousOn_ext
#print axioms OQ14.SourceRemotePlaneUniform.bandFlux_aesm_section
#print axioms OQ14.SourceRemotePlaneUniform.band_exterior_tail_tendsto
#print axioms OQ14.SourceRemotePlaneUniform.band_outside_core_flux_tendsto
