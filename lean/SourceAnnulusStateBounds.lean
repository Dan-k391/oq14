import SourceRemotePlaneBand
import SourcePairedGeometry

/-! Uniform-in-shell-index bounds of the layered radial states of the paired-shell source modes on the
stack annulus, and the resulting inverse-cube flux density bound with constants independent of the shell
index. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceAnnulusStateBounds
open Complex Filter OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem OQ14.RadialStack
  OQ14.RadialPropagation OQ14.RadialLayer OQ14.RadialGluing OQ14.RadialSource OQ14.HankelRealBasis OQ14.SourceRemotePlaneBand
open scoped Topology ComplexConjugate

theorem generatorBound_nonneg (l : ℕ) (q σ a : ℝ) (hσ : 0<σ) :
    0 ≤ generatorBound l q σ a := by
  unfold generatorBound OQ14.HankelEnergy.angular
  positivity

theorem cost_nonneg (l : ℕ) (g : Layer) : 0 ≤ cost l g :=
  mul_nonneg (generatorBound_nonneg l g.q g.σ g.a g.σ_pos) (sub_nonneg.mpr g.ordered)

theorem totalCost_nonneg (l : ℕ) (gs : List Layer) : 0 ≤ totalCost l gs := by
  unfold totalCost
  exact List.sum_nonneg (fun y hy => by
    obtain ⟨g,_,rfl⟩ := List.mem_map.mp hy
    exact cost_nonneg l g)

theorem totalCost_cons (l : ℕ) (g : Layer) (gs : List Layer) :
    totalCost l (g::gs)=cost l g+totalCost l gs := by
  simp [totalCost]

theorem profile_energy_le (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R) (s : State) (x : ℝ)
    (hRx : R<x) (hxX : x ≤ X) :
    RadialPropagation.energy (profile l gs s x).1 (profile l gs s x).2 ≤ Real.exp (totalCost l gs)*RadialPropagation.energy s.1 s.2 := by
  induction h generalizing s with
  | nil R => exact absurd (lt_of_lt_of_le hRx hxX) (lt_irrefl _)
  | cons g gs R h ih =>
    rw [totalCost_cons]
    by_cases hg : g.a<x
    · simp only [profile,if_pos hg]
      have hx0 : 0<x := g.a_pos.trans hg
      have hb := (actual_layer_energy_bound l g.q g.σ (initialAlpha l g.q g.σ g.b s.1 s.2)
        (initialBeta l g.q g.σ g.b s.1 s.2) x g.b g.q_pos.ne' g.σ_pos hx0 hxX).2
      have hbo := wave_outer l g s
      change RadialPropagation.energy (value l g.q g.σ (initialAlpha l g.q g.σ g.b s.1 s.2)
        (initialBeta l g.q g.σ g.b s.1 s.2) x) (momentum l g.q g.σ (initialAlpha l g.q g.σ g.b s.1 s.2)
        (initialBeta l g.q g.σ g.b s.1 s.2) x) ≤ _
      have hb' : RadialPropagation.energy (value l g.q g.σ (initialAlpha l g.q g.σ g.b s.1 s.2)
        (initialBeta l g.q g.σ g.b s.1 s.2) x) (momentum l g.q g.σ (initialAlpha l g.q g.σ g.b s.1 s.2)
        (initialBeta l g.q g.σ g.b s.1 s.2) x) ≤ Real.exp (generatorBound l g.q g.σ x*(g.b-x))*RadialPropagation.energy s.1 s.2 := by
        have := hb
        have h1 : value l g.q g.σ (initialAlpha l g.q g.σ g.b s.1 s.2)
            (initialBeta l g.q g.σ g.b s.1 s.2) g.b=s.1 := hbo.1
        have h2 : momentum l g.q g.σ (initialAlpha l g.q g.σ g.b s.1 s.2)
            (initialBeta l g.q g.σ g.b s.1 s.2) g.b=s.2 := hbo.2
        rwa [h1,h2] at this
      have hgen : generatorBound l g.q g.σ x ≤ generatorBound l g.q g.σ g.a := by
        unfold generatorBound
        have hA : 0 ≤ OQ14.HankelEnergy.angular l := by unfold OQ14.HankelEnergy.angular; positivity
        have : OQ14.HankelEnergy.angular l/(g.σ*x^2) ≤ OQ14.HankelEnergy.angular l/(g.σ*g.a^2) := by
          apply div_le_div_of_nonneg_left hA (mul_pos g.σ_pos (pow_pos g.a_pos 2))
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ g.a_pos.le hg.le 2) g.σ_pos.le
        linarith
      have hexp : Real.exp (generatorBound l g.q g.σ x*(g.b-x)) ≤ Real.exp (cost l g) := by
        apply Real.exp_le_exp.mpr
        unfold cost
        calc _ ≤ generatorBound l g.q g.σ g.a*(g.b-x) :=
              mul_le_mul_of_nonneg_right hgen (sub_nonneg.mpr hxX)
          _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (generatorBound_nonneg l g.q g.σ g.a g.σ_pos)
      have hE : 0 ≤ RadialPropagation.energy s.1 s.2 := RadialPropagation.energy_nonnegative _ _
      have h1 : (1 : ℝ) ≤ Real.exp (totalCost l gs) := Real.one_le_exp (totalCost_nonneg l gs)
      rw [Real.exp_add]
      calc _ ≤ Real.exp (generatorBound l g.q g.σ x*(g.b-x))*RadialPropagation.energy s.1 s.2 := hb'
        _ ≤ Real.exp (cost l g)*RadialPropagation.energy s.1 s.2 := mul_le_mul_of_nonneg_right hexp hE
        _ ≤ Real.exp (cost l g)*Real.exp (totalCost l gs)*RadialPropagation.energy s.1 s.2 := by
          have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (cost l g)).le
          nlinarith
    · simp only [profile,if_neg hg]
      have hxa : x ≤ g.a := not_lt.mp hg
      have h2 := ih (back l g s) hRx hxa
      have h3 := back_energy l g s
      rw [Real.exp_add]
      calc _ ≤ Real.exp (totalCost l gs)*RadialPropagation.energy (back l g s).1 (back l g s).2 := h2
        _ ≤ Real.exp (totalCost l gs)*(Real.exp (cost l g)*RadialPropagation.energy s.1 s.2) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        _ = _ := by ring

theorem raw_energy_le (d : Data) (x : ℝ) (hRx : d.R<x) (hxX : x ≤ d.X) :
    RadialPropagation.energy (raw d x).1 (raw d x).2 ≤
      ‖gamma d.l d.gs d.R d.X d.hR‖*(Real.exp (totalCost d.l d.gs)*frobeniusSq d.l d.X) := by
  have hX : 0<d.X := d.hR.trans_le (chain_ordered d.chain)
  have hraw : raw d x=((coefficients d.l d.gs d.R d.X d.hR).2)⁻¹ • profile d.l d.gs (outgoing d.l d.X) x := by
    simp only [raw,sourceState,if_neg (not_le.mpr hRx),outerMatched,if_pos hxX]
  have hβ : (coefficients d.l d.gs d.R d.X d.hR).2≠0 := coefficients_second_ne_zero d.l d.gs d.R d.X d.hR hX
  have hn : Complex.normSq ((coefficients d.l d.gs d.R d.X d.hR).2⁻¹) ≤ ‖gamma d.l d.gs d.R d.X d.hR‖ := by
    have him := gamma_im d.l d.gs d.R d.X d.hR hX
    have hpos : 0<Complex.normSq (coefficients d.l d.gs d.R d.X d.hR).2 := Complex.normSq_pos.mpr hβ
    have habs := Complex.abs_im_le_norm (gamma d.l d.gs d.R d.X d.hR)
    rw [him,abs_div,abs_neg,abs_one,abs_of_pos hpos] at habs
    rw [map_inv₀]
    simpa only [one_div] using habs
  have hP := profile_energy_le d.l d.chain (outgoing d.l d.X) x hRx hxX
  have hF : RadialPropagation.energy (outgoing d.l d.X).1 (outgoing d.l d.X).2=frobeniusSq d.l d.X := (frobeniusSq_eq d.l d.X).symm
  rw [hF] at hP
  rw [hraw]
  have hE : RadialPropagation.energy ((coefficients d.l d.gs d.R d.X d.hR).2⁻¹ • profile d.l d.gs (outgoing d.l d.X) x).1
      ((coefficients d.l d.gs d.R d.X d.hR).2⁻¹ • profile d.l d.gs (outgoing d.l d.X) x).2=
      Complex.normSq ((coefficients d.l d.gs d.R d.X d.hR).2⁻¹)*
        RadialPropagation.energy (profile d.l d.gs (outgoing d.l d.X) x).1 (profile d.l d.gs (outgoing d.l d.X) x).2 := by
    simp only [RadialPropagation.energy,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,map_mul]
    ring
  rw [hE]
  exact mul_le_mul hn hP (RadialPropagation.energy_nonnegative _ _) (norm_nonneg _)

theorem physical_raw_energy_uniform (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n l : ℕ) :
    ∃ s1 : ℕ, ∃ E0 : ℝ, 0 ≤ E0 ∧ ∀ s : ℕ, s1 ≤ s → ∀ x : ℝ,
      (SourcePairedGeometry.physicalData q hq n s).R<x →
      x ≤ (SourcePairedGeometry.physicalData q hq n s).X →
      RadialPropagation.energy (raw { SourcePairedGeometry.physicalData q hq n s with l := l } x).1
        (raw { SourcePairedGeometry.physicalData q hq n s with l := l } x).2 ≤ E0 := by
  let W := RadialFiniteLimit.width (RadialPairedFamily.tm q hq n)
  let C1 : ℝ := 4/(1-(1/2 : ℝ)^2)
  let K : ℝ := 2*q^2+(1/2 : ℝ)^2
  obtain ⟨s1,hs1⟩ := eventually_atTop.mp
    (RadialPhaseLimit.radius_tendsto.eventually (eventually_ge_atTop (4*OQ14.HankelEnergy.angular l+1)))
  refine ⟨s1,C1^2*Real.exp (K*W)*(Real.exp (K*W)*C1),by positivity,?_⟩
  intro s hs x hRx hxX
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
  have hγ := gamma_low_range d.l d.chain (q^2) (1/2) d.hR hc hν hpar
  have hcost := chain_cost_bound d.l d.chain (q^2) ((1/2 : ℝ)^2) d.hR (by norm_num) hν hpar
  have hF := low_range_frobeniusSq d.l (1/2) d.R d.X hc d.hR (chain_ordered d.chain) hν
  rw [hXR] at hγ hcost
  have hraw := raw_energy_le d x hRx hxX
  have h1 : ‖gamma d.l d.gs d.R d.X d.hR‖ ≤ C1^2*Real.exp (K*W) := hγ
  have h2 : Real.exp (totalCost d.l d.gs) ≤ Real.exp (K*W) := Real.exp_le_exp.mpr hcost
  have h3 : frobeniusSq d.l d.X ≤ C1 := hF
  have hfr : 0 ≤ frobeniusSq d.l d.X := by
    rw [frobeniusSq_eq]; exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  refine hraw.trans (mul_le_mul h1 (mul_le_mul h2 h3 hfr (Real.exp_pos _).le) (by positivity)
    (by positivity))

theorem select_inv_norm_le (gs : List Layer) (hσ : ∀ g ∈ gs, 1 ≤ g.σ) (r : ℝ) :
    ‖ClippedLayerProfiles.select gs (fun g _ => (g.σ : ℂ)⁻¹) (fun _ => 0) r‖ ≤ 1 := by
  induction gs with
  | nil => simp [ClippedLayerProfiles.select]
  | cons g gs ih =>
    unfold ClippedLayerProfiles.select
    by_cases h : g.a<r
    · rw [if_pos h]
      have := hσ g List.mem_cons_self
      rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos g.σ_pos]
      exact inv_le_one_of_one_le₀ this
    · rw [if_neg h]
      exact ih (fun g' hg' => hσ g' (List.mem_cons_of_mem _ hg'))

theorem inverseSigma_norm_le (d : Data) (hσ : ∀ g ∈ d.gs, 1 ≤ g.σ) (r : ℝ) (hRr : d.R<r) (hrX : r ≤ d.X) :
    ‖inverseSigma d r‖ ≤ 1 := by
  simp only [inverseSigma,extend,if_neg (not_le.mpr hRr),if_pos hrX]
  exact select_inv_norm_le d.gs hσ r

theorem electric_pol_rad (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) (x : Space) (hx : x≠0) :
    SourceUnclippedMaxwell.electric d P x=
      (((raw d ‖x‖).2/(‖x‖ : ℂ)^(d.l+2)) • HarmonicRadiationFactors.poloidal P x)+
      ((inverseSigma d ‖x‖*((d.l : ℂ)*(d.l+1)*(raw d ‖x‖).1/(‖x‖ : ℂ)^(d.l+3))) •
        HarmonicRadiationFactors.radial P x) := by
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  ext i
  simp only [SourceUnclippedMaxwell.electric,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    HarmonicRadiationFactors.poloidal_formula P d.l hp x i,HarmonicRadiationFactors.radial]
  field_simp
  ring

theorem magnetic_tor (d : Data) (P : Poly) (x : Space) (hx : x≠0) :
    SourceUnclippedMaxwell.magnetic d P x=
      ((-I*(raw d ‖x‖).1/(‖x‖ : ℂ)) • ((((‖x‖ : ℂ)^d.l)⁻¹) • DebyeRadialTrace.angularToroidal P x)) := by
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  ext i
  simp only [SourceUnclippedMaxwell.magnetic,Pi.smul_apply,smul_eq_mul]
  rw [pow_succ]
  field_simp
  left
  ring

theorem annulus_decomp (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (hσ : ∀ g ∈ d.gs, 1 ≤ g.σ) (B M0 M1 M2 : ℝ)
    (hB : ∀ r : ℝ, d.R<r → r ≤ d.X → ‖(raw d r).1‖ ≤ B ∧ ‖(raw d r).2‖ ≤ B)
    (h0 : ∀ x : Space, x≠0 → ‖(((‖x‖ : ℂ)^(d.l+1))⁻¹) • HarmonicRadiationFactors.poloidal P x‖ ≤ M0)
    (h1 : ∀ x : Space, x≠0 → ‖(((‖x‖ : ℂ)^(d.l+1))⁻¹) • HarmonicRadiationFactors.radial P x‖ ≤ M1)
    (h2 : ∀ x : Space, x≠0 → ‖(((‖x‖ : ℂ)^d.l)⁻¹) • DebyeRadialTrace.angularToroidal P x‖ ≤ M2)
    (x : Space) (hRx : d.R<‖x‖) (hxX : ‖x‖ ≤ d.X) :
    Decomp (B*M0) (B*((d.l : ℝ)*(d.l+1))*M1) (SourceUnclippedMaxwell.electric d P x) x ∧
      Decomp (B*M2) 0 (SourceUnclippedMaxwell.magnetic d P x) x := by
  have hrpos : 0<‖x‖ := d.hR.trans hRx
  have hx0 : x≠0 := norm_pos_iff.mp hrpos
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  obtain ⟨hB1,hB2⟩ := hB ‖x‖ hRx hxX
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB1
  have hσn := inverseSigma_norm_le d hσ ‖x‖ hRx hxX
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

theorem paired_annulus_decomp (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n l : ℕ) (P : Poly)
    (hp : P.IsHomogeneous l) :
    ∃ s1 : ℕ, ∃ K1 K2 L1 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ L1 ∧ ∀ s : ℕ, s1 ≤ s → ∀ x : Space,
      (SourcePairedGeometry.physicalData q hq n s).R<‖x‖ →
      ‖x‖ ≤ (SourcePairedGeometry.physicalData q hq n s).X →
      Decomp K1 K2 (SourceUnclippedMaxwell.electric { SourcePairedGeometry.physicalData q hq n s with l := l } P x) x ∧
      Decomp L1 0 (SourceUnclippedMaxwell.magnetic { SourcePairedGeometry.physicalData q hq n s with l := l } P x) x := by
  obtain ⟨s1,E0,hE0,hE⟩ := physical_raw_energy_uniform q hq hq1 n l
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
  intro s hs x hRx hxX
  exact annulus_decomp { SourcePairedGeometry.physicalData q hq n s with l := l } P hp
    (fun g hg => (SourcePairedGeometry.physical_parameters q hq hq1 n s g hg).1) (Real.sqrt E0) M0 M1 M2
    (fun r hr hrX => hBn _ _ (hE s hs r hr hrX)) h0 h1 h2 x hRx hxX

theorem paired_annulus_flux_bound (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n l : ℕ) (P : Poly)
    (hp : P.IsHomogeneous l) :
    ∃ s1 : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℕ, s1 ≤ s → ∀ x : Space, x 2=0 →
      (SourcePairedGeometry.physicalData q hq n s).R<‖x‖ →
      ‖x‖ ≤ (SourcePairedGeometry.physicalData q hq n s).X →
      ‖crossProduct (SourceUnclippedMaxwell.electric { SourcePairedGeometry.physicalData q hq n s with l := l } P x)
        (conjugate (SourceUnclippedMaxwell.magnetic { SourcePairedGeometry.physicalData q hq n s with l := l } P x)) 2‖ ≤
          C/‖x‖^3 := by
  obtain ⟨s1,K1,K2,L1,hK1,hK2,hL1,h⟩ := paired_annulus_decomp q hq hq1 n l P hp
  refine ⟨s1,2*K2*L1+2*K1*0,by positivity,?_⟩
  intro s hs x hx2 hRx hxX
  have hrpos : 0<‖x‖ := (SourcePairedGeometry.physicalData q hq n s).hR.trans hRx
  obtain ⟨hE,hH⟩ := h s hs x hRx hxX
  exact flux_bound_of_decomp x hx2 hrpos _ _ K1 K2 L1 0 hE hH

theorem paired_mode_annulus_decomp (tm : Bool) (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n l : ℕ) (P : Poly)
    (hp : P.IsHomogeneous l) :
    ∃ s1 : ℕ, ∃ K1 K2 L1 L2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ L1 ∧ 0 ≤ L2 ∧ ∀ s : ℕ, s1 ≤ s → ∀ x : Space,
      (SourcePairedGeometry.physicalData q hq n s).R<‖x‖ →
      ‖x‖ ≤ (SourcePairedGeometry.physicalData q hq n s).X →
      Decomp K1 K2 (modeElectric tm { SourcePairedGeometry.physicalData q hq n s with l := l } P x) x ∧
      Decomp L1 L2 (modeMagnetic tm { SourcePairedGeometry.physicalData q hq n s with l := l } P x) x := by
  obtain ⟨s1,K1,K2,L1,hK1,hK2,hL1,h⟩ := paired_annulus_decomp q hq hq1 n l P hp
  cases tm
  · refine ⟨s1,L1,0,‖(-1 : ℂ)‖*K1,‖(-1 : ℂ)‖*K2,hL1,le_rfl,by positivity,by positivity,?_⟩
    intro s hs x hRx hxX
    obtain ⟨hE,hH⟩ := h s hs x hRx hxX
    have : SourceGeneralMaxwell.teMagnetic { SourcePairedGeometry.physicalData q hq n s with l := l } P x=
        (-1 : ℂ) • SourceUnclippedMaxwell.electric { SourcePairedGeometry.physicalData q hq n s with l := l } P x := by
      funext i
      simp [SourceGeneralMaxwell.teMagnetic]
    simp only [modeElectric,modeMagnetic,Bool.false_eq_true,if_false,SourceGeneralMaxwell.teElectric,this]
    exact ⟨hH,decomp_smul (-1) hE⟩
  · refine ⟨s1,K1,K2,L1,0,hK1,hK2,hL1,le_rfl,?_⟩
    intro s hs x hRx hxX
    simpa only [modeElectric,modeMagnetic,if_true] using h s hs x hRx hxX

theorem band_annulus_flux_bound {ι κ : Type*} [Fintype ι] [Fintype κ] (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n : ℕ)
    (tmE : ι → Bool) (lE : ι → ℕ) (PE : ι → Poly) (hE : ∀ i, (PE i).IsHomogeneous (lE i)) (cE : ι → ℂ)
    (tmH : κ → Bool) (lH : κ → ℕ) (PH : κ → Poly) (hH : ∀ j, (PH j).IsHomogeneous (lH j)) (cH : κ → ℂ) :
    ∃ s1 : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℕ, s1 ≤ s → ∀ x : Space, x 2=0 →
      (SourcePairedGeometry.physicalData q hq n s).R<‖x‖ →
      ‖x‖ ≤ (SourcePairedGeometry.physicalData q hq n s).X →
      ‖crossProduct
        (∑ i, cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i) x)
        (conjugate (∑ j, cH j • modeMagnetic (tmH j)
          { SourcePairedGeometry.physicalData q hq n s with l := lH j } (PH j) x)) 2‖ ≤ C/‖x‖^3 := by
  choose s0 K1 K2 L1 L2 hK1 hK2 hL1 hL2 hdec using
    fun i => paired_mode_annulus_decomp (tmE i) q hq hq1 n (lE i) (PE i) (hE i)
  choose t0 M1 M2 N1 N2 hM1 hM2 hN1 hN2 hdec2 using
    fun j => paired_mode_annulus_decomp (tmH j) q hq hq1 n (lH j) (PH j) (hH j)
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
  · intro s hs x hx2 hRx hxX
    have hrpos : 0<‖x‖ := (SourcePairedGeometry.physicalData q hq n s).hR.trans hRx
    have hDE : Decomp (∑ i, ‖cE i‖*K1 i) (∑ i, ‖cE i‖*K2 i)
        (∑ i, cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i) x) x := by
      apply decomp_sum Finset.univ
        (fun i => cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i) x)
        (fun i => ‖cE i‖*K1 i) (fun i => ‖cE i‖*K2 i) x
      intro i _
      apply decomp_smul
      exact (hdec i s ((hS1' i).trans ((le_max_left _ _).trans hs)) x hRx hxX).1
    have hDH : Decomp (∑ j, ‖cH j‖*N1 j) (∑ j, ‖cH j‖*N2 j)
        (∑ j, cH j • modeMagnetic (tmH j) { SourcePairedGeometry.physicalData q hq n s with l := lH j } (PH j) x) x := by
      apply decomp_sum Finset.univ
        (fun j => cH j • modeMagnetic (tmH j) { SourcePairedGeometry.physicalData q hq n s with l := lH j } (PH j) x)
        (fun j => ‖cH j‖*N1 j) (fun j => ‖cH j‖*N2 j) x
      intro j _
      apply decomp_smul
      exact (hdec2 j s ((hS2' j).trans ((le_max_right _ _).trans hs)) x hRx hxX).2
    exact flux_bound_of_decomp x hx2 hrpos _ _ _ _ _ _ hDE hDH

end OQ14.SourceAnnulusStateBounds
#print axioms OQ14.SourceAnnulusStateBounds.generatorBound_nonneg
#print axioms OQ14.SourceAnnulusStateBounds.cost_nonneg
#print axioms OQ14.SourceAnnulusStateBounds.totalCost_nonneg
#print axioms OQ14.SourceAnnulusStateBounds.totalCost_cons
#print axioms OQ14.SourceAnnulusStateBounds.profile_energy_le
#print axioms OQ14.SourceAnnulusStateBounds.raw_energy_le
#print axioms OQ14.SourceAnnulusStateBounds.electric_pol_rad
#print axioms OQ14.SourceAnnulusStateBounds.magnetic_tor
#print axioms OQ14.SourceAnnulusStateBounds.annulus_decomp
#print axioms OQ14.SourceAnnulusStateBounds.physical_raw_energy_uniform
#print axioms OQ14.SourceAnnulusStateBounds.select_inv_norm_le
#print axioms OQ14.SourceAnnulusStateBounds.inverseSigma_norm_le
#print axioms OQ14.SourceAnnulusStateBounds.paired_annulus_decomp
#print axioms OQ14.SourceAnnulusStateBounds.paired_annulus_flux_bound
#print axioms OQ14.SourceAnnulusStateBounds.paired_mode_annulus_decomp
#print axioms OQ14.SourceAnnulusStateBounds.band_annulus_flux_bound
