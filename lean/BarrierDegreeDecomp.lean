import BarrierDegreeFluxConstants
import SourcePairedGeometry

/-! Per-degree decomposition constants, independent of the shell index, for the paired-shell source modes
normalized by the regular value at an inner scale `s0`, valid at every point outside the inner radius
(annulus and exterior alike), and their summability over the degree.

* `state_bound_low`, `state_bound_middle`: squared state magnitudes beyond the inner radius in the low
  (`2(l+1) ≤ R`) and intermediate (`l ≤ 2qR`) degree regimes; the barrier regime (`2qR ≤ l`) uses
  `BarrierAnnulusStateBounds.source_weighted_all_high` inside `weighted_state_bound`.
* `weighted_state_bound`: `|regular l s0|` times the state magnitudes is at most `Ub q W s0 R1 l` for any
  threshold `R1 ≤ R` with `max 1 (max W s0) ≤ R1`; `mode_decomp_uniform`: the corresponding `Decomp`.
* `paired_mode_decomp`, `paired_mode_series`: the physical paired data, threshold `s1pair`, constants
  `mK1 mK2 mL1 mL2` (TM/TE), their summability (also against the multiplicity `2l+1`). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.BarrierDegreeDecomp
open Complex Filter Set OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.SourceRemotePlaneBand OQ14.SphereHarmonicBasis OQ14.AngularExteriorBounds
  OQ14.BarrierDegreeFluxConstants OQ14.HankelRealBasis
open scoped Topology ComplexConjugate

/-! ### Regime bounds for the state magnitudes at every radius beyond the inner radius -/

/-- Low-degree state constant. -/
def Ulow (M W : ℝ) : ℝ :=
  OQ14.RadialLowTail.bound M W*(Real.exp ((2*M+(1/2 : ℝ)^2)*W)*(2/(1-(1/2 : ℝ)^2)+2))

theorem state_bound_low (d : Data) (M W : ℝ) (hM : 0 ≤ M) (hW : d.X-d.R ≤ W)
    (hl : 2*((d.l : ℝ)+1) ≤ d.R) (hp : ∀ g ∈ d.gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M)
    (r : ℝ) (hr : d.R<r) :
    ‖(raw d r).1‖^2 ≤ Ulow M W ∧ ‖(raw d r).2‖^2 ≤ Ulow M W := by
  have hRX := OQ14.RadialStack.chain_ordered d.chain
  have hW0 : 0 ≤ W := by linarith
  have hB0 : 0 ≤ OQ14.RadialLowTail.bound M W := by
    unfold OQ14.RadialLowTail.bound; positivity
  have hex : 1 ≤ Real.exp ((2*M+(1/2 : ℝ)^2)*W) := by
    apply Real.one_le_exp; positivity
  by_cases hrX : r ≤ d.X
  · have h := OQ14.BarrierAnnulusStateBounds.low_annulus_state_bound d.l d.chain M W hM d.hR hW hl hp r
      ⟨hr.le,hrX⟩
    have h' : ‖(raw d r).1‖^2+‖(raw d r).2‖^2 ≤ Ulow M W := h
    exact ⟨by nlinarith [sq_nonneg ‖(raw d r).2‖],by nlinarith [sq_nonneg ‖(raw d r).1‖]⟩
  · have h := OQ14.BarrierSourceStateBounds.low_exterior_state_bound d.l d.chain M W hM d.hR hW hl hp r
      (not_le.mp hrX)
    have h8 : 0 ≤ 2/(1-(1/2 : ℝ)^2) := by norm_num
    constructor
    · refine h.1.trans ?_
      unfold Ulow
      have : OQ14.RadialLowTail.bound M W*(2/(1-(1/2 : ℝ)^2)) ≤
          OQ14.RadialLowTail.bound M W*(Real.exp ((2*M+(1/2 : ℝ)^2)*W)*(2/(1-(1/2 : ℝ)^2)+2)) := by
        apply mul_le_mul_of_nonneg_left _ hB0
        nlinarith
      exact this
    · refine h.2.trans ?_
      unfold Ulow
      apply mul_le_mul_of_nonneg_left _ hB0
      nlinarith

/-- Intermediate-window state constant. -/
def midConst (q M W : ℝ) : ℝ :=
  (OQ14.RadialIntermediateBound.frameConstant q)^2*
    Real.exp (2*((2*M+OQ14.RadialIntermediateBound.angularBound q)*W))*(1+(1+2*q)^2)

theorem state_bound_middle (d : Data) (q M W : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M) (hR : 1 ≤ d.R)
    (hX : d.X ≤ 2*d.R) (hW : d.X-d.R ≤ W) (hl : (d.l : ℝ) ≤ 2*q*d.R)
    (hp : ∀ g ∈ d.gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (r : ℝ) (hr : d.R<r) :
    ‖(raw d r).1‖^2 ≤ midConst q M W*Real.exp (6*OQ14.HankelIntermediateBounds.exponent q*d.R) ∧
    ‖(raw d r).2‖^2 ≤ midConst q M W*Real.exp (6*OQ14.HankelIntermediateBounds.exponent q*d.R) := by
  have hRX := OQ14.RadialStack.chain_ordered d.chain
  have hW0 : 0 ≤ W := by linarith
  have hA : 0 ≤ OQ14.RadialIntermediateBound.angularBound q := by
    unfold OQ14.RadialIntermediateBound.angularBound; positivity
  have he : 0 ≤ OQ14.HankelIntermediateBounds.exponent q :=
    OQ14.RadialMiddleTail.exponent_nonnegative q hq
  obtain ⟨e,he_def⟩ : ∃ e, e=OQ14.HankelIntermediateBounds.exponent q := ⟨_,rfl⟩
  obtain ⟨c,hc_def⟩ : ∃ c, c=(2*M+OQ14.RadialIntermediateBound.angularBound q)*W := ⟨_,rfl⟩
  obtain ⟨fc,hfc⟩ : ∃ fc, fc=(OQ14.RadialIntermediateBound.frameConstant q)^2 := ⟨_,rfl⟩
  have hc : 0 ≤ c := by rw [hc_def]; positivity
  have hfc0 : 0 ≤ fc := by rw [hfc]; positivity
  rw [← he_def] at he
  have hmid : midConst q M W=fc*Real.exp (2*c)*(1+(1+2*q)^2) := by
    unfold midConst; rw [← hfc,← hc_def]
  have hE2 : (Real.exp (e*d.R))^2=Real.exp (2*e*d.R) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE2' : ((1+2*q)*Real.exp (e*d.R))^2=(1+2*q)^2*Real.exp (2*e*d.R) := by
    rw [mul_pow,hE2]
  have hG : Real.exp (4*e*d.R+c)=Real.exp (4*e*d.R)*Real.exp c := Real.exp_add _ _
  have h6 : Real.exp (6*e*d.R)=Real.exp (4*e*d.R)*Real.exp (2*e*d.R) := by
    rw [← Real.exp_add]; congr 1; ring
  have hc2 : Real.exp (2*c)=Real.exp c*Real.exp c := by rw [← Real.exp_add]; congr 1; ring
  have hq2 : (1+2*q)^2 ≤ 1+(1+2*q)^2 := by linarith
  have hexp6 : 0 ≤ Real.exp (6*e*d.R) := (Real.exp_pos _).le
  have hec : Real.exp c ≤ Real.exp c*Real.exp c := by
    have : 1 ≤ Real.exp c := Real.one_le_exp hc
    nlinarith [Real.exp_pos c]
  have hcore : fc*Real.exp c*Real.exp (6*e*d.R) ≤ midConst q M W*Real.exp (6*e*d.R) := by
    rw [hmid,hc2]
    apply mul_le_mul_of_nonneg_right _ hexp6
    have h2 : (1 : ℝ) ≤ 1+(1+2*q)^2 := by nlinarith
    calc fc*Real.exp c ≤ fc*(Real.exp c*Real.exp c) := mul_le_mul_of_nonneg_left hec hfc0
      _ ≤ fc*(Real.exp c*Real.exp c)*(1+(1+2*q)^2) := by
          have : 0 ≤ fc*(Real.exp c*Real.exp c) := by positivity
          nlinarith
  have hcore2 : fc*Real.exp c*((1+2*q)^2*Real.exp (6*e*d.R)) ≤ midConst q M W*Real.exp (6*e*d.R) := by
    rw [hmid,hc2]
    calc fc*Real.exp c*((1+2*q)^2*Real.exp (6*e*d.R))
        ≤ fc*(Real.exp c*Real.exp c)*((1+(1+2*q)^2)*Real.exp (6*e*d.R)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hec hfc0
          · exact mul_le_mul_of_nonneg_right hq2 hexp6
          · positivity
          · positivity
      _ = _ := by ring
  rw [← he_def]
  by_cases hrX : r ≤ d.X
  · have h := OQ14.BarrierAnnulusStateBounds.middle_annulus_state_bound d.l d.chain q M W hq hM hR hX hW hl hp r
      ⟨hr.le,hrX⟩
    rw [← he_def,← hc_def,← hfc] at h
    have hs : ‖(raw d r).1‖^2+‖(raw d r).2‖^2 ≤ midConst q M W*Real.exp (6*e*d.R) := by
      refine h.trans (le_of_eq ?_)
      rw [hmid,hE2,hE2',hG,h6,hc2]
      ring
    exact ⟨by nlinarith [sq_nonneg ‖(raw d r).2‖],by nlinarith [sq_nonneg ‖(raw d r).1‖]⟩
  · have h := OQ14.BarrierSourceStateBounds.middle_exterior_state_bound d.l d.chain q M W hq hM hR hX hW hl hp r
      (not_le.mp hrX)
    rw [← he_def,← hc_def,← hfc] at h
    constructor
    · refine h.1.trans ((le_of_eq ?_).trans hcore)
      rw [hE2,hG,h6]
      ring
    · refine h.2.trans ((le_of_eq ?_).trans hcore2)
      rw [hE2',hG,h6]
      ring

/-! ### Shell-index-independent per-degree constants -/

/-- Geometric barrier-range majorant at the threshold radius `R1`. -/
def Gh (q s0 R1 : ℝ) (l : ℕ) : ℝ := Real.exp ((l : ℝ)/(4*q))*(s0/R1)^(l+1)

/-- Weighted state majorant: regular value at `s0` times the three regime constants. -/
def Ub (q W s0 R1 : ℝ) (l : ℕ) : ℝ :=
  |regular l s0| *(Real.sqrt (Ulow (q^2) W)+
    Real.sqrt (midConst q (q^2) W*Real.exp (12*OQ14.HankelIntermediateBounds.exponent q*((l : ℝ)+1))))+
    Gh q s0 R1 l

def Kone (q W s0 R1 : ℝ) (l : ℕ) : ℝ := ((l : ℝ)+1)*envelope l*Ub q W s0 R1 l
def Ktwo (q W s0 R1 : ℝ) (l : ℕ) : ℝ := ((l : ℝ)*(l+1))*envelope l*Ub q W s0 R1 l
def Lone (q W s0 R1 : ℝ) (l : ℕ) : ℝ := 2*envelope l*Ub q W s0 R1 l

theorem Ub_nonneg (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0 ≤ s0) (hR1 : 0<R1) (l : ℕ) :
    0 ≤ Ub q W s0 R1 l := by
  unfold Ub Gh
  have hq0 : 0<q := by linarith
  positivity

/-- The weighted state magnitudes at every radius beyond the inner radius are bounded by `Ub`,
whatever the degree regime. -/
theorem weighted_state_bound (d : Data) (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hW : d.X-d.R ≤ W)
    (hR1 : max 1 (max W s0) ≤ R1) (hRR1 : R1 ≤ d.R) (hX : d.X ≤ 2*d.R)
    (hp : ∀ g ∈ d.gs,1 ≤ g.σ ∧ g.σ ≤ q^2 ∧ g.q^2 ≤ q^2) (hpq : ∀ g ∈ d.gs,g.q ≤ q)
    (hs0 : 0<s0) (r : ℝ) (hr : d.R<r) :
    |regular d.l s0| *‖(raw d r).1‖ ≤ Ub q W s0 R1 d.l ∧
    |regular d.l s0| *‖(raw d r).2‖ ≤ Ub q W s0 R1 d.l := by
  have hR1a : 1 ≤ R1 := (le_max_left _ _).trans hR1
  have hR1c : s0 ≤ R1 := ((le_max_right _ _).trans (le_max_right _ _)).trans hR1
  have hR : 1 ≤ d.R := hR1a.trans hRR1
  have hs0R : s0 ≤ d.R := hR1c.trans hRR1
  have hRpos : 0<d.R := d.hR
  have hq0 : 0 ≤ q^2 := by positivity
  have hqpos : 0<q := by linarith
  have hR1pos : 0<R1 := lt_of_lt_of_le one_pos hR1a
  have hsq1 : 0 ≤ Real.sqrt (Ulow (q^2) W) := Real.sqrt_nonneg _
  have hsq2 : 0 ≤ Real.sqrt (midConst q (q^2) W*
      Real.exp (12*OQ14.HankelIntermediateBounds.exponent q*((d.l : ℝ)+1))) := Real.sqrt_nonneg _
  have hGh : 0 ≤ Gh q s0 R1 d.l := by unfold Gh; positivity
  have habs : 0 ≤ |regular d.l s0| := abs_nonneg _
  by_cases hhigh : 2*q*d.R ≤ d.l
  · have hl2 : 2*d.R ≤ (d.l : ℝ) := by nlinarith
    have hν := OQ14.RadialHighOrderBound.high_order_barrier d.l d.R hRpos hl2
    have hA := OQ14.RiccatiSeriesCoefficients.amplitude_pos d.l 0
    have hreg : 0 ≤ regular d.l s0 := by
      have := OQ14.RiccatiGaussianBound.regular_gaussian_lower d.l d.R hRpos hν s0 ⟨hs0,hs0R⟩
      exact le_trans (by positivity) this
    obtain ⟨h1,h2⟩ := OQ14.BarrierAnnulusStateBounds.source_weighted_all_high d.l d.chain hRpos q hq hX hpq
      hhigh s0 hs0 hs0R r hr.le
    rw [abs_of_nonneg hreg]
    have hl1 : (0 : ℝ)<(d.l : ℝ)+1 := by positivity
    have e1 : 2*d.R/((d.l : ℝ)+1) ≤ 1 := by
      rw [div_le_one hl1]; linarith
    have e2 : Real.exp (d.R/2) ≤ Real.exp ((d.l : ℝ)/(4*q)) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      nlinarith
    have e3 : (s0/d.R)^(d.l+1) ≤ (s0/R1)^(d.l+1) := by
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_left hs0.le hR1pos hRR1
    have hbar1 : regular d.l s0*‖(raw d r).1‖ ≤ Gh q s0 R1 d.l := by
      refine h1.trans ?_
      unfold Gh
      calc 2*d.R*Real.exp (d.R/2)/((d.l : ℝ)+1)*(s0/d.R)^(d.l+1)
          = (2*d.R/((d.l : ℝ)+1))*Real.exp (d.R/2)*(s0/d.R)^(d.l+1) := by ring
        _ ≤ 1*Real.exp ((d.l : ℝ)/(4*q))*(s0/R1)^(d.l+1) := by
          apply mul_le_mul (mul_le_mul e1 e2 (Real.exp_pos _).le (by norm_num)) e3 (by positivity)
            (by positivity)
        _ = _ := by ring
    have hbar2 : regular d.l s0*‖(raw d r).2‖ ≤ Gh q s0 R1 d.l := by
      refine h2.trans ?_
      unfold Gh
      exact mul_le_mul e2 e3 (by positivity) (Real.exp_pos _).le
    unfold Ub
    constructor
    · nlinarith [mul_nonneg habs (add_nonneg hsq1 hsq2)]
    · nlinarith [mul_nonneg habs (add_nonneg hsq1 hsq2)]
  · push_neg at hhigh
    by_cases hlow : 2*((d.l : ℝ)+1) ≤ d.R
    · obtain ⟨u1,u2⟩ := state_bound_low d (q^2) W hq0 hW hlow hp r hr
      have b1 : ‖(raw d r).1‖ ≤ Real.sqrt (Ulow (q^2) W) := Real.le_sqrt_of_sq_le u1
      have b2 : ‖(raw d r).2‖ ≤ Real.sqrt (Ulow (q^2) W) := Real.le_sqrt_of_sq_le u2
      unfold Ub
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left b1 habs,mul_nonneg habs hsq2]
      · nlinarith [mul_le_mul_of_nonneg_left b2 habs,mul_nonneg habs hsq2]
    · push_neg at hlow
      have he : 0 ≤ OQ14.HankelIntermediateBounds.exponent q :=
        OQ14.RadialMiddleTail.exponent_nonnegative q hq
      obtain ⟨u1,u2⟩ := state_bound_middle d q (q^2) W hq hq0 hR hX hW hhigh.le hp r hr
      have hexp : Real.exp (6*OQ14.HankelIntermediateBounds.exponent q*d.R) ≤
          Real.exp (12*OQ14.HankelIntermediateBounds.exponent q*((d.l : ℝ)+1)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg he (sub_nonneg.mpr hlow.le)]
      have hmc : 0 ≤ midConst q (q^2) W := by
        unfold midConst; positivity
      have c1 : ‖(raw d r).1‖^2 ≤ midConst q (q^2) W*
          Real.exp (12*OQ14.HankelIntermediateBounds.exponent q*((d.l : ℝ)+1)) :=
        u1.trans (mul_le_mul_of_nonneg_left hexp hmc)
      have c2 : ‖(raw d r).2‖^2 ≤ midConst q (q^2) W*
          Real.exp (12*OQ14.HankelIntermediateBounds.exponent q*((d.l : ℝ)+1)) :=
        u2.trans (mul_le_mul_of_nonneg_left hexp hmc)
      have b1 := Real.le_sqrt_of_sq_le c1
      have b2 := Real.le_sqrt_of_sq_le c2
      unfold Ub
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left b1 habs,mul_nonneg habs hsq1]
      · nlinarith [mul_le_mul_of_nonneg_left b2 habs,mul_nonneg habs hsq1]

/-- Band-ready decomposition of one TM mode, normalized by the regular value at `s0`. -/
theorem mode_decomp_uniform (d : Data) (m : Index d.l) (q W s0 R1 : ℝ) (hq : 1 ≤ q)
    (hW : d.X-d.R ≤ W) (hR1 : max 1 (max W s0) ≤ R1) (hRR1 : R1 ≤ d.R) (hX : d.X ≤ 2*d.R)
    (hp : ∀ g ∈ d.gs,1 ≤ g.σ ∧ g.σ ≤ q^2 ∧ g.q^2 ≤ q^2) (hpq : ∀ g ∈ d.gs,g.q ≤ q)
    (hs0 : 0<s0) (x : Space) (hx : d.R<‖x‖) :
    Decomp (Kone q W s0 R1 d.l) (Ktwo q W s0 R1 d.l)
      (((regular d.l s0 : ℝ) : ℂ) • SourceUnclippedMaxwell.electric d (representative d.l m) x) x ∧
    Decomp (Lone q W s0 R1 d.l) 0
      (((regular d.l s0 : ℝ) : ℂ) • SourceUnclippedMaxwell.magnetic d (representative d.l m) x) x := by
  have hrpos : 0<‖x‖ := d.hR.trans hx
  have hx0 : x≠0 := norm_pos_iff.mp hrpos
  have hσ : ∀ g ∈ d.gs,1 ≤ g.σ := fun g hg => (hp g hg).1
  have he := envelope_nonnegative d.l
  obtain ⟨hU,hV⟩ := weighted_state_bound d q W s0 R1 hq hW hR1 hRR1 hX hp hpq hs0 ‖x‖ hx
  obtain ⟨hE,hH⟩ := tm_decomp_state d (representative d.l m) (representative_homogeneous d.l m)
    ((d.l+1 : ℝ)*envelope d.l) (envelope d.l) (2*envelope d.l)
    (fun n => (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => poloidal_bound d.l m n i))
    (fun n => scalar_value_bound d.l m n)
    (fun n => (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => toroidal_bound d.l m n i))
    hσ x hx0
  have hn : ‖((regular d.l s0 : ℝ) : ℂ)‖=|regular d.l s0| := by
    rw [Complex.norm_real,Real.norm_eq_abs]
  constructor
  · have h := decomp_smul ((regular d.l s0 : ℝ) : ℂ) hE
    refine decomp_mono hx0 h ?_ ?_
    · rw [hn]
      unfold Kone
      calc |regular d.l s0| *(‖(raw d ‖x‖).2‖*((d.l+1 : ℝ)*envelope d.l))
          =(|regular d.l s0| *‖(raw d ‖x‖).2‖)*((d.l+1 : ℝ)*envelope d.l) := by ring
        _ ≤ Ub q W s0 R1 d.l*((d.l+1 : ℝ)*envelope d.l) :=
          mul_le_mul_of_nonneg_right hV (by positivity)
        _ =((d.l : ℝ)+1)*envelope d.l*Ub q W s0 R1 d.l := by ring
    · rw [hn]
      unfold Ktwo
      calc |regular d.l s0| *(((d.l : ℝ)*(d.l+1))*‖(raw d ‖x‖).1‖*envelope d.l)
          =(|regular d.l s0| *‖(raw d ‖x‖).1‖)*(((d.l : ℝ)*(d.l+1))*envelope d.l) := by ring
        _ ≤ Ub q W s0 R1 d.l*(((d.l : ℝ)*(d.l+1))*envelope d.l) :=
          mul_le_mul_of_nonneg_right hU (by positivity)
        _ =((d.l : ℝ)*(d.l+1))*envelope d.l*Ub q W s0 R1 d.l := by ring
  · have h := decomp_smul ((regular d.l s0 : ℝ) : ℂ) hH
    refine decomp_mono hx0 h ?_ (by simp)
    rw [hn]
    unfold Lone
    calc |regular d.l s0| *(‖(raw d ‖x‖).1‖*(2*envelope d.l))
        =(|regular d.l s0| *‖(raw d ‖x‖).1‖)*(2*envelope d.l) := by ring
      _ ≤ Ub q W s0 R1 d.l*(2*envelope d.l) := mul_le_mul_of_nonneg_right hU (by positivity)
      _ =2*envelope d.l*Ub q W s0 R1 d.l := by ring

/-! ### Factorial decay of the inner-scale regular value and summability over the degree -/

theorem regular_abs_le (s0 : ℝ) (hs0 : 0<s0) (l : ℕ) (hl : s0 ≤ (l : ℝ)) :
    |regular l s0| ≤ s0^(l+1)/(l.factorial : ℝ) := by
  have hb : s0^2 < OQ14.RiccatiBarrier.ν l := by
    unfold OQ14.RiccatiBarrier.ν
    nlinarith [mul_self_le_mul_self hs0.le hl]
  have hmem : s0 ∈ Ioc 0 s0 := ⟨hs0,le_rfl⟩
  have hlow := OQ14.RiccatiGaussianBound.regular_gaussian_lower l s0 hs0 hb s0 hmem
  have hup := OQ14.RiccatiGaussianBound.regular_upper l s0 hs0 hb s0 hmem
  have hA := OQ14.RiccatiSeriesCoefficients.amplitude_pos l 0
  have hnn : 0 ≤ regular l s0 := le_trans (by positivity) hlow
  rw [abs_of_nonneg hnn]
  have hf := OQ14.RiccatiFactorialTail.amplitude_factorial_bound l
  calc regular l s0 ≤ OQ14.RiccatiSeriesCoefficients.amplitude l 0*s0^(l+1) := hup
    _ ≤ 1/(l.factorial : ℝ)*s0^(l+1) := mul_le_mul_of_nonneg_right hf (by positivity)
    _ = s0^(l+1)/(l.factorial : ℝ) := by ring

theorem sqrt_mid_eq (q M W : ℝ) (hmc : 0 ≤ midConst q M W) (l : ℕ) :
    Real.sqrt (midConst q M W*Real.exp (12*OQ14.HankelIntermediateBounds.exponent q*((l : ℝ)+1))) =
      Real.sqrt (midConst q M W)*(Real.exp (6*OQ14.HankelIntermediateBounds.exponent q)*
        (Real.exp (6*OQ14.HankelIntermediateBounds.exponent q))^l) := by
  have hz : Real.exp (12*OQ14.HankelIntermediateBounds.exponent q*((l : ℝ)+1)) =
      (Real.exp (6*OQ14.HankelIntermediateBounds.exponent q)*
        (Real.exp (6*OQ14.HankelIntermediateBounds.exponent q))^l)^2 := by
    rw [← pow_succ',← pow_mul,← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hz,Real.sqrt_mul hmc,Real.sqrt_sq (by positivity)]

theorem Gh_term_eq (q s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1) (j l : ℕ) :
    ((l : ℝ)+1)^j*envelope l*Gh q s0 R1 l =
      (scale*(s0/R1)/(base*Real.exp (1/(4*q))*s0/R1))*
        (((l : ℝ)+1)^(j+3)*(base*Real.exp (1/(4*q))*s0/R1)^(l+1)) := by
  have hb := base_pos
  have hq0 : 0<q := by linarith
  obtain ⟨E',hE'⟩ : ∃ E', E'=Real.exp (1/(4*q)) := ⟨_,rfl⟩
  have hE'pos : 0<E' := by rw [hE']; exact Real.exp_pos _
  have hexp : Real.exp ((l : ℝ)/(4*q))=E'^l := by
    rw [hE',← Real.exp_nat_mul]
    congr 1
    ring
  rw [← hE']
  unfold envelope Gh
  rw [hexp]
  have hρ' : base*E'*s0/R1=base*E'*(s0/R1) := by ring
  have hρpos : 0<base*E'*(s0/R1) := by positivity
  have hbne : base ≠ 0 := hb.ne'
  have hEne : E' ≠ 0 := hE'pos.ne'
  have hsne : s0 ≠ 0 := hs0.ne'
  have hRne : R1 ≠ 0 := hR1.ne'
  rw [hρ']
  field_simp
  ring

theorem piece_bound (j l : ℕ) (s0 A1 c2 E : ℝ) (hs0 : 0 ≤ s0) (hA : 0 ≤ A1) (hc : 0 ≤ c2) (hE : 1 ≤ E) :
    ((l : ℝ)+1)^j*envelope l*(s0^(l+1)/(l.factorial : ℝ)*(A1+c2*(E*E^l))) ≤
      (scale*s0*(A1+c2*E))*((2^(j+3)*base*s0*E)^l/(l.factorial : ℝ)) := by
  have hb := base_pos
  have hsc := scale_pos
  have hfac : 0<(l.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos l
  have hEl : 1 ≤ E^l := one_le_pow₀ hE
  have hE0 : 0<E := by linarith
  have h1 : ((l : ℝ)+1)^(j+3) ≤ ((2 : ℝ)^(j+3))^l := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ ((l : ℝ)+1)) (OQ14.RiccatiFactorialTail.successor_le_two_pow l) (j+3)
    simpa only [← pow_mul,Nat.mul_comm] using h
  have h2 : A1+c2*(E*E^l) ≤ (A1+c2*E)*E^l := by
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hEl)]
  have hq1 : ((l : ℝ)+1)^j*envelope l*(s0^(l+1)/(l.factorial : ℝ)*(A1+c2*(E*E^l))) =
      scale*((l : ℝ)+1)^(j+3)*(base^l*s0^(l+1)/(l.factorial : ℝ))*(A1+c2*(E*E^l)) := by
    unfold envelope
    ring
  rw [hq1]
  calc scale*((l : ℝ)+1)^(j+3)*(base^l*s0^(l+1)/(l.factorial : ℝ))*(A1+c2*(E*E^l))
      ≤ scale*((2 : ℝ)^(j+3))^l*(base^l*s0^(l+1)/(l.factorial : ℝ))*((A1+c2*E)*E^l) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hsc.le) (by positivity)
        · exact h2
        · positivity
        · positivity
    _ = (scale*s0*(A1+c2*E))*((2^(j+3)*base*s0*E)^l/(l.factorial : ℝ)) := by
        rw [mul_pow,mul_pow,mul_pow,pow_succ s0 l]
        ring

theorem summable_Ub_weighted (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) (j : ℕ) :
    Summable (fun l : ℕ => ((l : ℝ)+1)^j*envelope l*Ub q W s0 R1 l) := by
  have hb := base_pos
  have hsc := scale_pos
  have hq0 : 0<q := by linarith
  have he : 0 ≤ OQ14.HankelIntermediateBounds.exponent q :=
    OQ14.RadialMiddleTail.exponent_nonnegative q hq
  have hmc : 0 ≤ midConst q (q^2) W := by unfold midConst; positivity
  have hA : 0 ≤ Real.sqrt (Ulow (q^2) W) := Real.sqrt_nonneg _
  have hc2 : 0 ≤ Real.sqrt (midConst q (q^2) W) := Real.sqrt_nonneg _
  have hE1 : 1 ≤ Real.exp (6*OQ14.HankelIntermediateBounds.exponent q) :=
    Real.one_le_exp (by positivity)
  have hρ0 : 0<base*Real.exp (1/(4*q))*s0/R1 := by positivity
  have hρ1 : base*Real.exp (1/(4*q))*s0/R1<1 := by rw [div_lt_one hR1]; exact hρ
  have hs1 := ((Real.summable_pow_div_factorial
    (2^(j+3)*base*s0*Real.exp (6*OQ14.HankelIntermediateBounds.exponent q))).mul_left
    (scale*s0*(Real.sqrt (Ulow (q^2) W)+Real.sqrt (midConst q (q^2) W)*
      Real.exp (6*OQ14.HankelIntermediateBounds.exponent q))))
  have hs2 := summable_poly_geometric (j+3) (scale*(s0/R1)/(base*Real.exp (1/(4*q))*s0/R1))
    (base*Real.exp (1/(4*q))*s0/R1) hρ0 hρ1
  refine Summable.of_norm_bounded_eventually_nat _ (hs1.add hs2) ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈s0⌉₊] with l hl
  have hs0l : s0 ≤ (l : ℝ) := (Nat.le_ceil s0).trans (Nat.cast_le.mpr hl)
  have hreg := regular_abs_le s0 hs0 l hs0l
  have hmid := sqrt_mid_eq q (q^2) W hmc l
  have henv := envelope_nonnegative l
  have hUbn := Ub_nonneg q W s0 R1 hq hs0.le hR1 l
  have hnn : 0 ≤ ((l : ℝ)+1)^j*envelope l*Ub q W s0 R1 l := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hnn]
  have hpos1 : 0 ≤ Real.sqrt (Ulow (q^2) W)+Real.sqrt (midConst q (q^2) W)*
      (Real.exp (6*OQ14.HankelIntermediateBounds.exponent q)*
        (Real.exp (6*OQ14.HankelIntermediateBounds.exponent q))^l) := by positivity
  have hUb : Ub q W s0 R1 l ≤ s0^(l+1)/(l.factorial : ℝ)*(Real.sqrt (Ulow (q^2) W)+
      Real.sqrt (midConst q (q^2) W)*(Real.exp (6*OQ14.HankelIntermediateBounds.exponent q)*
        (Real.exp (6*OQ14.HankelIntermediateBounds.exponent q))^l))+Gh q s0 R1 l := by
    unfold Ub
    rw [hmid]
    have := mul_le_mul_of_nonneg_right hreg hpos1
    linarith
  have hP := piece_bound j l s0 (Real.sqrt (Ulow (q^2) W)) (Real.sqrt (midConst q (q^2) W))
    (Real.exp (6*OQ14.HankelIntermediateBounds.exponent q)) hs0.le hA hc2 hE1
  have hG := Gh_term_eq q s0 R1 hq hs0 hR1 j l
  have hpre : 0 ≤ ((l : ℝ)+1)^j*envelope l := by positivity
  calc ((l : ℝ)+1)^j*envelope l*Ub q W s0 R1 l
      ≤ ((l : ℝ)+1)^j*envelope l*(s0^(l+1)/(l.factorial : ℝ)*(Real.sqrt (Ulow (q^2) W)+
          Real.sqrt (midConst q (q^2) W)*(Real.exp (6*OQ14.HankelIntermediateBounds.exponent q)*
            (Real.exp (6*OQ14.HankelIntermediateBounds.exponent q))^l))+Gh q s0 R1 l) :=
        mul_le_mul_of_nonneg_left hUb hpre
    _ = ((l : ℝ)+1)^j*envelope l*(s0^(l+1)/(l.factorial : ℝ)*(Real.sqrt (Ulow (q^2) W)+
          Real.sqrt (midConst q (q^2) W)*(Real.exp (6*OQ14.HankelIntermediateBounds.exponent q)*
            (Real.exp (6*OQ14.HankelIntermediateBounds.exponent q))^l)))+
        ((l : ℝ)+1)^j*envelope l*Gh q s0 R1 l := by ring
    _ ≤ _ := add_le_add hP (le_of_eq hG)

theorem summable_of_le_weighted (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) (F : ℕ → ℝ) (c : ℝ) (j : ℕ)
    (hF0 : ∀ l, 0 ≤ F l)
    (hFle : ∀ l : ℕ, F l ≤ c*(((l : ℝ)+1)^j*envelope l*Ub q W s0 R1 l)) : Summable F :=
  Summable.of_nonneg_of_le hF0 hFle ((summable_Ub_weighted q W s0 R1 hq hs0 hR1 hρ j).mul_left c)

theorem Kone_nonneg (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0 ≤ s0) (hR1 : 0<R1) (l : ℕ) :
    0 ≤ Kone q W s0 R1 l := by
  have := Ub_nonneg q W s0 R1 hq hs0 hR1 l
  have := envelope_nonnegative l
  unfold Kone; positivity

theorem Ktwo_nonneg (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0 ≤ s0) (hR1 : 0<R1) (l : ℕ) :
    0 ≤ Ktwo q W s0 R1 l := by
  have := Ub_nonneg q W s0 R1 hq hs0 hR1 l
  have := envelope_nonnegative l
  unfold Ktwo; positivity

theorem Lone_nonneg (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0 ≤ s0) (hR1 : 0<R1) (l : ℕ) :
    0 ≤ Lone q W s0 R1 l := by
  have := Ub_nonneg q W s0 R1 hq hs0 hR1 l
  have := envelope_nonnegative l
  unfold Lone; positivity

theorem summable_Kone (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) : Summable (Kone q W s0 R1) := by
  refine (summable_Ub_weighted q W s0 R1 hq hs0 hR1 hρ 1).congr (fun l => ?_)
  unfold Kone
  ring

theorem summable_Ktwo (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) : Summable (Ktwo q W s0 R1) := by
  refine summable_of_le_weighted q W s0 R1 hq hs0 hR1 hρ _ 1 2 (Ktwo_nonneg q W s0 R1 hq hs0.le hR1) ?_
  intro l
  have hU := Ub_nonneg q W s0 R1 hq hs0.le hR1 l
  have he := envelope_nonnegative l
  unfold Ktwo
  have h : (l : ℝ)*(l+1) ≤ 1*((l : ℝ)+1)^2 := by nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
  calc ((l : ℝ)*(l+1))*envelope l*Ub q W s0 R1 l
      ≤ (1*((l : ℝ)+1)^2)*envelope l*Ub q W s0 R1 l :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h he) hU
    _ = 1*(((l : ℝ)+1)^2*envelope l*Ub q W s0 R1 l) := by ring

theorem summable_Lone (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) : Summable (Lone q W s0 R1) := by
  refine ((summable_Ub_weighted q W s0 R1 hq hs0 hR1 hρ 0).mul_left 2).congr (fun l => ?_)
  unfold Lone
  ring

/-- Multiplicity-weighted versions (the degree `l` has `2l+1` independent modes). -/
theorem summable_mult_Kone (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) :
    Summable (fun l : ℕ => (2*(l : ℝ)+1)*Kone q W s0 R1 l) := by
  refine summable_of_le_weighted q W s0 R1 hq hs0 hR1 hρ _ 2 2 (fun l => ?_) ?_
  · have := Kone_nonneg q W s0 R1 hq hs0.le hR1 l
    show 0 ≤ (2*(l : ℝ)+1)*Kone q W s0 R1 l
    positivity
  · intro l
    have hU := Ub_nonneg q W s0 R1 hq hs0.le hR1 l
    have he := envelope_nonnegative l
    unfold Kone
    have h : (2*(l : ℝ)+1)*((l : ℝ)+1) ≤ 2*((l : ℝ)+1)^2 := by nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
    calc (2*(l : ℝ)+1)*(((l : ℝ)+1)*envelope l*Ub q W s0 R1 l)
        = ((2*(l : ℝ)+1)*((l : ℝ)+1))*envelope l*Ub q W s0 R1 l := by ring
      _ ≤ (2*((l : ℝ)+1)^2)*envelope l*Ub q W s0 R1 l :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h he) hU
      _ = 2*(((l : ℝ)+1)^2*envelope l*Ub q W s0 R1 l) := by ring

theorem summable_mult_Ktwo (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) :
    Summable (fun l : ℕ => (2*(l : ℝ)+1)*Ktwo q W s0 R1 l) := by
  refine summable_of_le_weighted q W s0 R1 hq hs0 hR1 hρ _ 2 3 (fun l => ?_) ?_
  · have := Ktwo_nonneg q W s0 R1 hq hs0.le hR1 l
    show 0 ≤ (2*(l : ℝ)+1)*Ktwo q W s0 R1 l
    positivity
  · intro l
    have hU := Ub_nonneg q W s0 R1 hq hs0.le hR1 l
    have he := envelope_nonnegative l
    unfold Ktwo
    have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have h : (2*(l : ℝ)+1)*((l : ℝ)*(l+1)) ≤ 2*((l : ℝ)+1)^3 := by nlinarith [mul_nonneg hl0 hl0]
    calc (2*(l : ℝ)+1)*(((l : ℝ)*(l+1))*envelope l*Ub q W s0 R1 l)
        = ((2*(l : ℝ)+1)*((l : ℝ)*(l+1)))*envelope l*Ub q W s0 R1 l := by ring
      _ ≤ (2*((l : ℝ)+1)^3)*envelope l*Ub q W s0 R1 l :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h he) hU
      _ = 2*(((l : ℝ)+1)^3*envelope l*Ub q W s0 R1 l) := by ring

theorem summable_mult_Lone (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) :
    Summable (fun l : ℕ => (2*(l : ℝ)+1)*Lone q W s0 R1 l) := by
  refine summable_of_le_weighted q W s0 R1 hq hs0 hR1 hρ _ 4 1 (fun l => ?_) ?_
  · have := Lone_nonneg q W s0 R1 hq hs0.le hR1 l
    show 0 ≤ (2*(l : ℝ)+1)*Lone q W s0 R1 l
    positivity
  · intro l
    have hU := Ub_nonneg q W s0 R1 hq hs0.le hR1 l
    have he := envelope_nonnegative l
    unfold Lone
    have h : (2*(l : ℝ)+1) ≤ 2*((l : ℝ)+1)^1 := by nlinarith [(Nat.cast_nonneg l : (0 : ℝ) ≤ l)]
    calc (2*(l : ℝ)+1)*(2*envelope l*Ub q W s0 R1 l)
        = 2*((2*(l : ℝ)+1)*envelope l*Ub q W s0 R1 l) := by ring
      _ ≤ 2*((2*((l : ℝ)+1)^1)*envelope l*Ub q W s0 R1 l) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h he) hU)
          (by norm_num)
      _ = 4*(((l : ℝ)+1)^1*envelope l*Ub q W s0 R1 l) := by ring

/-! ### Mode-indexed constants: TM uses `(Kone,Ktwo)` for the electric and `(Lone,0)` for the magnetic
field; the TE mode swaps them through `teElectric = magnetic`, `teMagnetic = -electric`. -/

def mK1 (tm : Bool) (q W s0 R1 : ℝ) (l : ℕ) : ℝ :=
  if tm then Kone q W s0 R1 l else Lone q W s0 R1 l
def mK2 (tm : Bool) (q W s0 R1 : ℝ) (l : ℕ) : ℝ :=
  if tm then Ktwo q W s0 R1 l else 0
def mL1 (tm : Bool) (q W s0 R1 : ℝ) (l : ℕ) : ℝ :=
  if tm then Lone q W s0 R1 l else Kone q W s0 R1 l
def mL2 (tm : Bool) (q W s0 R1 : ℝ) (l : ℕ) : ℝ :=
  if tm then 0 else Ktwo q W s0 R1 l

theorem mK1_true (q W s0 R1 : ℝ) : mK1 true q W s0 R1 = Kone q W s0 R1 := by funext l; simp [mK1]
theorem mK1_false (q W s0 R1 : ℝ) : mK1 false q W s0 R1 = Lone q W s0 R1 := by funext l; simp [mK1]
theorem mK2_true (q W s0 R1 : ℝ) : mK2 true q W s0 R1 = Ktwo q W s0 R1 := by funext l; simp [mK2]
theorem mK2_false (q W s0 R1 : ℝ) : mK2 false q W s0 R1 = fun _ => 0 := by funext l; simp [mK2]
theorem mL1_true (q W s0 R1 : ℝ) : mL1 true q W s0 R1 = Lone q W s0 R1 := by funext l; simp [mL1]
theorem mL1_false (q W s0 R1 : ℝ) : mL1 false q W s0 R1 = Kone q W s0 R1 := by funext l; simp [mL1]
theorem mL2_true (q W s0 R1 : ℝ) : mL2 true q W s0 R1 = fun _ => 0 := by funext l; simp [mL2]
theorem mL2_false (q W s0 R1 : ℝ) : mL2 false q W s0 R1 = Ktwo q W s0 R1 := by funext l; simp [mL2]

theorem mode_constants_nonneg (tm : Bool) (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0 ≤ s0) (hR1 : 0<R1)
    (l : ℕ) :
    0 ≤ mK1 tm q W s0 R1 l ∧ 0 ≤ mK2 tm q W s0 R1 l ∧ 0 ≤ mL1 tm q W s0 R1 l ∧
      0 ≤ mL2 tm q W s0 R1 l := by
  have h1 := Kone_nonneg q W s0 R1 hq hs0 hR1 l
  have h2 := Ktwo_nonneg q W s0 R1 hq hs0 hR1 l
  have h3 := Lone_nonneg q W s0 R1 hq hs0 hR1 l
  cases tm <;> simp [mK1,mK2,mL1,mL2,h1,h2,h3]

theorem mode_constants_summable (tm : Bool) (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) :
    Summable (mK1 tm q W s0 R1) ∧ Summable (mK2 tm q W s0 R1) ∧ Summable (mL1 tm q W s0 R1) ∧
      Summable (mL2 tm q W s0 R1) ∧
    Summable (fun l : ℕ => (2*(l : ℝ)+1)*mK1 tm q W s0 R1 l) ∧
    Summable (fun l : ℕ => (2*(l : ℝ)+1)*mK2 tm q W s0 R1 l) ∧
    Summable (fun l : ℕ => (2*(l : ℝ)+1)*mL1 tm q W s0 R1 l) ∧
    Summable (fun l : ℕ => (2*(l : ℝ)+1)*mL2 tm q W s0 R1 l) := by
  have h1 := summable_Kone q W s0 R1 hq hs0 hR1 hρ
  have h2 := summable_Ktwo q W s0 R1 hq hs0 hR1 hρ
  have h3 := summable_Lone q W s0 R1 hq hs0 hR1 hρ
  have m1 := summable_mult_Kone q W s0 R1 hq hs0 hR1 hρ
  have m2 := summable_mult_Ktwo q W s0 R1 hq hs0 hR1 hρ
  have m3 := summable_mult_Lone q W s0 R1 hq hs0 hR1 hρ
  have z : Summable (fun l : ℕ => (2*(l : ℝ)+1)*(0 : ℝ)) := by simpa using summable_zero
  cases tm
  · simp only [mK1_false,mK2_false,mL1_false,mL2_false]
    exact ⟨h3,summable_zero,h1,h2,m3,z,m1,m2⟩
  · simp only [mK1_true,mK2_true,mL1_true,mL2_true]
    exact ⟨h1,h2,h3,summable_zero,m1,m2,m3,z⟩

/-! ### Paired physical data -/

/-- Total width of the TM quarter-pair family (the outer minus the inner radius of every shell). -/
def Wpair (q : ℝ) (hq : 0<q) (n : ℕ) : ℝ :=
  OQ14.RadialFiniteLimit.width (OQ14.RadialPairedFamily.tm q hq n)

/-- The single threshold radius: at least `1`, the width, the inner scale, and twice the geometric
rate constant times the inner scale. -/
def R1pair (q : ℝ) (hq : 0<q) (n : ℕ) (s0 : ℝ) : ℝ :=
  max (max 1 (max (Wpair q hq n) s0)) (2*(base*Real.exp (1/(4*q))*s0))

/-- The shell index beyond which the inner radius `2π(s+1)` is at least `R1pair`. -/
def s1pair (q : ℝ) (hq : 0<q) (n : ℕ) (s0 : ℝ) : ℕ := ⌈R1pair q hq n s0⌉₊

theorem R1pair_max_le (q : ℝ) (hq : 0<q) (n : ℕ) (s0 : ℝ) :
    max 1 (max (Wpair q hq n) s0) ≤ R1pair q hq n s0 := le_max_left _ _

theorem R1pair_pos (q : ℝ) (hq : 0<q) (n : ℕ) (s0 : ℝ) : 0<R1pair q hq n s0 :=
  lt_of_lt_of_le one_pos ((le_max_left _ _).trans (R1pair_max_le q hq n s0))

theorem R1pair_rate (q : ℝ) (hq : 0<q) (n : ℕ) (s0 : ℝ) (hs0 : 0<s0) :
    base*Real.exp (1/(4*q))*s0 < R1pair q hq n s0 := by
  have hb := base_pos
  have hx : 0<base*Real.exp (1/(4*q))*s0 := by positivity
  exact lt_of_lt_of_le (by linarith : base*Real.exp (1/(4*q))*s0 < 2*(base*Real.exp (1/(4*q))*s0))
    (le_max_right _ _)

theorem radius_ge_R1pair (q : ℝ) (hq : 0<q) (n : ℕ) (s0 : ℝ) (s : ℕ) (hs : s1pair q hq n s0 ≤ s) :
    R1pair q hq n s0 ≤ OQ14.RadialPhaseLimit.radius s := by
  have h1 : R1pair q hq n s0 ≤ (s : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr hs)
  have h2 := Real.two_le_pi
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  unfold OQ14.RadialPhaseLimit.radius
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.pi-2) hs0]

/-- **Per-mode decomposition for the physical paired data.**  For `q ≥ 1`, `n`, an inner scale `s0 > 0`,
every degree `l`, every real mode `m`, every shell index `s ≥ s1pair`, and every point strictly outside
the inner radius `radius s` (annulus and exterior alike), the mode normalized by the regular value at
`s0` decomposes with constants independent of `s`. -/
theorem paired_mode_decomp (tm : Bool) (q : ℝ) (hq : 0<q) (hq1 : 1 ≤ q) (n : ℕ) (s0 : ℝ) (hs0 : 0<s0)
    (l : ℕ) (m : Index l) (s : ℕ) (x : Space) (hs : s1pair q hq n s0 ≤ s)
    (hx : (OQ14.SourcePairedGeometry.physicalData q hq n s).R<‖x‖) :
    Decomp (mK1 tm q (Wpair q hq n) s0 (R1pair q hq n s0) l)
      (mK2 tm q (Wpair q hq n) s0 (R1pair q hq n s0) l)
      (((regular l s0 : ℝ) : ℂ) •
        modeElectric tm { OQ14.SourcePairedGeometry.physicalData q hq n s with l := l }
          (representative l m) x) x ∧
    Decomp (mL1 tm q (Wpair q hq n) s0 (R1pair q hq n s0) l)
      (mL2 tm q (Wpair q hq n) s0 (R1pair q hq n s0) l)
      (((regular l s0 : ℝ) : ℂ) •
        modeMagnetic tm { OQ14.SourcePairedGeometry.physicalData q hq n s with l := l }
          (representative l m) x) x := by
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
  have hrpos : 0<‖x‖ := (OQ14.SourcePairedGeometry.physicalData q hq n s).hR.trans hx
  have hx0 : x≠0 := norm_pos_iff.mp hrpos
  obtain ⟨hE,hH⟩ := mode_decomp_uniform { OQ14.SourcePairedGeometry.physicalData q hq n s with l := l } m
    q (Wpair q hq n) s0 (R1pair q hq n s0) hq1 hW hmax hrad hX
    (fun g hg => ⟨(hpar g hg).1,(hpar g hg).2.1,(hpar g hg).2.2.1⟩)
    (fun g hg => (hpar g hg).2.2.2) hs0 x hx
  cases tm
  · have hE' := decomp_smul (-1 : ℂ) hE
    have hn : ‖(-1 : ℂ)‖=1 := by simp
    rw [hn,one_mul,one_mul] at hE'
    have heq : ((regular l s0 : ℝ) : ℂ) •
        SourceGeneralMaxwell.teMagnetic { OQ14.SourcePairedGeometry.physicalData q hq n s with l := l }
          (representative l m) x =
        (-1 : ℂ) • (((regular l s0 : ℝ) : ℂ) • SourceUnclippedMaxwell.electric
          { OQ14.SourcePairedGeometry.physicalData q hq n s with l := l } (representative l m) x) := by
      funext i
      simp [SourceGeneralMaxwell.teMagnetic]
    simp only [modeElectric,modeMagnetic,Bool.false_eq_true,if_false,SourceGeneralMaxwell.teElectric,
      mK1,mK2,mL1,mL2,heq]
    exact ⟨hH,hE'⟩
  · simp only [modeElectric,modeMagnetic,if_true,mK1,mK2,mL1,mL2]
    exact ⟨hE,hH⟩

/-- **Packaged series form.**  For fixed `tm`, `q ≥ 1`, `n`, `s0 > 0` there are explicit
shell-independent per-degree constants `K1 K2 L1 L2` (nonnegative, summable, also summable against the
multiplicity `2l+1`) and a threshold `s1` such that the normalized mode of every degree and every real
mode decomposes with them at every point outside the inner radius, for every shell index `s ≥ s1`. -/
theorem paired_mode_series (tm : Bool) (q : ℝ) (hq : 0<q) (hq1 : 1 ≤ q) (n : ℕ) (s0 : ℝ) (hs0 : 0<s0) :
    ∃ s1 : ℕ, ∃ K1 K2 L1 L2 : ℕ → ℝ,
      (∀ l, 0 ≤ K1 l ∧ 0 ≤ K2 l ∧ 0 ≤ L1 l ∧ 0 ≤ L2 l) ∧
      Summable K1 ∧ Summable K2 ∧ Summable L1 ∧ Summable L2 ∧
      Summable (fun l : ℕ => (2*(l : ℝ)+1)*K1 l) ∧ Summable (fun l : ℕ => (2*(l : ℝ)+1)*K2 l) ∧
      Summable (fun l : ℕ => (2*(l : ℝ)+1)*L1 l) ∧ Summable (fun l : ℕ => (2*(l : ℝ)+1)*L2 l) ∧
      ∀ (l : ℕ) (m : Index l) (s : ℕ) (x : Space), s1 ≤ s →
        (OQ14.SourcePairedGeometry.physicalData q hq n s).R<‖x‖ →
        Decomp (K1 l) (K2 l) (((regular l s0 : ℝ) : ℂ) •
          modeElectric tm { OQ14.SourcePairedGeometry.physicalData q hq n s with l := l }
            (representative l m) x) x ∧
        Decomp (L1 l) (L2 l) (((regular l s0 : ℝ) : ℂ) •
          modeMagnetic tm { OQ14.SourcePairedGeometry.physicalData q hq n s with l := l }
            (representative l m) x) x := by
  have hR1 := R1pair_pos q hq n s0
  have hρ := R1pair_rate q hq n s0 hs0
  obtain ⟨a1,a2,a3,a4,b1,b2,b3,b4⟩ := mode_constants_summable tm q (Wpair q hq n) s0
    (R1pair q hq n s0) hq1 hs0 hR1 hρ
  refine ⟨s1pair q hq n s0,mK1 tm q (Wpair q hq n) s0 (R1pair q hq n s0),
    mK2 tm q (Wpair q hq n) s0 (R1pair q hq n s0),mL1 tm q (Wpair q hq n) s0 (R1pair q hq n s0),
    mL2 tm q (Wpair q hq n) s0 (R1pair q hq n s0),
    fun l => mode_constants_nonneg tm q (Wpair q hq n) s0 (R1pair q hq n s0) hq1 hs0.le hR1 l,
    a1,a2,a3,a4,b1,b2,b3,b4,?_⟩
  intro l m s x hs hx
  exact paired_mode_decomp tm q hq hq1 n s0 hs0 l m s x hs hx

end OQ14.BarrierDegreeDecomp
#print axioms OQ14.BarrierDegreeDecomp.state_bound_low
#print axioms OQ14.BarrierDegreeDecomp.state_bound_middle
#print axioms OQ14.BarrierDegreeDecomp.Ub_nonneg
#print axioms OQ14.BarrierDegreeDecomp.weighted_state_bound
#print axioms OQ14.BarrierDegreeDecomp.mode_decomp_uniform
#print axioms OQ14.BarrierDegreeDecomp.regular_abs_le
#print axioms OQ14.BarrierDegreeDecomp.sqrt_mid_eq
#print axioms OQ14.BarrierDegreeDecomp.Gh_term_eq
#print axioms OQ14.BarrierDegreeDecomp.piece_bound
#print axioms OQ14.BarrierDegreeDecomp.summable_Ub_weighted
#print axioms OQ14.BarrierDegreeDecomp.summable_of_le_weighted
#print axioms OQ14.BarrierDegreeDecomp.Kone_nonneg
#print axioms OQ14.BarrierDegreeDecomp.Ktwo_nonneg
#print axioms OQ14.BarrierDegreeDecomp.Lone_nonneg
#print axioms OQ14.BarrierDegreeDecomp.summable_Kone
#print axioms OQ14.BarrierDegreeDecomp.summable_Ktwo
#print axioms OQ14.BarrierDegreeDecomp.summable_Lone
#print axioms OQ14.BarrierDegreeDecomp.summable_mult_Kone
#print axioms OQ14.BarrierDegreeDecomp.summable_mult_Ktwo
#print axioms OQ14.BarrierDegreeDecomp.summable_mult_Lone
#print axioms OQ14.BarrierDegreeDecomp.mK1_true
#print axioms OQ14.BarrierDegreeDecomp.mK1_false
#print axioms OQ14.BarrierDegreeDecomp.mK2_true
#print axioms OQ14.BarrierDegreeDecomp.mK2_false
#print axioms OQ14.BarrierDegreeDecomp.mL1_true
#print axioms OQ14.BarrierDegreeDecomp.mL1_false
#print axioms OQ14.BarrierDegreeDecomp.mL2_true
#print axioms OQ14.BarrierDegreeDecomp.mL2_false
#print axioms OQ14.BarrierDegreeDecomp.mode_constants_nonneg
#print axioms OQ14.BarrierDegreeDecomp.mode_constants_summable
#print axioms OQ14.BarrierDegreeDecomp.R1pair_max_le
#print axioms OQ14.BarrierDegreeDecomp.R1pair_pos
#print axioms OQ14.BarrierDegreeDecomp.R1pair_rate
#print axioms OQ14.BarrierDegreeDecomp.radius_ge_R1pair
#print axioms OQ14.BarrierDegreeDecomp.paired_mode_decomp
#print axioms OQ14.BarrierDegreeDecomp.paired_mode_series
