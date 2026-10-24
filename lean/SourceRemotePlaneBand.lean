import SourceRemotePlaneFluxTE

/-! Finite-band exterior plane flux: the transverse far-field cancellation in general form.

At a plane point `x` (`x 2 = 0`, `x ≠ 0`) write every field as a part orthogonal to `x` plus a part
parallel to `x`. The cross product of two orthogonal parts is parallel to `x`, hence has no third
component, and the product of two parallel parts is zero. Only the (radial) parallel part of one field
against the orthogonal part of the other survives. For the exact exterior formulas of the layered source
modes (TM and TE) the orthogonal part is O(1/r) and the parallel part O(1/r^2), so every finite complex
combination has plane flux density O(1/r^3). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceRemotePlaneBand
open Complex Filter OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.SourceRadiation OQ14.ModalAlgebra OQ14.SourceFarAmplitude
open scoped Topology ComplexConjugate

/-- Bilinear (non-conjugated) pairing with the real position vector. -/
def dotPos (x : Space) (v : Vector) : ℂ := (x 0 : ℂ)*v 0+(x 1 : ℂ)*v 1+(x 2 : ℂ)*v 2

theorem ne_zero_of_plane (x : Space) (hx0 : x≠0) (hx2 : x 2=0) : x 0≠0 ∨ x 1≠0 := by
  by_contra h
  push_neg at h
  apply hx0
  ext i
  fin_cases i <;> simp [h.1,h.2,hx2]

theorem dotPos_conjugate (x : Space) (v : Vector) :
    dotPos x (conjugate v)=(starRingEnd ℂ) (dotPos x v) := by
  simp [dotPos,conjugate,map_add,map_mul,Complex.conj_ofReal]

/-- Two vectors orthogonal to a nonzero plane vector have zero cross product normal component. -/
theorem tangential_cross_zero (x : Space) (hx2 : x 2=0) (hx0 : x≠0) (a b : Vector)
    (ha : dotPos x a=0) (hb : dotPos x b=0) : crossProduct a b 2=0 := by
  rw [SourceRemotePlaneFlux.cross_two]
  have ha' : (x 0 : ℂ)*a 0+(x 1 : ℂ)*a 1=0 := by simpa [dotPos,hx2] using ha
  have hb' : (x 0 : ℂ)*b 0+(x 1 : ℂ)*b 1=0 := by simpa [dotPos,hx2] using hb
  have h0 : (x 0 : ℂ)*(a 0*b 1-a 1*b 0)=0 := by linear_combination (b 1)*ha'-(a 1)*hb'
  have h1 : (x 1 : ℂ)*(a 0*b 1-a 1*b 0)=0 := by linear_combination (a 0)*hb'-(b 0)*ha'
  rcases ne_zero_of_plane x hx0 hx2 with h | h
  · exact (mul_eq_zero.mp h0).resolve_left (Complex.ofReal_ne_zero.mpr h)
  · exact (mul_eq_zero.mp h1).resolve_left (Complex.ofReal_ne_zero.mpr h)

theorem plane_normal_flux_of_tangential (x : Space) (hx2 : x 2=0) (hx0 : x≠0)
    (Et Ht Er Hr : Vector) (hEt : dotPos x Et=0) (hHt : dotPos x Ht=0)
    (e h : ℂ) (hEr : Er=e • DebyeRadialTrace.position x) (hHr : Hr=h • DebyeRadialTrace.position x) :
    crossProduct (Et+Er) (conjugate (Ht+Hr)) 2=
      crossProduct Er (conjugate Ht) 2+crossProduct Et (conjugate Hr) 2 := by
  have hz := tangential_cross_zero x hx2 hx0 Et (conjugate Ht) hEt
    (by rw [dotPos_conjugate,hHt,map_zero])
  simp only [SourceRemotePlaneFlux.cross_two,conjugate] at hz ⊢
  simp only [hEr,hHr,DebyeRadialTrace.position,Pi.add_apply,Pi.smul_apply,smul_eq_mul,map_add,map_mul,
    Complex.conj_ofReal]
  linear_combination hz

/-- `F` splits at `x` into a part orthogonal to `x` of size `K1/r` and a part parallel to `x` of size `K2/r^2`. -/
def Decomp (K1 K2 : ℝ) (F : Vector) (x : Space) : Prop :=
  ∃ Et Er : Vector, F=Et+Er ∧ dotPos x Et=0 ∧ (∃ e : ℂ, Er=e • DebyeRadialTrace.position x) ∧
    ‖Et‖ ≤ K1/‖x‖ ∧ ‖Er‖ ≤ K2/‖x‖^2

theorem decomp_zero (x : Space) : Decomp 0 0 0 x :=
  ⟨0,0,by simp,by simp [dotPos],⟨0,by simp⟩,by simp,by simp⟩

theorem decomp_smul {K1 K2 : ℝ} {F : Vector} {x : Space} (c : ℂ) (h : Decomp K1 K2 F x) :
    Decomp (‖c‖*K1) (‖c‖*K2) (c • F) x := by
  obtain ⟨Et,Er,rfl,hd,⟨e,he⟩,h1,h2⟩ := h
  refine ⟨c • Et,c • Er,smul_add c Et Er,?_,⟨c*e,by rw [he,smul_smul]⟩,?_,?_⟩
  · unfold dotPos at hd ⊢
    simp only [Pi.smul_apply,smul_eq_mul]
    linear_combination c*hd
  · rw [norm_smul]
    calc _ ≤ ‖c‖*(K1/‖x‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := by ring
  · rw [norm_smul]
    calc _ ≤ ‖c‖*(K2/‖x‖^2) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = _ := by ring

theorem decomp_add {K1 K2 L1 L2 : ℝ} {F G : Vector} {x : Space} (hF : Decomp K1 K2 F x)
    (hG : Decomp L1 L2 G x) : Decomp (K1+L1) (K2+L2) (F+G) x := by
  obtain ⟨Et,Er,rfl,hd,⟨e,he⟩,h1,h2⟩ := hF
  obtain ⟨Ft,Fr,rfl,hd',⟨f,hf⟩,h1',h2'⟩ := hG
  refine ⟨Et+Ft,Er+Fr,by abel,?_,⟨e+f,by rw [he,hf,add_smul]⟩,?_,?_⟩
  · unfold dotPos at hd hd' ⊢
    simp only [Pi.add_apply]
    linear_combination hd+hd'
  · calc _ ≤ ‖Et‖+‖Ft‖ := norm_add_le _ _
      _ ≤ K1/‖x‖+L1/‖x‖ := add_le_add h1 h1'
      _ = _ := by ring
  · calc _ ≤ ‖Er‖+‖Fr‖ := norm_add_le _ _
      _ ≤ K2/‖x‖^2+L2/‖x‖^2 := add_le_add h2 h2'
      _ = _ := by ring

theorem decomp_sum {ι : Type*} (s : Finset ι) (F : ι → Vector) (K1 K2 : ι → ℝ) (x : Space)
    (h : ∀ i ∈ s, Decomp (K1 i) (K2 i) (F i) x) :
    Decomp (∑ i ∈ s,K1 i) (∑ i ∈ s,K2 i) (∑ i ∈ s,F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using decomp_zero x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha,Finset.sum_insert ha]
    exact decomp_add (h a (Finset.mem_insert_self a s)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem flux_bound_of_decomp (x : Space) (hx2 : x 2=0) (hrpos : 0<‖x‖) (E H : Vector)
    (K1 K2 L1 L2 : ℝ) (hE : Decomp K1 K2 E x) (hH : Decomp L1 L2 H x) :
    ‖crossProduct E (conjugate H) 2‖ ≤ (2*K2*L1+2*K1*L2)/‖x‖^3 := by
  have hx0 : x≠0 := norm_pos_iff.mp hrpos
  obtain ⟨Et,Er,rfl,hEt,⟨e,hEr⟩,hE1,hE2⟩ := hE
  obtain ⟨Ht,Hr,rfl,hHt,⟨h,hHr⟩,hH1,hH2⟩ := hH
  rw [plane_normal_flux_of_tangential x hx2 hx0 Et Ht Er Hr hEt hHt e h hEr hHr]
  have b1 := SourceRemotePlaneFlux.cross_component_bound Er Ht (K2/‖x‖^2) (L1/‖x‖) hE2 hH1
  have b2 := SourceRemotePlaneFlux.cross_component_bound Et Hr (K1/‖x‖) (L2/‖x‖^2) hE1 hH2
  calc _ ≤ ‖crossProduct Er (conjugate Ht) 2‖+‖crossProduct Et (conjugate Hr) 2‖ := norm_add_le _ _
    _ ≤ 2*(K2/‖x‖^2)*(L1/‖x‖)+2*(K1/‖x‖)*(L2/‖x‖^2) := add_le_add b1 b2
    _ = _ := by
      have h : ‖x‖≠0 := hrpos.ne'
      field_simp
      ring

/-! ### The exterior fields of one layered mode -/

theorem pol_dot (P : Poly) (x : Space) : dotPos x (HarmonicRadiationFactors.poloidal P x)=0 := by
  simp only [dotPos,HarmonicRadiationFactors.poloidal,DebyeRadialTrace.position,SourceRemotePlaneFlux.cross_zero,
    SourceRemotePlaneFlux.cross_one,SourceRemotePlaneFlux.cross_two]
  ring

theorem tor_dot (P : Poly) (x : Space) : dotPos x (DebyeRadialTrace.angularToroidal P x)=0 :=
  SourceRemotePlaneFlux.toroidal_dot P x

theorem radial_eq_smul (P : Poly) (x : Space) :
    HarmonicRadiationFactors.radial P x=complexEvaluate P x • DebyeRadialTrace.position x := by
  ext i
  simp only [HarmonicRadiationFactors.radial,DebyeRadialTrace.position,Pi.smul_apply,smul_eq_mul]
  ring

theorem electric_eq_weighted (d : Data) (P : Poly) (x : Space) (hx : d.X<‖x‖) :
    SourceUnclippedMaxwell.electric d P x=
      (Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹) • electricWeighted d P x := by
  have hr : 0<‖x‖ := (d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hx
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have he : Complex.exp (I*(‖x‖ : ℂ))*Complex.exp (-I*(‖x‖ : ℂ))=1 := by
    rw [← Complex.exp_add]; simp
  have hun : Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹*(Complex.exp (-I*(‖x‖ : ℂ))*(‖x‖ : ℂ))=1 := by
    calc _ = (Complex.exp (I*(‖x‖ : ℂ))*Complex.exp (-I*(‖x‖ : ℂ)))*((‖x‖ : ℂ)⁻¹*(‖x‖ : ℂ)) := by ring
      _ = 1 := by rw [he,inv_mul_cancel₀ hr0,one_mul]
  unfold electricWeighted
  rw [smul_smul,hun,one_smul]

theorem magnetic_eq_weighted (d : Data) (P : Poly) (x : Space) (hx : d.X<‖x‖) :
    SourceUnclippedMaxwell.magnetic d P x=
      (Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹) • magneticWeighted d P x := by
  have hr : 0<‖x‖ := (d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hx
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have he : Complex.exp (I*(‖x‖ : ℂ))*Complex.exp (-I*(‖x‖ : ℂ))=1 := by
    rw [← Complex.exp_add]; simp
  have hun : Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹*(Complex.exp (-I*(‖x‖ : ℂ))*(‖x‖ : ℂ))=1 := by
    calc _ = (Complex.exp (I*(‖x‖ : ℂ))*Complex.exp (-I*(‖x‖ : ℂ)))*((‖x‖ : ℂ)⁻¹*(‖x‖ : ℂ)) := by ring
      _ = 1 := by rw [he,inv_mul_cancel₀ hr0,one_mul]
  unfold magneticWeighted
  rw [smul_smul,hun,one_smul]

theorem exp_norm (r : ℝ) (hr : 0<r) :
    ‖Complex.exp (I*(r : ℂ))*(r : ℂ)⁻¹‖=r⁻¹ := by
  have he : ‖Complex.exp (I*(r : ℂ))‖=1 := by
    rw [Complex.norm_exp]; simp
  rw [norm_mul,he,one_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]

theorem tm_decomp (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    ∃ r0 K1 K2 L1 : ℝ, 0<r0 ∧ d.X<r0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ L1 ∧ ∀ x : Space, r0 ≤ ‖x‖ →
      Decomp K1 K2 (SourceUnclippedMaxwell.electric d P x) x ∧
        Decomp L1 0 (SourceUnclippedMaxwell.magnetic d P x) x := by
  obtain ⟨M0,hM0,h0⟩ := HarmonicRadiationFactors.poloidal_bound P d.l hp
  obtain ⟨M1,hM1,h1⟩ := HarmonicRadiationFactors.radial_bound P d.l hp
  obtain ⟨M2,hM2,h2⟩ := HarmonicRadiationGeometry.normalized_toroidal_bound P d.l hp
  have hpol : Tendsto (fun r : ℝ => p d.l r) atTop (𝓝 1) := by
    simpa only [one_mul] using RadialRellich.hankelPoly_radial_limit d.l 1 (by norm_num) I
  have hpd : Tendsto (fun r : ℝ => pD d.l r) atTop (𝓝 0) := HankelEnergy.hankelPolyD_tendsto d.l I
  obtain ⟨r1,hr1⟩ := eventually_atTop.mp (hpol.norm.eventually (gt_mem_nhds (by norm_num : ‖(1 : ℂ)‖<2)))
  obtain ⟨r2,hr2⟩ := eventually_atTop.mp (hpd.norm.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖<1)))
  have hL : 0 ≤ (d.l : ℝ)*(d.l+1) := by positivity
  refine ⟨max (max r1 r2) (max 1 (d.X+1)),3*‖amplitude d‖*M0,2*‖amplitude d‖*((d.l : ℝ)*(d.l+1))*M1,
    2*‖amplitude d‖*M2,lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_right _ _)),
    lt_of_lt_of_le (by linarith) ((le_max_right _ _).trans (le_max_right _ _)),by positivity,by positivity,
    by positivity,?_⟩
  intro x hx
  have hX : d.X<‖x‖ := lt_of_lt_of_le (by linarith) (((le_max_right _ _).trans (le_max_right _ _)).trans hx)
  have hrpos : 0<‖x‖ := (d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hX
  have hx0 : x≠0 := norm_pos_iff.mp hrpos
  have hp1 : ‖p d.l ‖x‖‖ ≤ 2 := (hr1 _ (((le_max_left _ _).trans (le_max_left _ _)).trans hx)).le
  have hp2 : ‖pD d.l ‖x‖‖ ≤ 1 := (hr2 _ (((le_max_right _ _).trans (le_max_left _ _)).trans hx)).le
  have hcn := exp_norm ‖x‖ hrpos
  have hphase : ‖phase d.l‖=1 := by simp [SourceRadiation.phase]
  have hA : ‖amplitude d*phase d.l*(I*p d.l ‖x‖+pD d.l ‖x‖)‖ ≤ 3*‖amplitude d‖ := by
    rw [norm_mul,norm_mul,hphase,mul_one]
    have : ‖I*p d.l ‖x‖+pD d.l ‖x‖‖ ≤ 3 := by
      calc _ ≤ ‖I*p d.l ‖x‖‖+‖pD d.l ‖x‖‖ := norm_add_le _ _
        _ ≤ 3 := by rw [norm_mul,Complex.norm_I,one_mul]; linarith
    have h3 := mul_le_mul_of_nonneg_left this (norm_nonneg (amplitude d))
    linarith
  have hB : ‖amplitude d*phase d.l*((d.l : ℂ)*(d.l+1))*(p d.l ‖x‖/(‖x‖ : ℂ))‖ ≤
      ‖amplitude d‖*((d.l : ℝ)*(d.l+1))*2/‖x‖ := by
    rw [norm_mul,norm_mul,norm_mul,norm_div,hphase,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hrpos]
    have hl : ‖((d.l : ℂ)*(d.l+1))‖=(d.l : ℝ)*(d.l+1) := by
      rw [show ((d.l : ℂ)*(d.l+1))=(((d.l : ℝ)*(d.l+1) : ℝ) : ℂ) by push_cast; ring,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg hL]
    rw [hl,mul_one]
    calc _ ≤ ‖amplitude d‖*((d.l : ℝ)*(d.l+1))*(2/‖x‖) := by gcongr
      _ = _ := by ring
  have hC : ‖-I*amplitude d*phase d.l*p d.l ‖x‖‖ ≤ 2*‖amplitude d‖ := by
    rw [norm_mul,norm_mul,norm_mul,norm_neg,Complex.norm_I,hphase]
    nlinarith [mul_nonneg (norm_nonneg (amplitude d)) (sub_nonneg.2 hp1)]
  constructor
  · refine ⟨(Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹*(amplitude d*phase d.l*(I*p d.l ‖x‖+pD d.l ‖x‖))) •
        ((((‖x‖ : ℂ)^(d.l+1))⁻¹) • HarmonicRadiationFactors.poloidal P x),
      (Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹*(amplitude d*phase d.l*((d.l : ℂ)*(d.l+1))*(p d.l ‖x‖/(‖x‖ : ℂ)))) •
        ((((‖x‖ : ℂ)^(d.l+1))⁻¹) • HarmonicRadiationFactors.radial P x),?_,?_,?_,?_,?_⟩
    · rw [electric_eq_weighted d P x hX,electric_exterior d P hp x hX]
      simp only [smul_add,smul_smul,mul_assoc]
    · unfold dotPos
      simp only [Pi.smul_apply,smul_eq_mul]
      have := pol_dot P x
      unfold dotPos at this
      linear_combination
        (Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹*(amplitude d*phase d.l*(I*p d.l ‖x‖+pD d.l ‖x‖)))*
          (((‖x‖ : ℂ)^(d.l+1))⁻¹)*this
    · refine ⟨(Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹*(amplitude d*phase d.l*((d.l : ℂ)*(d.l+1))*
        (p d.l ‖x‖/(‖x‖ : ℂ))))*(((‖x‖ : ℂ)^(d.l+1))⁻¹*complexEvaluate P x),?_⟩
      rw [radial_eq_smul]
      simp only [smul_smul,mul_assoc]
    · rw [norm_smul,norm_mul,hcn]
      have hb0 := h0 x hx0
      calc _ ≤ ‖x‖⁻¹*(3*‖amplitude d‖)*M0 := by gcongr
        _ = _ := by ring
    · rw [norm_smul,norm_mul,hcn]
      have hb1 := h1 x hx0
      calc _ ≤ ‖x‖⁻¹*(‖amplitude d‖*((d.l : ℝ)*(d.l+1))*2/‖x‖)*M1 := by gcongr
        _ = _ := by ring
  · refine ⟨(Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹*(-I*amplitude d*phase d.l*p d.l ‖x‖)) •
        ((((‖x‖ : ℂ)^d.l)⁻¹) • DebyeRadialTrace.angularToroidal P x),0,?_,?_,⟨0,by simp⟩,?_,by simp⟩
    · rw [magnetic_eq_weighted d P x hX,magnetic_exterior d P x hX,smul_smul,add_zero]
    · unfold dotPos
      simp only [Pi.smul_apply,smul_eq_mul]
      have := tor_dot P x
      unfold dotPos at this
      linear_combination
        (Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹*(-I*amplitude d*phase d.l*p d.l ‖x‖))*
          (((‖x‖ : ℂ)^d.l)⁻¹)*this
    · rw [norm_smul,norm_mul,hcn]
      have hb2 := h2 x hx0
      calc _ ≤ ‖x‖⁻¹*(2*‖amplitude d‖)*M2 := by gcongr
        _ = _ := by ring

/-! ### Mixed TM/TE finite bands -/

/-- Electric field of a TM (`tm = true`) or TE (`tm = false`) layered source mode. -/
def modeElectric (tm : Bool) (d : Data) (P : Poly) (x : Space) : Vector :=
  if tm then SourceUnclippedMaxwell.electric d P x else SourceGeneralMaxwell.teElectric d P x

def modeMagnetic (tm : Bool) (d : Data) (P : Poly) (x : Space) : Vector :=
  if tm then SourceUnclippedMaxwell.magnetic d P x else SourceGeneralMaxwell.teMagnetic d P x

theorem mode_decomp (tm : Bool) (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    ∃ r0 K1 K2 L1 L2 : ℝ, 0<r0 ∧ d.X<r0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ L1 ∧ 0 ≤ L2 ∧
      ∀ x : Space, r0 ≤ ‖x‖ →
        Decomp K1 K2 (modeElectric tm d P x) x ∧ Decomp L1 L2 (modeMagnetic tm d P x) x := by
  obtain ⟨r0,K1,K2,L1,hr0,hX,hK1,hK2,hL1,h⟩ := tm_decomp d P hp
  cases tm
  · refine ⟨r0,L1,0,‖(-1 : ℂ)‖*K1,‖(-1 : ℂ)‖*K2,hr0,hX,hL1,le_rfl,by positivity,by positivity,?_⟩
    intro x hx
    obtain ⟨hE,hH⟩ := h x hx
    have : SourceGeneralMaxwell.teMagnetic d P x=(-1 : ℂ) • SourceUnclippedMaxwell.electric d P x := by
      funext i
      simp [SourceGeneralMaxwell.teMagnetic]
    simp only [modeElectric,modeMagnetic,Bool.false_eq_true,if_false,SourceGeneralMaxwell.teElectric,this]
    exact ⟨hH,decomp_smul (-1) hE⟩
  · refine ⟨r0,K1,K2,L1,0,hr0,hX,hK1,hK2,hL1,le_rfl,?_⟩
    intro x hx
    simpa only [modeElectric,modeMagnetic,if_true] using h x hx

theorem band_plane_flux_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (tmE : ι → Bool) (dE : ι → Data) (PE : ι → Poly) (hE : ∀ i, (PE i).IsHomogeneous (dE i).l) (cE : ι → ℂ)
    (tmH : κ → Bool) (dH : κ → Data) (PH : κ → Poly) (hH : ∀ j, (PH j).IsHomogeneous (dH j).l) (cH : κ → ℂ) :
    ∃ r0 C : ℝ, 0<r0 ∧ 0 ≤ C ∧ (∀ i, (dE i).X<r0) ∧ (∀ j, (dH j).X<r0) ∧ ∀ x : Space, x 2=0 → r0 ≤ ‖x‖ →
      ‖crossProduct (∑ i, cE i • modeElectric (tmE i) (dE i) (PE i) x)
        (conjugate (∑ j, cH j • modeMagnetic (tmH j) (dH j) (PH j) x)) 2‖ ≤ C/‖x‖^3 := by
  choose r0 K1 K2 L1 L2 hr0 hX hK1 hK2 hL1 hL2 hdec using
    fun i => mode_decomp (tmE i) (dE i) (PE i) (hE i)
  choose s0 M1 M2 N1 N2 hs0 hsX hM1 hM2 hN1 hN2 hdec' using
    fun j => mode_decomp (tmH j) (dH j) (PH j) (hH j)
  obtain ⟨R1,hR1⟩ := (Set.finite_range r0).bddAbove
  obtain ⟨R2,hR2⟩ := (Set.finite_range s0).bddAbove
  have hR1' : ∀ i, r0 i ≤ R1 := fun i => hR1 (Set.mem_range_self i)
  have hR2' : ∀ j, s0 j ≤ R2 := fun j => hR2 (Set.mem_range_self j)
  have hR : 0<max (max R1 R2) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max (max R1 R2) 1+1,
    2*(∑ i, ‖cE i‖*K2 i)*(∑ j, ‖cH j‖*N1 j)+2*(∑ i, ‖cE i‖*K1 i)*(∑ j, ‖cH j‖*N2 j),by linarith,?_,?_,?_,?_⟩
  · have h1 : 0 ≤ ∑ i, ‖cE i‖*K2 i := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hK2 i))
    have h2 : 0 ≤ ∑ j, ‖cH j‖*N1 j := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hN1 j))
    have h3 : 0 ≤ ∑ i, ‖cE i‖*K1 i := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hK1 i))
    have h4 : 0 ≤ ∑ j, ‖cH j‖*N2 j := Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (hN2 j))
    positivity
  · intro i
    exact lt_of_lt_of_le (hX i) ((hR1' i).trans (by linarith [le_max_left (max R1 R2) 1,le_max_left R1 R2]))
  · intro j
    exact lt_of_lt_of_le (hsX j) ((hR2' j).trans (by linarith [le_max_left (max R1 R2) 1,le_max_right R1 R2]))
  · intro x hx2 hx
    have hxr : max (max R1 R2) 1+1 ≤ ‖x‖ := hx
    have hrpos : 0<‖x‖ := by linarith
    have hDE : Decomp (∑ i, ‖cE i‖*K1 i) (∑ i, ‖cE i‖*K2 i)
        (∑ i, cE i • modeElectric (tmE i) (dE i) (PE i) x) x := by
      apply decomp_sum Finset.univ (fun i => cE i • modeElectric (tmE i) (dE i) (PE i) x)
        (fun i => ‖cE i‖*K1 i) (fun i => ‖cE i‖*K2 i) x
      intro i _
      apply decomp_smul
      exact (hdec i x (by linarith [hR1' i,le_max_left (max R1 R2) 1,le_max_left R1 R2])).1
    have hDH : Decomp (∑ j, ‖cH j‖*N1 j) (∑ j, ‖cH j‖*N2 j)
        (∑ j, cH j • modeMagnetic (tmH j) (dH j) (PH j) x) x := by
      apply decomp_sum Finset.univ (fun j => cH j • modeMagnetic (tmH j) (dH j) (PH j) x)
        (fun j => ‖cH j‖*N1 j) (fun j => ‖cH j‖*N2 j) x
      intro j _
      apply decomp_smul
      exact (hdec' j x (by linarith [hR2' j,le_max_left (max R1 R2) 1,le_max_right R1 R2])).2
    exact flux_bound_of_decomp x hx2 hrpos _ _ _ _ _ _ hDE hDH

end OQ14.SourceRemotePlaneBand
#print axioms OQ14.SourceRemotePlaneBand.ne_zero_of_plane
#print axioms OQ14.SourceRemotePlaneBand.dotPos_conjugate
#print axioms OQ14.SourceRemotePlaneBand.tangential_cross_zero
#print axioms OQ14.SourceRemotePlaneBand.plane_normal_flux_of_tangential
#print axioms OQ14.SourceRemotePlaneBand.decomp_zero
#print axioms OQ14.SourceRemotePlaneBand.decomp_smul
#print axioms OQ14.SourceRemotePlaneBand.decomp_add
#print axioms OQ14.SourceRemotePlaneBand.decomp_sum
#print axioms OQ14.SourceRemotePlaneBand.flux_bound_of_decomp
#print axioms OQ14.SourceRemotePlaneBand.pol_dot
#print axioms OQ14.SourceRemotePlaneBand.tor_dot
#print axioms OQ14.SourceRemotePlaneBand.radial_eq_smul
#print axioms OQ14.SourceRemotePlaneBand.electric_eq_weighted
#print axioms OQ14.SourceRemotePlaneBand.magnetic_eq_weighted
#print axioms OQ14.SourceRemotePlaneBand.exp_norm
#print axioms OQ14.SourceRemotePlaneBand.tm_decomp
#print axioms OQ14.SourceRemotePlaneBand.mode_decomp
#print axioms OQ14.SourceRemotePlaneBand.band_plane_flux_bound
