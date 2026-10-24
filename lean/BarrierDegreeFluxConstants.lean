import SourceRemotePlaneBand
import AngularExteriorBounds
import BarrierAnnulusStateBounds

/-! Degree-explicit plane-flux constants of one layered TM source mode, valid at every nonzero point
(annulus and exterior alike), in terms of the actual radial state `raw d ‖x‖ = (u, p)` and the
all-degree angular envelopes. In the barrier range the state bounds of `BarrierSourceStateBounds` and
`BarrierAnnulusStateBounds` turn this into a geometric decay in the degree for modes normalized by
the regular value at an inner scale. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.BarrierDegreeFluxConstants
open Complex Filter OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.SourceRemotePlaneBand OQ14.SphereHarmonicBasis OQ14.AngularExteriorBounds
open scoped Topology ComplexConjugate

/-- The direction of a nonzero vector as a point of the unit sphere. -/
def rayPoint (x : Space) (hx : x≠0) : Sphere :=
  ⟨‖x‖⁻¹ • x,by
    have hr : 0<‖x‖ := norm_pos_iff.mpr hx
    simp [mem_sphere_zero_iff_norm,norm_smul,abs_of_pos hr,hr.ne']⟩

theorem rayPoint_smul (x : Space) (hx : x≠0) : ‖x‖ • (rayPoint x hx : Space)=x := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  simp [rayPoint,smul_smul,mul_inv_cancel₀ hr.ne']

theorem ray_bound (F : Field) (k : ℕ) (hh : ∀ (r : ℝ) (x : Space),F (r • x)=(r : ℂ)^k • F x)
    (M : ℝ) (hM : ∀ n : Sphere,‖F n‖ ≤ M) (x : Space) (hx : x≠0) : ‖F x‖ ≤ ‖x‖^k*M := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have h := hh ‖x‖ (rayPoint x hx)
  rw [rayPoint_smul x hx] at h
  rw [h,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  exact mul_le_mul_of_nonneg_left (hM _) (by positivity)

theorem eval_ray_bound (P : Poly) (k : ℕ) (hp : P.IsHomogeneous k) (M : ℝ)
    (hM : ∀ n : Sphere,‖complexEvaluate P n‖ ≤ M) (x : Space) (hx : x≠0) :
    ‖complexEvaluate P x‖ ≤ ‖x‖^k*M := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have h := FischerDecomposition.complexEvaluate_smul P k hp ‖x‖ (rayPoint x hx)
  rw [rayPoint_smul x hx] at h
  rw [h,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  exact mul_le_mul_of_nonneg_left (hM _) (by positivity)

theorem position_norm_le (x : Space) : ‖DebyeRadialTrace.position x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  simpa only [DebyeRadialTrace.position,Complex.norm_real] using PiLp.norm_apply_le x i

theorem inverseSigma_norm_le (d : Data) (hσ : ∀ g ∈ d.gs,1 ≤ g.σ) (r : ℝ) :
    ‖inverseSigma d r‖ ≤ 1 := by
  have hsel : ∀ (gs : List OQ14.RadialStack.Layer),(∀ g ∈ gs,1 ≤ g.σ) → ∀ r : ℝ,
      ‖OQ14.ClippedLayerProfiles.inverseSigma gs r‖ ≤ 1 := by
    intro gs
    induction gs with
    | nil =>
      intro _ r
      simp [OQ14.ClippedLayerProfiles.inverseSigma,OQ14.ClippedLayerProfiles.select]
    | cons g gs ih =>
      intro h r
      unfold OQ14.ClippedLayerProfiles.inverseSigma OQ14.ClippedLayerProfiles.select
      by_cases hg : g.a<r
      · rw [if_pos hg]
        have : 1 ≤ g.σ := h g List.mem_cons_self
        rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
        exact inv_le_one_of_one_le₀ this
      · rw [if_neg hg]
        exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) r
  unfold inverseSigma SourceRadialSystem.extend
  split_ifs
  · simp
  · exact hsel d.gs hσ r
  · simp

/-- Generic-radius form of the TM mode fields: orthogonal and radial parts of the electric field and the
purely orthogonal magnetic field. -/
theorem electric_split (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) (x : Space) (hx : x≠0) :
    SourceUnclippedMaxwell.electric d P x=
      (((raw d ‖x‖).2/(‖x‖ : ℂ)^(d.l+2)) • HarmonicRadiationFactors.poloidal P x)+
      ((inverseSigma d ‖x‖*((d.l : ℂ)*(d.l+1)*(raw d ‖x‖).1/(‖x‖ : ℂ)^(d.l+3))*complexEvaluate P x) •
        DebyeRadialTrace.position x) := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  ext i
  simp only [SourceUnclippedMaxwell.electric,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    HarmonicRadiationFactors.poloidal_formula P d.l hp x i,HarmonicRadiationFactors.radial,
    DebyeRadialTrace.position]
  field_simp
  ring

theorem magnetic_eq (d : Data) (P : Poly) (x : Space) :
    SourceUnclippedMaxwell.magnetic d P x=
      ((-I*(raw d ‖x‖).1/(‖x‖ : ℂ)^(d.l+1)) • DebyeRadialTrace.angularToroidal P x) := by
  ext i
  simp only [SourceUnclippedMaxwell.magnetic,Pi.smul_apply,smul_eq_mul]
  ring

/-- Explicit decomposition constants of one TM mode at any nonzero point, in terms of the state magnitudes
there. -/
theorem tm_decomp_state (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) (Mpol Mp Mt : ℝ)
    (hMpol : ∀ n : Sphere,‖HarmonicRadiationFactors.poloidal P n‖ ≤ Mpol)
    (hMp : ∀ n : Sphere,‖complexEvaluate P n‖ ≤ Mp)
    (hMt : ∀ n : Sphere,‖DebyeRadialTrace.angularToroidal P n‖ ≤ Mt)
    (hσ : ∀ g ∈ d.gs,1 ≤ g.σ) (x : Space) (hx : x≠0) :
    Decomp (‖(raw d ‖x‖).2‖*Mpol) (((d.l : ℝ)*(d.l+1))*‖(raw d ‖x‖).1‖*Mp)
      (SourceUnclippedMaxwell.electric d P x) x ∧
    Decomp (‖(raw d ‖x‖).1‖*Mt) 0 (SourceUnclippedMaxwell.magnetic d P x) x := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hrk : ∀ k : ℕ,0<‖x‖^k := fun k => pow_pos hr k
  have hL : 0 ≤ (d.l : ℝ)*(d.l+1) := by positivity
  constructor
  · refine ⟨((raw d ‖x‖).2/(‖x‖ : ℂ)^(d.l+2)) • HarmonicRadiationFactors.poloidal P x,
      (inverseSigma d ‖x‖*((d.l : ℂ)*(d.l+1)*(raw d ‖x‖).1/(‖x‖ : ℂ)^(d.l+3))*complexEvaluate P x) •
        DebyeRadialTrace.position x,electric_split d P hp x hx,?_,⟨_,rfl⟩,?_,?_⟩
    · unfold dotPos
      simp only [Pi.smul_apply,smul_eq_mul]
      have := pol_dot P x
      unfold dotPos at this
      linear_combination ((raw d ‖x‖).2/(‖x‖ : ℂ)^(d.l+2))*this
    · have hpol : ‖HarmonicRadiationFactors.poloidal P x‖ ≤ ‖x‖^(d.l+1)*Mpol :=
        ray_bound (HarmonicRadiationFactors.poloidal P) (d.l+1)
          (HarmonicRadiationFactors.poloidal_smul P d.l hp) Mpol hMpol x hx
      rw [norm_smul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
      calc ‖(raw d ‖x‖).2‖/‖x‖^(d.l+2)*‖HarmonicRadiationFactors.poloidal P x‖
          ≤ ‖(raw d ‖x‖).2‖/‖x‖^(d.l+2)*(‖x‖^(d.l+1)*Mpol) :=
            mul_le_mul_of_nonneg_left hpol (div_nonneg (norm_nonneg _) (hrk _).le)
        _ =‖(raw d ‖x‖).2‖*Mpol/‖x‖ := by
          field_simp
          ring
    · have hev := eval_ray_bound P d.l hp Mp hMp x hx
      have hinv := inverseSigma_norm_le d hσ ‖x‖
      rw [norm_smul]
      have hnum : ‖inverseSigma d ‖x‖*((d.l : ℂ)*(d.l+1)*(raw d ‖x‖).1/(‖x‖ : ℂ)^(d.l+3))*
          complexEvaluate P x‖ ≤ ((d.l : ℝ)*(d.l+1))*‖(raw d ‖x‖).1‖*Mp/‖x‖^3 := by
        have hl : ‖((d.l : ℂ)*(d.l+1))‖=(d.l : ℝ)*(d.l+1) := by
          rw [show ((d.l : ℂ)*(d.l+1))=(((d.l : ℝ)*(d.l+1) : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL]
        have hu : ‖((d.l : ℂ)*(d.l+1)*(raw d ‖x‖).1)‖=((d.l : ℝ)*(d.l+1))*‖(raw d ‖x‖).1‖ := by
          rw [norm_mul,hl]
        have hden : ‖(‖x‖ : ℂ)^(d.l+3)‖=‖x‖^(d.l+3) := by
          rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
        rw [norm_mul,norm_mul,norm_div,hu,hden]
        have hMp0 : 0 ≤ Mp := (norm_nonneg _).trans (hMp (rayPoint x hx))
        calc ‖inverseSigma d ‖x‖‖*(((d.l : ℝ)*(d.l+1))*‖(raw d ‖x‖).1‖/‖x‖^(d.l+3))*‖complexEvaluate P x‖
            ≤ 1*(((d.l : ℝ)*(d.l+1))*‖(raw d ‖x‖).1‖/‖x‖^(d.l+3))*(‖x‖^d.l*Mp) := by
              gcongr
          _ =((d.l : ℝ)*(d.l+1))*‖(raw d ‖x‖).1‖*Mp/‖x‖^3 := by
              field_simp
              ring
      calc ‖inverseSigma d ‖x‖*((d.l : ℂ)*(d.l+1)*(raw d ‖x‖).1/(‖x‖ : ℂ)^(d.l+3))*
            complexEvaluate P x‖*‖DebyeRadialTrace.position x‖
          ≤ (((d.l : ℝ)*(d.l+1))*‖(raw d ‖x‖).1‖*Mp/‖x‖^3)*‖x‖ :=
            mul_le_mul hnum (position_norm_le x) (norm_nonneg _) (by
              have hMp0 : 0 ≤ Mp := (norm_nonneg _).trans (hMp (rayPoint x hx))
              positivity)
        _ =((d.l : ℝ)*(d.l+1))*‖(raw d ‖x‖).1‖*Mp/‖x‖^2 := by
          field_simp
          ring
  · refine ⟨(-I*(raw d ‖x‖).1/(‖x‖ : ℂ)^(d.l+1)) • DebyeRadialTrace.angularToroidal P x,0,?_,?_,
      ⟨0,by simp⟩,?_,by simp⟩
    · rw [magnetic_eq,add_zero]
    · unfold dotPos
      simp only [Pi.smul_apply,smul_eq_mul]
      have := tor_dot P x
      unfold dotPos at this
      linear_combination (-I*(raw d ‖x‖).1/(‖x‖ : ℂ)^(d.l+1))*this
    · have htor : ‖DebyeRadialTrace.angularToroidal P x‖ ≤ ‖x‖^d.l*Mt :=
        ray_bound (DebyeRadialTrace.angularToroidal P) d.l
          (HarmonicRadiationGeometry.angularToroidal_smul P d.l hp) Mt hMt x hx
      rw [norm_smul,norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,norm_pow,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos hr]
      calc ‖(raw d ‖x‖).1‖/‖x‖^(d.l+1)*‖DebyeRadialTrace.angularToroidal P x‖
          ≤ ‖(raw d ‖x‖).1‖/‖x‖^(d.l+1)*(‖x‖^d.l*Mt) :=
            mul_le_mul_of_nonneg_left htor (div_nonneg (norm_nonneg _) (hrk _).le)
        _ =‖(raw d ‖x‖).1‖*Mt/‖x‖ := by
          field_simp
          ring

/-- Plane flux density of one TM mode at any nonzero plane point, with explicit constants. -/
theorem plane_flux_density_state (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) (Mpol Mp Mt : ℝ)
    (hMpol : ∀ n : Sphere,‖HarmonicRadiationFactors.poloidal P n‖ ≤ Mpol)
    (hMp : ∀ n : Sphere,‖complexEvaluate P n‖ ≤ Mp)
    (hMt : ∀ n : Sphere,‖DebyeRadialTrace.angularToroidal P n‖ ≤ Mt)
    (hσ : ∀ g ∈ d.gs,1 ≤ g.σ) (x : Space) (hx2 : x 2=0) (hx : x≠0) :
    ‖crossProduct (SourceUnclippedMaxwell.electric d P x)
      (conjugate (SourceUnclippedMaxwell.magnetic d P x)) 2‖ ≤
      2*(((d.l : ℝ)*(d.l+1))*Mp*Mt)*‖(raw d ‖x‖).1‖^2/‖x‖^3 := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨hE,hH⟩ := tm_decomp_state d P hp Mpol Mp Mt hMpol hMp hMt hσ x hx
  have h := flux_bound_of_decomp x hx2 hr _ _ _ _ _ _ hE hH
  refine h.trans (le_of_eq ?_)
  ring

/-- All-degree envelope form for the normalized harmonic `representative d.l m`. -/
theorem degree_flux_bound (d : Data) (m : Index d.l) (hσ : ∀ g ∈ d.gs,1 ≤ g.σ) (x : Space)
    (hx2 : x 2=0) (hx : x≠0) :
    ‖crossProduct (SourceUnclippedMaxwell.electric d (representative d.l m) x)
      (conjugate (SourceUnclippedMaxwell.magnetic d (representative d.l m) x)) 2‖ ≤
      4*((d.l : ℝ)*(d.l+1))*(envelope d.l)^2*‖(raw d ‖x‖).1‖^2/‖x‖^3 := by
  have he := envelope_nonnegative d.l
  have h := plane_flux_density_state d (representative d.l m) (representative_homogeneous d.l m)
    ((d.l+1 : ℝ)*envelope d.l) (envelope d.l) (2*envelope d.l)
    (fun n => (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => poloidal_bound d.l m n i))
    (fun n => scalar_value_bound d.l m n)
    (fun n => (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => toroidal_bound d.l m n i))
    hσ x hx2 hx
  refine h.trans (le_of_eq ?_)
  ring

theorem decomp_mono {K1 K2 K1' K2' : ℝ} {F : Vector} {x : Space} (hx : x≠0) (h : Decomp K1 K2 F x)
    (h1 : K1 ≤ K1') (h2 : K2 ≤ K2') : Decomp K1' K2' F x := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨Et,Er,hF,hd,he,b1,b2⟩ := h
  refine ⟨Et,Er,hF,hd,he,b1.trans (by gcongr),b2.trans (by gcongr)⟩

/-! ### Barrier range: geometric decay in the degree for modes normalized by `regular l s` -/

/-- Diagonal flux constant of the barrier range for the mode normalized by `regular l s`. -/
def barrierConstant (R s : ℝ) (l : ℕ) : ℝ := 16*R^2*Real.exp R*(envelope l)^2*(s/R)^(2*(l+1))

/-- First-order (amplitude) constant of the barrier range. -/
def barrierAmplitude (R s : ℝ) (l : ℕ) : ℝ := 2*R*Real.exp (R/2)*envelope l*(s/R)^(l+1)

theorem barrierConstant_eq (R s : ℝ) (l : ℕ) :
    barrierConstant R s l=4*(barrierAmplitude R s l)^2 := by
  unfold barrierConstant barrierAmplitude
  have : Real.exp R=Real.exp (R/2)^2 := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [this]
  ring

/-- Barrier range: the diagonal plane flux density of the mode normalized by `regular l s` has the
explicit constant `barrierConstant`, at every plane point at distance at least the inner radius. -/
theorem degree_flux_barrier (d : Data) (m : Index d.l) (hσ : ∀ g ∈ d.gs,1 ≤ g.σ) (q : ℝ) (hq : 1 ≤ q)
    (hX : d.X ≤ 2*d.R) (hparams : ∀ g ∈ d.gs,g.q ≤ q) (hl : 2*q*d.R ≤ d.l) (s : ℝ) (hs : 0<s)
    (hsR : s ≤ d.R) (x : Space) (hx2 : x 2=0) (hxR : d.R ≤ ‖x‖) :
    (OQ14.HankelRealBasis.regular d.l s)^2*
      ‖crossProduct (SourceUnclippedMaxwell.electric d (representative d.l m) x)
        (conjugate (SourceUnclippedMaxwell.magnetic d (representative d.l m) x)) 2‖ ≤
      barrierConstant d.R s d.l/‖x‖^3 := by
  have hR := d.hR
  have hrpos : 0<‖x‖ := hR.trans_le hxR
  have hx0 : x≠0 := norm_pos_iff.mp hrpos
  have hflux := degree_flux_bound d m hσ x hx2 hx0
  have hw := (OQ14.BarrierAnnulusStateBounds.source_weighted_all_high d.l d.chain hR q hq hX hparams
    hl s hs hsR ‖x‖ hxR).1
  have hreg0 : 0 ≤ OQ14.HankelRealBasis.regular d.l s := by
    have hl2 : 2*d.R ≤ (d.l : ℝ) := by nlinarith
    have hν := OQ14.RadialHighOrderBound.high_order_barrier d.l d.R hR hl2
    have hA := OQ14.RiccatiSeriesCoefficients.amplitude_pos d.l 0
    have := OQ14.RiccatiGaussianBound.regular_gaussian_lower d.l d.R hR hν s ⟨hs,hsR⟩
    exact le_trans (by positivity) this
  set U := ‖(raw d ‖x‖).1‖ with hU
  have hw' : OQ14.HankelRealBasis.regular d.l s*U ≤
      2*d.R*Real.exp (d.R/2)/((d.l : ℝ)+1)*(s/d.R)^(d.l+1) := hw
  have hl1 : (0 : ℝ)<(d.l : ℝ)+1 := by positivity
  have hsq : (OQ14.HankelRealBasis.regular d.l s*U)^2 ≤
      (2*d.R*Real.exp (d.R/2)/((d.l : ℝ)+1)*(s/d.R)^(d.l+1))^2 :=
    pow_le_pow_left₀ (mul_nonneg hreg0 (norm_nonneg _)) hw' 2
  have hr3 : 0<‖x‖^3 := by positivity
  have he := envelope_nonnegative d.l
  calc (OQ14.HankelRealBasis.regular d.l s)^2*‖crossProduct _ _ 2‖
      ≤ (OQ14.HankelRealBasis.regular d.l s)^2*(4*((d.l : ℝ)*(d.l+1))*(envelope d.l)^2*U^2/‖x‖^3) :=
        mul_le_mul_of_nonneg_left hflux (sq_nonneg _)
    _ =4*((d.l : ℝ)*(d.l+1))*(envelope d.l)^2*(OQ14.HankelRealBasis.regular d.l s*U)^2/‖x‖^3 := by ring
    _ ≤ 4*((d.l : ℝ)*(d.l+1))*(envelope d.l)^2*
          (2*d.R*Real.exp (d.R/2)/((d.l : ℝ)+1)*(s/d.R)^(d.l+1))^2/‖x‖^3 := by gcongr
    _ ≤ barrierConstant d.R s d.l/‖x‖^3 := by
        unfold barrierConstant
        apply div_le_div_of_nonneg_right _ hr3.le
        have hE : Real.exp d.R=Real.exp (d.R/2)^2 := by rw [← Real.exp_nat_mul]; congr 1; ring
        have hl0 : (d.l : ℝ) ≤ (d.l : ℝ)+1 := by linarith
        have hfrac : (d.l : ℝ)*(d.l+1)/((d.l : ℝ)+1)^2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith [(Nat.cast_nonneg d.l : (0 : ℝ) ≤ d.l)]
        have hpow : (s/d.R)^(2*(d.l+1))=((s/d.R)^(d.l+1))^2 := by rw [← pow_mul]; ring_nf
        rw [hE,hpow]
        have hbase : 4*((d.l : ℝ)*(d.l+1))*(envelope d.l)^2*
            (2*d.R*Real.exp (d.R/2)/((d.l : ℝ)+1)*(s/d.R)^(d.l+1))^2 =
            16*d.R^2*Real.exp (d.R/2)^2*(envelope d.l)^2*((s/d.R)^(d.l+1))^2*
              ((d.l : ℝ)*(d.l+1)/((d.l : ℝ)+1)^2) := by
          field_simp
          ring
        rw [hbase]
        have hpos : 0 ≤ 16*d.R^2*Real.exp (d.R/2)^2*(envelope d.l)^2*((s/d.R)^(d.l+1))^2 := by positivity
        calc _ ≤ 16*d.R^2*Real.exp (d.R/2)^2*(envelope d.l)^2*((s/d.R)^(d.l+1))^2*1 :=
              mul_le_mul_of_nonneg_left hfrac hpos
          _ = _ := by ring

/-- TE dual of the diagonal flux bound: the same constant. -/
theorem te_degree_flux_eq (d : Data) (m : Index d.l) (x : Space) :
    ‖crossProduct (SourceGeneralMaxwell.teElectric d (representative d.l m) x)
      (conjugate (SourceGeneralMaxwell.teMagnetic d (representative d.l m) x)) 2‖=
    ‖crossProduct (SourceUnclippedMaxwell.electric d (representative d.l m) x)
      (conjugate (SourceUnclippedMaxwell.magnetic d (representative d.l m) x)) 2‖ := by
  rw [SourceRemotePlaneFluxTE.te_flux_eq_conj,RCLike.norm_conj]

/-! ### Summability over the degree -/

theorem summable_poly_geometric (j : ℕ) (c ρ : ℝ) (h0 : 0<ρ) (h1 : ρ<1) :
    Summable (fun l : ℕ => c*(((l : ℝ)+1)^j*ρ^(l+1))) := by
  have hg := summable_pow_mul_geometric_of_norm_lt_one j (r := ρ)
    (by rw [Real.norm_eq_abs,abs_of_pos h0]; exact h1)
  have hg1 := (summable_nat_add_iff 1).mpr hg
  refine (hg1.mul_left c).congr (fun l => ?_)
  push_cast
  rfl

theorem base_pos : 0<base := by
  unfold base OQ14.HarmonicSpatialMajorant.angularScale
  positivity

theorem scale_pos : 0<scale := by
  unfold scale OQ14.HarmonicSpatialMajorant.areaScale
  have : 0 ≤ (OQ14.SphereHarmonicBasis.angularMeasure.real Set.univ)⁻¹ := by positivity
  positivity

theorem summable_barrierAmplitude (k : ℕ) (R s : ℝ) (hR : 0<R) (hs : 0<s) (hsb : base*s<R) :
    Summable (fun l : ℕ => ((l : ℝ)+1)^k*barrierAmplitude R s l) := by
  have hb := base_pos
  have hρ0 : 0<base*s/R := by positivity
  have hρ1 : base*s/R<1 := by rw [div_lt_one hR]; exact hsb
  refine (summable_poly_geometric (k+3) (2*R*Real.exp (R/2)*scale/base) _ hρ0 hρ1).congr (fun l => ?_)
  have hρ : (base*s/R)^(l+1)=base^l*base*(s/R)^(l+1) := by
    rw [mul_div_assoc,mul_pow]; ring
  unfold barrierAmplitude envelope
  rw [hρ]
  field_simp
  ring

theorem summable_barrierConstant (k : ℕ) (R s : ℝ) (hR : 0<R) (hs : 0<s) (hsb : base*s<R) :
    Summable (fun l : ℕ => ((l : ℝ)+1)^k*barrierConstant R s l) := by
  have hb := base_pos
  have hρ0 : 0<(base*s/R)^2 := by positivity
  have hρ1 : (base*s/R)^2<1 := by
    have : base*s/R<1 := by rw [div_lt_one hR]; exact hsb
    have h0 : 0 ≤ base*s/R := by positivity
    nlinarith
  refine (summable_poly_geometric (k+6) (16*R^2*Real.exp R*scale^2/base^2) _ hρ0 hρ1).congr (fun l => ?_)
  have hρ : ((base*s/R)^2)^(l+1)=(base^l)^2*base^2*((s/R)^(l+1))^2 := by
    rw [← pow_mul,mul_div_assoc,mul_pow]; ring
  unfold barrierConstant envelope
  have hpw : (s/R)^(2*(l+1))=((s/R)^(l+1))^2 := by rw [← pow_mul]; ring_nf
  rw [hρ,hpw]
  field_simp
  ring

/-- Degree sum of the diagonal barrier constants, with the multiplicity weight `2l+1` and any
polynomial weight, converges whenever the inner scale is below `R/base`. -/
theorem tsum_degree_flux (k : ℕ) (R s : ℝ) (hR : 0<R) (hs : 0<s) (hsb : base*s<R) :
    Summable (fun l : ℕ => (2*(l : ℝ)+1)*((l : ℝ)+1)^k*barrierConstant R s l) ∧
    0 ≤ ∑' l : ℕ,(2*(l : ℝ)+1)*((l : ℝ)+1)^k*barrierConstant R s l := by
  have hS := summable_barrierConstant (k+1) R s hR hs hsb
  have hnn : ∀ l : ℕ,0 ≤ (2*(l : ℝ)+1)*((l : ℝ)+1)^k*barrierConstant R s l := fun l => by
    unfold barrierConstant
    have := envelope_nonnegative l
    positivity
  refine ⟨?_,tsum_nonneg hnn⟩
  refine Summable.of_nonneg_of_le hnn (fun l => ?_) (hS.mul_left 2)
  have hc : 0 ≤ barrierConstant R s l := by
    unfold barrierConstant
    have := envelope_nonnegative l
    positivity
  have h2 : (2*(l : ℝ)+1) ≤ 2*((l : ℝ)+1) := by linarith
  calc (2*(l : ℝ)+1)*((l : ℝ)+1)^k*barrierConstant R s l
      ≤ (2*((l : ℝ)+1))*((l : ℝ)+1)^k*barrierConstant R s l := by gcongr
    _ =2*(((l : ℝ)+1)^(k+1)*barrierConstant R s l) := by ring

end OQ14.BarrierDegreeFluxConstants
#print axioms OQ14.BarrierDegreeFluxConstants.rayPoint_smul
#print axioms OQ14.BarrierDegreeFluxConstants.ray_bound
#print axioms OQ14.BarrierDegreeFluxConstants.eval_ray_bound
#print axioms OQ14.BarrierDegreeFluxConstants.position_norm_le
#print axioms OQ14.BarrierDegreeFluxConstants.inverseSigma_norm_le
#print axioms OQ14.BarrierDegreeFluxConstants.electric_split
#print axioms OQ14.BarrierDegreeFluxConstants.magnetic_eq
#print axioms OQ14.BarrierDegreeFluxConstants.tm_decomp_state
#print axioms OQ14.BarrierDegreeFluxConstants.plane_flux_density_state
#print axioms OQ14.BarrierDegreeFluxConstants.degree_flux_bound
#print axioms OQ14.BarrierDegreeFluxConstants.decomp_mono
#print axioms OQ14.BarrierDegreeFluxConstants.barrierConstant_eq
#print axioms OQ14.BarrierDegreeFluxConstants.degree_flux_barrier
#print axioms OQ14.BarrierDegreeFluxConstants.te_degree_flux_eq
#print axioms OQ14.BarrierDegreeFluxConstants.summable_poly_geometric
#print axioms OQ14.BarrierDegreeFluxConstants.base_pos
#print axioms OQ14.BarrierDegreeFluxConstants.scale_pos
#print axioms OQ14.BarrierDegreeFluxConstants.summable_barrierAmplitude
#print axioms OQ14.BarrierDegreeFluxConstants.summable_barrierConstant
#print axioms OQ14.BarrierDegreeFluxConstants.tsum_degree_flux
