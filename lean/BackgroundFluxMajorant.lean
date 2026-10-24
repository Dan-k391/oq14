import BackgroundShellCoefficient
import BarrierDegreeFluxConstants
import BarrierAnnulusStateBounds
import SourceRemotePlaneBand

/-! Uniform inverse-cube majorant of the background field on the plane.  The TE background fields of a finite
coefficient vector are mode formulas applied to the radial background state; the state is bounded uniformly in the
shell index and the radius: in the core by the bounded transmission times the regular Riccati-Bessel energy, in the
annulus by the layerwise energy propagation of the exterior combination, and in the exterior by the Hankel energy.
The audited radial/tangential decomposition then gives constants independent of the shell index. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.BackgroundFluxMajorant
open Complex Filter OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.SourceRemotePlaneBand OQ14.BackgroundModeMaxwell OQ14.BackgroundCoreTransmission
  OQ14.BackgroundModeTE OQ14.RadialGluing
open scoped Topology ComplexConjugate

/-! ### Decomposition of the mode formulas for an arbitrary radial state -/

theorem eform_split (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l) (s u p : ℂ) (x : Space) (hx : x≠0) :
    (fun i => Eform l P s u p x i)=
      ((p/(‖x‖ : ℂ)^(l+2)) • HarmonicRadiationFactors.poloidal P x)+
      ((s*((l : ℂ)*(l+1)*u/(‖x‖ : ℂ)^(l+3))*complexEvaluate P x) • DebyeRadialTrace.position x) := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  ext i
  simp only [Eform,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    HarmonicRadiationFactors.poloidal_formula P l hp x i,HarmonicRadiationFactors.radial,
    DebyeRadialTrace.position]
  field_simp
  ring

theorem hform_eq (l : ℕ) (P : Poly) (u : ℂ) (x : Space) :
    (fun i => Hform l P u x i)=((-I*u/(‖x‖ : ℂ)^(l+1)) • DebyeRadialTrace.angularToroidal P x) := by
  ext i
  simp only [Hform,Pi.smul_apply,smul_eq_mul]
  ring

/-- Decomposition constants of the electric and magnetic mode formulas for any radial state `(u,p)` and inverse
permittivity `s` with `‖s‖ ≤ 1`. -/
theorem eh_decomp_state (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l) (Mpol Mp Mt : ℝ)
    (hMpol : ∀ n : SphereHarmonicBasis.Sphere,‖HarmonicRadiationFactors.poloidal P n‖ ≤ Mpol)
    (hMp : ∀ n : SphereHarmonicBasis.Sphere,‖complexEvaluate P n‖ ≤ Mp)
    (hMt : ∀ n : SphereHarmonicBasis.Sphere,‖DebyeRadialTrace.angularToroidal P n‖ ≤ Mt)
    (s : ℂ) (hs : ‖s‖ ≤ 1) (u p : ℂ) (x : Space) (hx : x≠0) :
    Decomp (‖p‖*Mpol) (((l : ℝ)*(l+1))*‖u‖*Mp) (fun i => Eform l P s u p x i) x ∧
    Decomp (‖u‖*Mt) 0 (fun i => Hform l P u x i) x := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hrk : ∀ k : ℕ,0<‖x‖^k := fun k => pow_pos hr k
  have hL : 0 ≤ (l : ℝ)*(l+1) := by positivity
  constructor
  · refine ⟨(p/(‖x‖ : ℂ)^(l+2)) • HarmonicRadiationFactors.poloidal P x,
      (s*((l : ℂ)*(l+1)*u/(‖x‖ : ℂ)^(l+3))*complexEvaluate P x) •
        DebyeRadialTrace.position x,eform_split l P hp s u p x hx,?_,⟨_,rfl⟩,?_,?_⟩
    · unfold dotPos
      simp only [Pi.smul_apply,smul_eq_mul]
      have := pol_dot P x
      unfold dotPos at this
      linear_combination (p/(‖x‖ : ℂ)^(l+2))*this
    · have hpol : ‖HarmonicRadiationFactors.poloidal P x‖ ≤ ‖x‖^(l+1)*Mpol :=
        BarrierDegreeFluxConstants.ray_bound (HarmonicRadiationFactors.poloidal P) (l+1)
          (HarmonicRadiationFactors.poloidal_smul P l hp) Mpol hMpol x hx
      rw [norm_smul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
      calc ‖p‖/‖x‖^(l+2)*‖HarmonicRadiationFactors.poloidal P x‖
          ≤ ‖p‖/‖x‖^(l+2)*(‖x‖^(l+1)*Mpol) :=
            mul_le_mul_of_nonneg_left hpol (div_nonneg (norm_nonneg _) (hrk _).le)
        _ =‖p‖*Mpol/‖x‖ := by
          field_simp
          ring
    · have hev := BarrierDegreeFluxConstants.eval_ray_bound P l hp Mp hMp x hx
      have hinv := hs
      rw [norm_smul]
      have hnum : ‖s*((l : ℂ)*(l+1)*u/(‖x‖ : ℂ)^(l+3))*
          complexEvaluate P x‖ ≤ ((l : ℝ)*(l+1))*‖u‖*Mp/‖x‖^3 := by
        have hl : ‖((l : ℂ)*(l+1))‖=(l : ℝ)*(l+1) := by
          rw [show ((l : ℂ)*(l+1))=(((l : ℝ)*(l+1) : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL]
        have hu : ‖((l : ℂ)*(l+1)*u)‖=((l : ℝ)*(l+1))*‖u‖ := by
          rw [norm_mul,hl]
        have hden : ‖(‖x‖ : ℂ)^(l+3)‖=‖x‖^(l+3) := by
          rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
        rw [norm_mul,norm_mul,norm_div,hu,hden]
        have hMp0 : 0 ≤ Mp := (norm_nonneg _).trans (hMp (BarrierDegreeFluxConstants.rayPoint x hx))
        calc ‖s‖*(((l : ℝ)*(l+1))*‖u‖/‖x‖^(l+3))*‖complexEvaluate P x‖
            ≤ 1*(((l : ℝ)*(l+1))*‖u‖/‖x‖^(l+3))*(‖x‖^l*Mp) := by
              gcongr
          _ =((l : ℝ)*(l+1))*‖u‖*Mp/‖x‖^3 := by
              field_simp
              ring
      calc ‖s*((l : ℂ)*(l+1)*u/(‖x‖ : ℂ)^(l+3))*
            complexEvaluate P x‖*‖DebyeRadialTrace.position x‖
          ≤ (((l : ℝ)*(l+1))*‖u‖*Mp/‖x‖^3)*‖x‖ :=
            mul_le_mul hnum (BarrierDegreeFluxConstants.position_norm_le x) (norm_nonneg _) (by
              have hMp0 : 0 ≤ Mp := (norm_nonneg _).trans (hMp (BarrierDegreeFluxConstants.rayPoint x hx))
              positivity)
        _ =((l : ℝ)*(l+1))*‖u‖*Mp/‖x‖^2 := by
          field_simp
          ring
  · refine ⟨(-I*u/(‖x‖ : ℂ)^(l+1)) • DebyeRadialTrace.angularToroidal P x,0,?_,?_,
      ⟨0,by simp⟩,?_,by simp⟩
    · rw [hform_eq,add_zero]
    · unfold dotPos
      simp only [Pi.smul_apply,smul_eq_mul]
      have := tor_dot P x
      unfold dotPos at this
      linear_combination (-I*u/(‖x‖ : ℂ)^(l+1))*this
    · have htor : ‖DebyeRadialTrace.angularToroidal P x‖ ≤ ‖x‖^l*Mt :=
        BarrierDegreeFluxConstants.ray_bound (DebyeRadialTrace.angularToroidal P) l
          (HarmonicRadiationGeometry.angularToroidal_smul P l hp) Mt hMt x hx
      rw [norm_smul,norm_div,norm_mul,norm_neg,Complex.norm_I,one_mul,norm_pow,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos hr]
      calc ‖u‖/‖x‖^(l+1)*‖DebyeRadialTrace.angularToroidal P x‖
          ≤ ‖u‖/‖x‖^(l+1)*(‖x‖^l*Mt) :=
            mul_le_mul_of_nonneg_left htor (div_nonneg (norm_nonneg _) (hrk _).le)
        _ =‖u‖*Mt/‖x‖ := by
          field_simp
          ring


/-! ### The background fields as mode formulas on the half background state -/

/-- Half of the (amplitude-two) background state: the state of the unit regular incident wave. -/
def bgHalf (d : Data) (r : ℝ) : OQ14.RadialStack.State :=
  (1/2 : ℂ) • backgroundState d.l d.gs d.R d.X d.hR r

theorem bgHalf_eq (d : Data) (r : ℝ) :
    bgHalf d r=kappa d • (sourceState d.l d.gs d.R d.X d.hR r-conjState (sourceState d.l d.gs d.R d.X d.hR r)) := by
  unfold bgHalf
  rw [backgroundState_eq d.l d.gs d.R d.X d.hR (hX_pos d) (RadialStack.chain_ordered d.chain) r,smul_smul]
  congr 1
  unfold kappa
  ring

theorem Eform_sub_smul (l : ℕ) (P : Poly) (s k u₁ p₁ u₂ p₂ : ℂ) (x : Space) (i : Fin 3) :
    Eform l P s (k*(u₁-u₂)) (k*(p₁-p₂)) x i=k*(Eform l P s u₁ p₁ x i-Eform l P s u₂ p₂ x i) := by
  unfold Eform
  ring

theorem Hform_sub_smul (l : ℕ) (P : Poly) (k u₁ u₂ : ℂ) (x : Space) (i : Fin 3) :
    Hform l P (k*(u₁-u₂)) x i=k*(Hform l P u₁ x i-Hform l P u₂ x i) := by
  unfold Hform
  ring

theorem backgroundElectric_eq_form (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : x≠0) (i : Fin 3) :
    backgroundElectric d P x i=
      Eform d.l P (inverseSigma d ‖x‖) (bgHalf d ‖x‖).1 (bgHalf d ‖x‖).2 x i := by
  rw [backgroundElectric_eq d P hp hh x hx i,conj_electric_eq_form,electric_eq_Eform,bgHalf_eq]
  simp only [Prod.smul_fst,Prod.smul_snd,Prod.fst_sub,Prod.snd_sub,smul_eq_mul]
  rw [Eform_sub_smul]
  rfl

theorem backgroundMagnetic_eq_form (d : Data) (P : Poly) (x : Space) (hx : x≠0) (i : Fin 3) :
    backgroundMagnetic d P x i=Hform d.l P (bgHalf d ‖x‖).1 x i := by
  rw [backgroundMagnetic_eq d P x hx i,conj_magnetic_eq_form,magnetic_eq_Hform,bgHalf_eq]
  simp only [Prod.smul_fst,Prod.fst_sub,smul_eq_mul]
  rw [Hform_sub_smul]
  rfl


/-! ### Uniform energy bound of the half background state -/

section StateBounds
open OQ14.RadialPropagation OQ14.HankelRealBasis OQ14.ModalAlgebra OQ14.RadialStack
open OQ14.HankelEnergy (angular)

theorem energy_smul (c u p : ℂ) : OQ14.RadialPropagation.energy (c*u) (c*p)=Complex.normSq c*OQ14.RadialPropagation.energy u p := by
  unfold OQ14.RadialPropagation.energy
  rw [map_mul,map_mul]
  ring

theorem normSq_add_le (a b : ℂ) : Complex.normSq (a+b) ≤ 2*(Complex.normSq a+Complex.normSq b) := by
  nlinarith [Complex.normSq_nonneg (a-b),Complex.normSq_add a b,Complex.normSq_sub a b]

theorem energy_add_le (u p v w : ℂ) : OQ14.RadialPropagation.energy (u+v) (p+w) ≤ 2*(OQ14.RadialPropagation.energy u p+OQ14.RadialPropagation.energy v w) := by
  unfold OQ14.RadialPropagation.energy
  have h1 := normSq_add_le u v
  have h2 := normSq_add_le p w
  linarith

theorem frob_low (l : ℕ) (ρ r : ℝ) (hρ : 0<ρ) (hl : angular l ≤ (1/2)^2*ρ^2) (hr : ρ ≤ r) :
    frobeniusSq l r ≤ 16/3 := by
  have h := low_range_frobeniusSq l (1/2) ρ r (by norm_num) hρ hr hl
  have e : 4/(1-(1/2 : ℝ)^2)=16/3 := by norm_num
  linarith

theorem energy_outgoing (l : ℕ) (r : ℝ) :
    OQ14.RadialPropagation.energy (outgoing l r).1 (outgoing l r).2=frobeniusSq l r := by
  rw [frobeniusSq_eq]
  rfl

theorem energy_incoming (l : ℕ) (r : ℝ) :
    OQ14.RadialPropagation.energy (incomingState l r).1 (incomingState l r).2=frobeniusSq l r := by
  rw [← energy_outgoing,incomingState_eq]
  unfold OQ14.RadialPropagation.energy conjState
  simp only [Complex.normSq_conj]

theorem energy_regularState (l : ℕ) (r : ℝ) :
    OQ14.RadialPropagation.energy (regularState l r).1 (regularState l r).2 ≤ frobeniusSq l r := by
  unfold OQ14.RadialPropagation.energy regularState frobeniusSq
  simp only [Complex.normSq_ofReal]
  nlinarith [sq_nonneg (irregular l r),sq_nonneg (irregularD l r)]

theorem normSq_half : Complex.normSq (1/2 : ℂ)=1/4 := by
  simp [Complex.normSq_apply]
  norm_num

theorem normSq_refl_sub_one_half (z : ℂ) (hz : Complex.normSq z=1) :
    Complex.normSq ((z-1)/2) ≤ 1 := by
  have h2 : Complex.normSq (2 : ℂ)=4 := by
    simp [Complex.normSq_apply]
    norm_num
  rw [map_div₀,h2]
  have h := normSq_add_le z (-1)
  have h1 : Complex.normSq (-1 : ℂ)=1 := by simp
  rw [← sub_eq_add_neg,hz,h1] at h
  linarith

/-- **Uniform OQ14.RadialPropagation.energy bound of the half background state** at every radius `r ≥ ρ`: core, annulus and exterior. -/
theorem bgHalf_energy_le (d : Data) (M : ℝ) (hM : 1≤M) (hparams : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M)
    (T W A : ℝ) (hT : ‖transmission d.l d.gs d.R d.X d.hR‖≤T) (hW : d.X-d.R≤W) (hA0 : 0≤A)
    (hA : angular d.l≤A*d.R^2) (ρ : ℝ) (hρ : 0<ρ) (hρl : angular d.l≤(1/2)^2*ρ^2) (r : ℝ) (hr : ρ ≤ r) :
    OQ14.RadialPropagation.energy (bgHalf d r).1 (bgHalf d r).2 ≤
      (T/2)^2*(16/3)+(1/4)*Real.exp ((2*M+A)*W)*(64/3)+64/3 := by
  have hX := hX_pos d
  have hRX := RadialStack.chain_ordered d.chain
  have hr0 : 0<r := hρ.trans_le hr
  have hT0 : 0≤T := (norm_nonneg _).trans hT
  have hc0 : 0≤(T/2)^2*(16/3) := by positivity
  have ha0 : 0≤(1/4)*Real.exp ((2*M+A)*W)*(64/3) := by positivity
  have hfr : ∀ y, ρ ≤ y → frobeniusSq d.l y ≤ 16/3 := fun y hy => frob_low d.l ρ y hρ hρl hy
  by_cases h1 : r ≤ d.R
  · have e : bgHalf d r=(transmission d.l d.gs d.R d.X d.hR/2) • regularState d.l r := by
      unfold bgHalf
      rw [backgroundState_core d.l d.gs d.R d.X d.hR r h1,smul_smul]
      congr 1
      ring
    rw [e]
    simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    rw [energy_smul]
    have h2 : Complex.normSq (transmission d.l d.gs d.R d.X d.hR/2) ≤ (T/2)^2 := by
      have : Complex.normSq (transmission d.l d.gs d.R d.X d.hR/2)=
          Complex.normSq (transmission d.l d.gs d.R d.X d.hR)/4 := by
        rw [map_div₀]
        congr 1
        simp [Complex.normSq_apply]
        norm_num
      rw [this,Complex.normSq_eq_norm_sq]
      have := pow_le_pow_left₀ (norm_nonneg _) hT 2
      nlinarith
    have h3 := (energy_regularState d.l r).trans (hfr r hr)
    calc _ ≤ (T/2)^2*(16/3) :=
          mul_le_mul h2 h3 (energy_nonnegative _ _) (sq_nonneg _)
      _ ≤ _ := by linarith
  · by_cases h2 : r ≤ d.X
    · have e : bgHalf d r=(1/2 : ℂ) • profile d.l d.gs
          (incomingState d.l d.X+reflection d.l d.gs d.R d.X d.hR • outgoing d.l d.X) r := by
        unfold bgHalf
        rw [backgroundState_stack d.l d.gs d.R d.X d.hR r (not_le.mp h1) h2]
      rw [e]
      simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
      rw [energy_smul,normSq_half]
      set sX := incomingState d.l d.X+reflection d.l d.gs d.R d.X d.hR • outgoing d.l d.X with hsX
      have hprof := OQ14.BarrierAnnulusStateBounds.profile_energy_le d.l d.chain M A d.hR hA0 hA hparams
        sX r ⟨(not_le.mp h1).le,h2⟩
      have hexp : Real.exp ((2*M+A)*(d.X-r)) ≤ Real.exp ((2*M+A)*W) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith [not_le.mp h1]
      have hsX_e : OQ14.RadialPropagation.energy sX.1 sX.2 ≤ 64/3 := by
        have hrefl := reflection_normSq d.l d.gs d.R d.X d.hR hX
        have hin := (energy_incoming d.l d.X).trans_le (hfr d.X (hr.trans h2))
        have hout : OQ14.RadialPropagation.energy (reflection d.l d.gs d.R d.X d.hR • outgoing d.l d.X).1
            (reflection d.l d.gs d.R d.X d.hR • outgoing d.l d.X).2 ≤ 16/3 := by
          simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
          rw [energy_smul,hrefl,one_mul]
          exact (energy_outgoing d.l d.X).trans_le (hfr d.X (hr.trans h2))
        have hadd := energy_add_le (incomingState d.l d.X).1 (incomingState d.l d.X).2
          (reflection d.l d.gs d.R d.X d.hR • outgoing d.l d.X).1
          (reflection d.l d.gs d.R d.X d.hR • outgoing d.l d.X).2
        rw [hsX]
        simp only [Prod.fst_add,Prod.snd_add]
        linarith
      have h4 : OQ14.RadialPropagation.energy (profile d.l d.gs sX r).1 (profile d.l d.gs sX r).2 ≤
          Real.exp ((2*M+A)*W)*(64/3) :=
        hprof.trans (mul_le_mul hexp hsX_e (energy_nonnegative _ _) (Real.exp_pos _).le)
      calc 1/4*OQ14.RadialPropagation.energy (profile d.l d.gs sX r).1 (profile d.l d.gs sX r).2
          ≤ 1/4*(Real.exp ((2*M+A)*W)*(64/3)) := by linarith
        _ ≤ _ := by linarith
    · have hx2 := not_le.mp h2
      have e : bgHalf d r=regularState d.l r+
          ((reflection d.l d.gs d.R d.X d.hR-1)/2) • outgoing d.l r := by
        unfold bgHalf
        rw [backgroundState_exterior_decomposition d.l d.gs d.R d.X d.hR hRX r hx2,smul_add,smul_smul,
          smul_smul]
        congr 1
        · rw [show (1/2 : ℂ)*2=1 by norm_num,one_smul]
        · congr 1
          ring
      rw [e]
      have hrefl := reflection_normSq d.l d.gs d.R d.X d.hR hX
      have hc := normSq_refl_sub_one_half _ hrefl
      have h5 := energy_add_le (regularState d.l r).1 (regularState d.l r).2
        (((reflection d.l d.gs d.R d.X d.hR-1)/2) • outgoing d.l r).1
        (((reflection d.l d.gs d.R d.X d.hR-1)/2) • outgoing d.l r).2
      have h6 : OQ14.RadialPropagation.energy (((reflection d.l d.gs d.R d.X d.hR-1)/2) • outgoing d.l r).1
          (((reflection d.l d.gs d.R d.X d.hR-1)/2) • outgoing d.l r).2 ≤ 16/3 := by
        simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
        rw [energy_smul]
        have := (energy_outgoing d.l r).trans_le (hfr r hr)
        calc _ ≤ 1*(16/3) := mul_le_mul hc this (energy_nonnegative _ _) zero_le_one
          _ = 16/3 := by ring
      have h7 := (energy_regularState d.l r).trans (hfr r hr)
      simp only [Prod.fst_add,Prod.snd_add]
      linarith

end StateBounds


/-! ### One TE mode of the physical stack -/

section Mode
open OQ14.HankelEnergy (angular)

theorem sphere_bounds (P : Poly) : ∃ Mpol Mp Mt : ℝ, 0≤Mpol ∧ 0≤Mp ∧ 0≤Mt ∧
    (∀ n : SphereHarmonicBasis.Sphere,‖HarmonicRadiationFactors.poloidal P n‖ ≤ Mpol) ∧
    (∀ n : SphereHarmonicBasis.Sphere,‖complexEvaluate P n‖ ≤ Mp) ∧
    (∀ n : SphereHarmonicBasis.Sphere,‖DebyeRadialTrace.angularToroidal P n‖ ≤ Mt) := by
  have h1 : Continuous (fun n : SphereHarmonicBasis.Sphere => HarmonicRadiationFactors.poloidal P n) :=
    (HarmonicRadiationFactors.poloidal_continuous P).comp continuous_subtype_val
  have h2 : Continuous (fun n : SphereHarmonicBasis.Sphere => complexEvaluate P n) :=
    (complexEvaluate_regular P).continuous.comp continuous_subtype_val
  have h3 : Continuous (fun n : SphereHarmonicBasis.Sphere => DebyeRadialTrace.angularToroidal P n) :=
    (HarmonicRadiationGeometry.angularToroidal_continuous P).comp continuous_subtype_val
  obtain ⟨M1,hM1⟩ := (isCompact_univ : IsCompact (Set.univ : Set SphereHarmonicBasis.Sphere)).exists_bound_of_continuousOn
    h1.continuousOn
  obtain ⟨M2,hM2⟩ := (isCompact_univ : IsCompact (Set.univ : Set SphereHarmonicBasis.Sphere)).exists_bound_of_continuousOn
    h2.continuousOn
  obtain ⟨M3,hM3⟩ := (isCompact_univ : IsCompact (Set.univ : Set SphereHarmonicBasis.Sphere)).exists_bound_of_continuousOn
    h3.continuousOn
  exact ⟨max 0 M1,max 0 M2,max 0 M3,le_max_left _ _,le_max_left _ _,le_max_left _ _,
    fun n => (hM1 n (Set.mem_univ n)).trans (le_max_right _ _),
    fun n => (hM2 n (Set.mem_univ n)).trans (le_max_right _ _),
    fun n => (hM3 n (Set.mem_univ n)).trans (le_max_right _ _)⟩

theorem decomp_neg {K1 K2 : ℝ} {F : Vector} {x : Space} (h : Decomp K1 K2 F x) : Decomp K1 K2 (-F) x := by
  have h1 := decomp_smul (-1 : ℂ) h
  rw [norm_neg,norm_one,one_mul,one_mul] at h1
  simpa using h1

theorem norm_le_sqrt_energy (u p : ℂ) (E : ℝ) (h : OQ14.RadialPropagation.energy u p ≤ E) :
    ‖u‖ ≤ Real.sqrt E ∧ ‖p‖ ≤ Real.sqrt E := by
  unfold OQ14.RadialPropagation.energy at h
  have h1 : ‖u‖^2 ≤ E := by
    rw [← Complex.normSq_eq_norm_sq]
    nlinarith [Complex.normSq_nonneg p]
  have h2 : ‖p‖^2 ≤ E := by
    rw [← Complex.normSq_eq_norm_sq]
    nlinarith [Complex.normSq_nonneg u]
  exact ⟨Real.le_sqrt_of_sq_le h1,Real.le_sqrt_of_sq_le h2⟩

/-- The data of degree `l` of the physical TE stack at shell index `s`. -/
abbrev physTEl (q : ℝ) (hq : 0<q) (n s l : ℕ) : Data := { physicalTE q hq n s with l := l }

theorem radius_ge_one (s : ℕ) : 1≤RadialPhaseLimit.radius s := by
  unfold RadialPhaseLimit.radius
  have := Real.two_le_pi
  have hs : (0 : ℝ)≤s := Nat.cast_nonneg s
  nlinarith

theorem physTEl_width (q : ℝ) (hq : 0<q) (n s l : ℕ) :
    (physTEl q hq n s l).X-(physTEl q hq n s l).R=OQ14.RadialFiniteLimit.width (OQ14.RadialPairedFamily.tm q hq n) := by
  show RadialPhaseLimit.radius s+RadialFiniteLimit.width (RadialPairedFamily.tm q hq n)-
    RadialPhaseLimit.radius s=OQ14.RadialFiniteLimit.width (OQ14.RadialPairedFamily.tm q hq n)
  ring

theorem physTEl_parameters (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n s l : ℕ) :
    ∀ g∈(physTEl q hq n s l).gs,1≤g.σ ∧ g.σ≤q^2 ∧ g.q^2≤q^2 := by
  intro g hg
  have h1 := physicalTE_sigma q hq n s g hg
  have h2 := physicalTE_parameters q hq hq1 n s g hg
  rw [h1,div_one] at h2
  rw [h1]
  exact ⟨le_rfl,one_le_sq' q hq1,h2.2⟩

/-- **Decomposition of one TE mode of the physical stack, uniformly in the shell index.**  For every radius
`‖x‖ ≥ ρ` the TE electric field (the background magnetic field of the TM structure) is purely orthogonal to `x`
with constant `B * Mt`, and the TE magnetic field (minus the background electric field) splits with constants
`B * Mpol` and `l(l+1) * B * Mp`, where `B` is the square root of the explicit energy bound. -/
theorem mode_decomp (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n l : ℕ) (P : Poly) (hp : P.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (Mpol Mp Mt T : ℝ)
    (hMpol : ∀ n : SphereHarmonicBasis.Sphere,‖HarmonicRadiationFactors.poloidal P n‖ ≤ Mpol)
    (hMp : ∀ n : SphereHarmonicBasis.Sphere,‖complexEvaluate P n‖ ≤ Mp)
    (hMt : ∀ n : SphereHarmonicBasis.Sphere,‖DebyeRadialTrace.angularToroidal P n‖ ≤ Mt)
    (hT : ∀ s : ℕ,‖transmission l (physicalTE q hq n s).gs (physicalTE q hq n s).R (physicalTE q hq n s).X
      (physicalTE q hq n s).hR‖ ≤ T)
    (ρ : ℝ) (hρ : 0<ρ) (hρl : angular l ≤ (1/2)^2*ρ^2) (s : ℕ) (x : Space) (hx : ρ ≤ ‖x‖) :
    Decomp (Real.sqrt ((T/2)^2*(16/3)+(1/4)*Real.exp ((2*q^2+angular l)*OQ14.RadialFiniteLimit.width (OQ14.RadialPairedFamily.tm q hq n))*(64/3)+64/3)*Mt) 0
        (backgroundMagnetic (physTEl q hq n s l) P x) x ∧
      Decomp (Real.sqrt ((T/2)^2*(16/3)+(1/4)*Real.exp ((2*q^2+angular l)*OQ14.RadialFiniteLimit.width (OQ14.RadialPairedFamily.tm q hq n))*(64/3)+64/3)*Mpol)
        (((l : ℝ)*(l+1))*Real.sqrt ((T/2)^2*(16/3)+(1/4)*Real.exp ((2*q^2+angular l)*OQ14.RadialFiniteLimit.width (OQ14.RadialPairedFamily.tm q hq n))*(64/3)+64/3)*Mp)
        (-(backgroundElectric (physTEl q hq n s l) P) x) x := by
  have hx0 : x≠0 := norm_pos_iff.mp (hρ.trans_le hx)
  set d := physTEl q hq n s l with hd
  have hen := bgHalf_energy_le d (q^2) (one_le_sq' q hq1) (physTEl_parameters q hq hq1 n s l) T
    (OQ14.RadialFiniteLimit.width (OQ14.RadialPairedFamily.tm q hq n)) (angular l) (hT s) (physTEl_width q hq n s l).le (by unfold angular; positivity)
    (by
      have h1 := radius_ge_one s
      have hR2 : (1 : ℝ)≤(physTEl q hq n s l).R^2 := by
        have : (physTEl q hq n s l).R=RadialPhaseLimit.radius s := rfl
        rw [this]
        nlinarith
      have : (0 : ℝ)≤angular l := by unfold angular; positivity
      nlinarith)
    ρ hρ hρl ‖x‖ hx
  obtain ⟨hu,hpp⟩ := norm_le_sqrt_energy _ _ _ hen
  have hs : ‖inverseSigma d ‖x‖‖≤1 :=
    BarrierDegreeFluxConstants.inverseSigma_norm_le d (fun g hg => (physTEl_parameters q hq hq1 n s l g hg).1) _
  obtain ⟨hE,hH⟩ := eh_decomp_state l P hp Mpol Mp Mt hMpol hMp hMt (inverseSigma d ‖x‖) hs
    (bgHalf d ‖x‖).1 (bgHalf d ‖x‖).2 x hx0
  have hM0 : 0≤Mt := (norm_nonneg _).trans (hMt (BarrierDegreeFluxConstants.rayPoint x hx0))
  have hMp0 : 0≤Mp := (norm_nonneg _).trans (hMp (BarrierDegreeFluxConstants.rayPoint x hx0))
  have hMpol0 : 0≤Mpol := (norm_nonneg _).trans (hMpol (BarrierDegreeFluxConstants.rayPoint x hx0))
  have eM : backgroundMagnetic d P x=fun i => Hform l P (bgHalf d ‖x‖).1 x i :=
    funext (fun i => backgroundMagnetic_eq_form d P x hx0 i)
  have eE : backgroundElectric d P x=fun i => Eform l P (inverseSigma d ‖x‖) (bgHalf d ‖x‖).1
      (bgHalf d ‖x‖).2 x i :=
    funext (fun i => backgroundElectric_eq_form d P hp hh x hx0 i)
  constructor
  · rw [eM]
    exact BarrierDegreeFluxConstants.decomp_mono hx0 hH (mul_le_mul_of_nonneg_right hu hM0) le_rfl
  · have : (-(backgroundElectric d P) x)=-(backgroundElectric d P x) := rfl
    rw [this,eE]
    apply decomp_neg
    refine BarrierDegreeFluxConstants.decomp_mono hx0 hE (mul_le_mul_of_nonneg_right hpp hMpol0) ?_
    have hL : (0 : ℝ)≤(l : ℝ)*(l+1) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hL) hMp0

end Mode


/-! ### Finite families and the flux majorant -/

section Family
open OQ14.HankelEnergy (angular)

/-- The TE magnetic background field of a finite family of modes: minus the TM-structure electric background. -/
def famBackgroundH {ι : Type*} (d₀ : Data) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) : Field :=
  ∑ q ∈ s,c q • (-(backgroundElectric { d₀ with l := lq q } (P q)))

/-- **Decomposition of the TE background fields of a finite family, uniformly in the shell index.**  For every
shell index `s` and every point with `‖x‖ ≥ 2 (L+1)` (`L` bounding the degrees of the family) the electric
field is orthogonal to `x` up to `K1/‖x‖` and the magnetic field splits into an orthogonal part `L1/‖x‖` and a
radial part `L2/‖x‖^2`, with `K1, L1, L2` independent of `s`. -/
theorem family_decomp (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n : ℕ) {ι : Type*} (supp : Finset ι) (c : ι → ℂ)
    (lq : ι → ℕ) (P : ι → Poly) (hp : ∀ j,(P j).IsHomogeneous (lq j))
    (hh : ∀ j,HarmonicPolynomial.formalLaplacian (P j)=0) (L : ℕ) (hL : ∀ j∈supp,lq j ≤ L) :
    ∃ K1 L1 L2 : ℝ,∀ (s : ℕ) (x : Space),2*((L : ℝ)+1) ≤ ‖x‖ →
      Decomp K1 0 (famBackground (physicalTE q hq n s) supp c lq P x) x ∧
      Decomp L1 L2 (famBackgroundH (physicalTE q hq n s) supp c lq P x) x := by
  choose Mpol Mp Mt hMpol0 hMp0 hMt0 hbpol hbp hbt using fun j => sphere_bounds (P j)
  have hTj : ∀ j,∃ T : ℝ,∀ s : ℕ,‖transmission (lq j) (physicalTE q hq n s).gs (physicalTE q hq n s).R
      (physicalTE q hq n s).X (physicalTE q hq n s).hR‖ ≤ T := by
    intro j
    obtain ⟨T,hT⟩ := (physicalTE_transmission_limit q hq n (lq j)).norm.bddAbove_range
    exact ⟨T,fun s => hT ⟨s,rfl⟩⟩
  choose T hT using hTj
  let B : ι → ℝ := fun j => Real.sqrt ((T j/2)^2*(16/3)+(1/4)*
    Real.exp ((2*q^2+angular (lq j))*OQ14.RadialFiniteLimit.width (OQ14.RadialPairedFamily.tm q hq n))*(64/3)+64/3)
  refine ⟨∑ j ∈ supp,‖c j‖*(B j*Mt j),∑ j ∈ supp,‖c j‖*(B j*Mpol j),
    ∑ j ∈ supp,‖c j‖*(((lq j : ℝ)*(lq j+1))*B j*Mp j),?_⟩
  intro s x hx
  have hρ : (0 : ℝ)<2*((L : ℝ)+1) := by positivity
  have hmode : ∀ j∈supp,
      Decomp (B j*Mt j) 0 (backgroundMagnetic (physTEl q hq n s (lq j)) (P j) x) x ∧
      Decomp (B j*Mpol j) (((lq j : ℝ)*(lq j+1))*B j*Mp j)
        (-(backgroundElectric (physTEl q hq n s (lq j)) (P j) x)) x := by
    intro j hj
    have hl : angular (lq j) ≤ (1/2)^2*(2*((L : ℝ)+1))^2 := by
      unfold angular
      have h1 : (lq j : ℝ) ≤ L := Nat.cast_le.mpr (hL j hj)
      have h0 : (0 : ℝ) ≤ lq j := Nat.cast_nonneg _
      nlinarith
    exact mode_decomp q hq hq1 n (lq j) (P j) (hp j) (hh j) (Mpol j) (Mp j) (Mt j) (T j) (hbpol j) (hbp j)
      (hbt j) (hT j) _ hρ hl s x hx
  constructor
  · have e : famBackground (physicalTE q hq n s) supp c lq P x=
        ∑ j ∈ supp,c j • backgroundMagnetic (physTEl q hq n s (lq j)) (P j) x := by
      simp [famBackground,Finset.sum_apply]
    rw [e]
    have h := decomp_sum supp (fun j => c j • backgroundMagnetic (physTEl q hq n s (lq j)) (P j) x)
      (fun j => ‖c j‖*(B j*Mt j)) (fun j => ‖c j‖*0) x
      (fun j hj => decomp_smul (c j) (hmode j hj).1)
    simpa using h
  · have e : famBackgroundH (physicalTE q hq n s) supp c lq P x=
        ∑ j ∈ supp,c j • (-(backgroundElectric (physTEl q hq n s (lq j)) (P j) x)) := by
      simp [famBackgroundH,Finset.sum_apply]
    rw [e]
    exact decomp_sum supp (fun j => c j • (-(backgroundElectric (physTEl q hq n s (lq j)) (P j) x)))
      (fun j => ‖c j‖*(B j*Mpol j)) (fun j => ‖c j‖*(((lq j : ℝ)*(lq j+1))*B j*Mp j)) x
      (fun j hj => decomp_smul (c j) (hmode j hj).2)

/-- **Flux majorant for a finite family.**  There are `ρ₁` and `C` such that for all shell indices `s` and all
plane points `x` with `ρ₁ ≤ ‖x‖` the normal flux density of the TE background field is at most `C/‖x‖^3`. -/
theorem family_flux_majorant (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n : ℕ) {ι : Type*} (supp : Finset ι)
    (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) (hp : ∀ j,(P j).IsHomogeneous (lq j))
    (hh : ∀ j,HarmonicPolynomial.formalLaplacian (P j)=0) (L : ℕ) (hL : ∀ j∈supp,lq j ≤ L) :
    ∃ ρ₁ C : ℝ,0<ρ₁ ∧ 0≤C ∧ ∀ (s : ℕ) (x : Space),x 2=0 → ρ₁ ≤ ‖x‖ →
      ‖crossProduct (famBackground (physicalTE q hq n s) supp c lq P x)
        (conjugate (famBackgroundH (physicalTE q hq n s) supp c lq P x)) 2‖ ≤ C/‖x‖^3 := by
  obtain ⟨K1,L1,L2,h⟩ := family_decomp q hq hq1 n supp c lq P hp hh L hL
  have hρ : (0 : ℝ)<2*((L : ℝ)+1) := by positivity
  refine ⟨2*((L : ℝ)+1),|2*0*L1+2*K1*L2|,hρ,abs_nonneg _,?_⟩
  intro s x hx2 hx
  obtain ⟨hE,hH⟩ := h s x hx
  have hr : 0<‖x‖ := hρ.trans_le hx
  have hf := flux_bound_of_decomp x hx2 hr _ _ K1 0 L1 L2 hE hH
  exact hf.trans (div_le_div_of_nonneg_right (le_abs_self _) (by positivity))

end Family


/-! ### The finite TE coefficient vector -/

section FiniteVector

/-- Bound on the degrees of a finite coefficient vector. -/
def maxDegree (A : SymmetricHarmonicJets.Index →₀ ℂ) : ℕ := A.support.sup (fun q => q.val.1)

theorem le_maxDegree (A : SymmetricHarmonicJets.Index →₀ ℂ) (q : SymmetricHarmonicJets.Index)
    (hq : q∈A.support) : q.val.1 ≤ maxDegree A :=
  Finset.le_sup (f := fun q : SymmetricHarmonicJets.Index => q.val.1) hq

/-- **Decomposition majorant for a finite TE coefficient vector.**  The TE background electric field
`famBackground` and magnetic field `famBackgroundH` of the physical paired stack at shell index `s` decompose,
for every `s` and every `x` with `ρ₁ ≤ ‖x‖`, with constants independent of `s`. -/
theorem background_decomp_majorant (q : ℝ) (hq : 1≤q) (n : ℕ) (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    ∃ ρ₁ K1 L1 L2 : ℝ,0<ρ₁ ∧ ∀ (s : ℕ) (x : Space),ρ₁ ≤ ‖x‖ →
      Decomp K1 0 (famBackground (physicalTE q (zero_lt_one.trans_le hq) n s) A.support (teCoeff A)
        (fun q => q.val.1) RestrictedTEIncoming.polynomial x) x ∧
      Decomp L1 L2 (famBackgroundH (physicalTE q (zero_lt_one.trans_le hq) n s) A.support (teCoeff A)
        (fun q => q.val.1) RestrictedTEIncoming.polynomial x) x := by
  obtain ⟨K1,L1,L2,h⟩ := family_decomp q (zero_lt_one.trans_le hq) hq n A.support (teCoeff A)
    (fun q => q.val.1) RestrictedTEIncoming.polynomial (fun j => polynomial_homogeneous j)
    (fun j => polynomial_harmonic j) (maxDegree A) (fun j hj => le_maxDegree A j hj)
  exact ⟨2*((maxDegree A : ℝ)+1),K1,L1,L2,by positivity,h⟩

/-- **Uniform inverse-cube flux majorant of the background field on the plane.**  For a finite TE coefficient
vector `A` there are `ρ₁ > 0` and `C ≥ 0` such that for all shell indices `s` and all plane points `x` with
`ρ₁ ≤ ‖x‖` the normal component of `E_bg × conj H_bg` is at most `C/‖x‖^3`. -/
theorem background_flux_majorant (q : ℝ) (hq : 1≤q) (n : ℕ) (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    ∃ ρ₁ C : ℝ,0<ρ₁ ∧ 0≤C ∧ ∀ (s : ℕ) (x : Space),x 2=0 → ρ₁ ≤ ‖x‖ →
      ‖crossProduct (famBackground (physicalTE q (zero_lt_one.trans_le hq) n s) A.support (teCoeff A)
          (fun q => q.val.1) RestrictedTEIncoming.polynomial x)
        (conjugate (famBackgroundH (physicalTE q (zero_lt_one.trans_le hq) n s) A.support (teCoeff A)
          (fun q => q.val.1) RestrictedTEIncoming.polynomial x)) 2‖ ≤ C/‖x‖^3 :=
  family_flux_majorant q (zero_lt_one.trans_le hq) hq n A.support (teCoeff A) (fun q => q.val.1)
    RestrictedTEIncoming.polynomial (fun j => polynomial_homogeneous j) (fun j => polynomial_harmonic j)
    (maxDegree A) (fun j hj => le_maxDegree A j hj)

end FiniteVector

end OQ14.BackgroundFluxMajorant
#print axioms OQ14.BackgroundFluxMajorant.eform_split
#print axioms OQ14.BackgroundFluxMajorant.hform_eq
#print axioms OQ14.BackgroundFluxMajorant.eh_decomp_state
#print axioms OQ14.BackgroundFluxMajorant.bgHalf_eq
#print axioms OQ14.BackgroundFluxMajorant.Eform_sub_smul
#print axioms OQ14.BackgroundFluxMajorant.Hform_sub_smul
#print axioms OQ14.BackgroundFluxMajorant.backgroundElectric_eq_form
#print axioms OQ14.BackgroundFluxMajorant.backgroundMagnetic_eq_form
#print axioms OQ14.BackgroundFluxMajorant.energy_smul
#print axioms OQ14.BackgroundFluxMajorant.normSq_add_le
#print axioms OQ14.BackgroundFluxMajorant.energy_add_le
#print axioms OQ14.BackgroundFluxMajorant.frob_low
#print axioms OQ14.BackgroundFluxMajorant.energy_outgoing
#print axioms OQ14.BackgroundFluxMajorant.energy_incoming
#print axioms OQ14.BackgroundFluxMajorant.energy_regularState
#print axioms OQ14.BackgroundFluxMajorant.normSq_half
#print axioms OQ14.BackgroundFluxMajorant.normSq_refl_sub_one_half
#print axioms OQ14.BackgroundFluxMajorant.bgHalf_energy_le
#print axioms OQ14.BackgroundFluxMajorant.sphere_bounds
#print axioms OQ14.BackgroundFluxMajorant.decomp_neg
#print axioms OQ14.BackgroundFluxMajorant.norm_le_sqrt_energy
#print axioms OQ14.BackgroundFluxMajorant.radius_ge_one
#print axioms OQ14.BackgroundFluxMajorant.physTEl_width
#print axioms OQ14.BackgroundFluxMajorant.physTEl_parameters
#print axioms OQ14.BackgroundFluxMajorant.mode_decomp
#print axioms OQ14.BackgroundFluxMajorant.family_decomp
#print axioms OQ14.BackgroundFluxMajorant.family_flux_majorant
#print axioms OQ14.BackgroundFluxMajorant.le_maxDegree
#print axioms OQ14.BackgroundFluxMajorant.background_decomp_majorant
#print axioms OQ14.BackgroundFluxMajorant.background_flux_majorant
