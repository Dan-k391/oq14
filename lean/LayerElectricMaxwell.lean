import LayerElectricProfiles
import RadialLayerMaxwell

/-! The first Maxwell equation through every interface of an actual finite TM chain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.LayerElectricMaxwell
open MeasureTheory Set OQ14.Maxwell OQ14.RadialStack OQ14.RadialGluing
  OQ14.ClippedLayerProfiles OQ14.LayerElectricProfiles OQ14.HarmonicPolynomial

theorem dispersion_identity (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (k : ℝ) (hdisp : ∀ g ∈ gs, g.q^2=k^2*g.σ) (r : ℝ) (hr : R < r) (hrX : r ≤ X) :
    inverseSigma gs r*((l : ℂ)*(l+1)/(r : ℂ)^2)-potential l gs r=(k : ℂ)^2 := by
  induction h with
  | nil R => exact (not_lt_of_ge hrX hr).elim
  | cons g gs R h ih =>
    by_cases hgr : g.a < r
    · simp only [inverseSigma,select,if_pos hgr,potential]
      have hd := congrArg Complex.ofReal (hdisp g (List.mem_cons_self))
      simp only [Complex.ofReal_pow,Complex.ofReal_mul] at hd
      simp only [RadialLayer.potential,HankelEnergy.angular,Complex.ofReal_sub,
        Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
        Complex.ofReal_add,Complex.ofReal_one]
      have hs : (g.σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr g.σ_pos.ne'
      field_simp [hs]
      linear_combination hd
    · simp only [inverseSigma,select,if_neg hgr,potential]
      exact ih (fun g hg => hdisp g (List.mem_cons_of_mem _ hg)) hr (not_lt.mp hgr)

theorem curl_coefficient (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (k : ℝ) (hdisp : ∀ g ∈ gs, g.q^2=k^2*g.σ) (s : State)
    (c r : ℝ) (hc : 0 < c) (hcr : c < r) (hr : R < r) (hrX : r ≤ X) :
    b l gs s c r-aD l gs s c r/(r : ℂ)=
      (k : ℂ)^2*quotient (l+1) (value l gs s c) c r := by
  have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hc.trans hcr).ne'
  have hd := dispersion_identity l h k hdisp r hr hrX
  calc
    _ = (inverseSigma gs r*((l : ℂ)*(l+1)/(r : ℂ)^2)-potential l gs r)*
        quotient (l+1) (value l gs s c) c r := by
      simp only [b,aD,if_pos hcr,quotient,radius,max_eq_right hcr.le,pow_succ]
      generalize he : (r : ℂ)^l=z
      have hz : z ≠ 0 := he ▸ pow_ne_zero l hn
      field_simp [hn,hz]
      ring_nf
      field_simp [hn,hz]
      ring
    _ = _ := by rw [hd]

def electric (l : ℕ) (gs : List Layer) (s : State) (c : ℝ) (p : Poly) : Field :=
  RadialNormalPrimitive.electric (a l gs s c) (b l gs s c) p

def magnetic (l : ℕ) (gs : List Layer) (s : State) (c k : ℝ) (p : Poly) : Field :=
  fun x i => (-Complex.I*(k : ℂ))*quotient (l+1) (value l gs s c) c ‖x‖*
    DebyeRadialTrace.angularToroidal p x i

theorem first_weak_maxwell (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (k : ℝ) (hdisp : ∀ g ∈ gs, g.q^2=k^2*g.σ) (s : State)
    (c : ℝ) (hc : 0 < c) (hcR : c ≤ R) (p : Poly)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {x : Space | R < ‖x‖ ∧ ‖x‖ < X}) :
    weakCurlPairing (electric l gs s c p) φ=
      fun i => ∫ x, (Complex.I*(k : ℂ)*magnetic l gs s c k p x i)*φ x := by
  rw [electric,LayerElectricProfiles.electric_weak_curl l h s c hc p φ hφ hcompact]
  ext i
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ tsupport φ
  · obtain ⟨hr,hX⟩ := hs hx
    rw [curl_coefficient l h k hdisp s c ‖x‖ hc (hcR.trans_lt hr) hr hX.le]
    simp only [magnetic]
    linear_combination (k : ℂ)^2*quotient (l+1) (value l gs s c) c ‖x‖*
      DebyeRadialTrace.angularToroidal p x i*φ x*Complex.I_sq
  · rw [image_eq_zero_of_nmem_tsupport hx,mul_zero,mul_zero]

theorem homogeneous_electric_components (l : ℕ) (q σ : ℝ) (α β : ℂ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    RiccatiTransmission.tmE l (σ : ℂ) (RadialLayer.value l q σ α β) p x i=
      (RadialLayer.momentum l q σ α β ‖x‖/(‖x‖ : ℂ)^l)*dcoord (complexEvaluate p) x i+
      ((l : ℂ)*(l+1)*RadialLayer.value l q σ α β ‖x‖/((σ : ℂ)*(‖x‖ : ℂ)^(l+3))-
        (l : ℂ)*RadialLayer.momentum l q σ α β ‖x‖/(‖x‖ : ℂ)^(l+2))*(x i : ℂ)*complexEvaluate p x := by
  have hr := norm_ne_zero_iff.mpr hx
  have hn : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hs : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ
  have hd := (RadialLayer.solution_ode l q σ α β ‖x‖ hq hσ hr).1
  change (σ : ℂ)⁻¹*RiccatiDebyeTrace.N l (RadialLayer.value l q σ α β) p x i=_
  rw [RiccatiDebyeTrace.N,RiccatiDebyeTrace.M,
    DebyeRadialTrace.toroidal_curl _ (RadialLayerMaxwell.profile_smooth l q σ α β hq) p l hp hh x hx,
    (RadialQuotient.profile_hasDerivAt l _ (fun r => (σ : ℂ)*RadialLayer.momentum l q σ α β r) ‖x‖ hr hd).deriv]
  simp only [RadialQuotient.profileD,RadialQuotient.profile,pow_succ]
  push_cast
  generalize he : (‖x‖ : ℂ)^l=z
  have hz : z ≠ 0 := he ▸ pow_ne_zero l hn
  field_simp [hn,hs,hz]
  ring_nf
  field_simp [hn,hs,hz]
  ring

end OQ14.LayerElectricMaxwell

#print axioms OQ14.LayerElectricMaxwell.dispersion_identity
#print axioms OQ14.LayerElectricMaxwell.curl_coefficient
#print axioms OQ14.LayerElectricMaxwell.first_weak_maxwell
#print axioms OQ14.LayerElectricMaxwell.homogeneous_electric_components
