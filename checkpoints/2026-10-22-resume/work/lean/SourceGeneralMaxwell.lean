import SourceUnclippedMaxwell

/-! Both constitutive coefficients of the actual source state, including TE duality. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.SourceGeneralMaxwell
open MeasureTheory Set OQ14.Maxwell OQ14.RadialStack OQ14.SourceRadialSystem
open OQ14.ClippedLayerProfiles (radius)
open OQ14.LayerElectricProfiles (quotient)

def mu (d : Data) : ℝ → ℂ := SourceRadialSystem.extend d.R d.X
  (ClippedLayerProfiles.select d.gs (fun g _ => ((g.q^2/g.σ : ℝ) : ℂ)) (fun _ => 0)) (fun _ => 1)

theorem layer_dispersion (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (r : ℝ) (hr : R<r) (hrX : r≤X) :
    ClippedLayerProfiles.inverseSigma gs r*((l : ℂ)*(l+1)/(r : ℂ)^2)-
      ClippedLayerProfiles.potential l gs r=
      ClippedLayerProfiles.select gs (fun g _ => ((g.q^2/g.σ : ℝ) : ℂ)) (fun _ => 0) r := by
  induction h with
  | nil R => exact (not_lt_of_ge hrX hr).elim
  | cons g gs R h ih =>
    by_cases hgr : g.a<r
    · simp only [ClippedLayerProfiles.inverseSigma,ClippedLayerProfiles.potential,
        ClippedLayerProfiles.select,if_pos hgr,RadialLayer.potential,HankelEnergy.angular,
        Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
        Complex.ofReal_natCast,Complex.ofReal_add,Complex.ofReal_one]
      have hs : (g.σ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr g.σ_pos.ne'
      field_simp [hs]
    · simp only [ClippedLayerProfiles.inverseSigma,ClippedLayerProfiles.potential,
        ClippedLayerProfiles.select,if_neg hgr]
      exact ih hr (not_lt.mp hgr)

theorem dispersion_identity (d : Data) (r : ℝ) :
    inverseSigma d r*((d.l : ℂ)*(d.l+1)/(r : ℂ)^2)-potential d r=mu d r := by
  by_cases hR : r≤d.R
  · simp only [inverseSigma,potential,mu,SourceRadialSystem.extend,if_pos hR,
      HankelEnergy.weight,HankelEnergy.angular,Complex.ofReal_neg,Complex.ofReal_sub,
      Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_natCast,
      Complex.ofReal_add,Complex.ofReal_one]
    ring
  · by_cases hX : r≤d.X
    · simpa only [inverseSigma,potential,mu,SourceRadialSystem.extend,if_neg hR,if_pos hX] using
        layer_dispersion d.l d.chain r (not_le.mp hR) hX
    · simp only [inverseSigma,potential,mu,SourceRadialSystem.extend,if_neg hR,if_neg hX,
        HankelEnergy.weight,HankelEnergy.angular,Complex.ofReal_neg,Complex.ofReal_sub,
        Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_natCast,
        Complex.ofReal_add,Complex.ofReal_one]
      ring

theorem curl_coefficient (d : Data) (r : ℝ) (hr : d.c<r) :
    SourceElectricProfiles.b d r-SourceElectricProfiles.aD d r/(r : ℂ)=
      mu d r*quotient (d.l+1) (SourceElectricProfiles.value d) d.c r := by
  have hn : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (d.hc.trans hr).ne'
  calc
    _ = (inverseSigma d r*((d.l : ℂ)*(d.l+1)/(r : ℂ)^2)-potential d r)*
        quotient (d.l+1) (SourceElectricProfiles.value d) d.c r := by
      simp only [SourceElectricProfiles.b,SourceElectricProfiles.aD,if_pos hr,quotient,radius,
        max_eq_right hr.le,pow_succ]
      generalize he : (r : ℂ)^d.l=z
      have hz : z≠0 := he ▸ pow_ne_zero d.l hn
      field_simp [hn,hz]
      ring_nf
      field_simp [hn,hz]
      ring
    _ = _ := by rw [dispersion_identity]

theorem clipped_first_weak_maxwell (d : Data) (p : HarmonicPolynomial.Poly)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {x : Space | d.c<‖x‖}) :
    weakCurlPairing (SourceElectricProfiles.electric d p) φ=fun i => ∫ x,
      (Complex.I*mu d ‖x‖*SourceElectricProfiles.magnetic d p x i)*φ x := by
  rw [SourceElectricProfiles.electric_weak_curl d p φ hφ hcompact]
  ext i
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x∈tsupport φ
  · rw [curl_coefficient d ‖x‖ (hs hx)]
    simp only [SourceElectricProfiles.magnetic]
    linear_combination mu d ‖x‖*quotient (d.l+1) (SourceElectricProfiles.value d) d.c ‖x‖*
      DebyeRadialTrace.angularToroidal p x i*φ x*Complex.I_sq
  · rw [image_eq_zero_of_nmem_tsupport hx,mul_zero,mul_zero]

theorem first_weak_maxwell (d : Data) (p : HarmonicPolynomial.Poly)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ)
    (h0 : 0∉tsupport φ) :
    weakCurlPairing (SourceUnclippedMaxwell.electric d p) φ=fun i => ∫ x,
      (Complex.I*mu d ‖x‖*SourceUnclippedMaxwell.magnetic d p x i)*φ x := by
  obtain ⟨c,hc,hs⟩ := SourceUnclippedMaxwell.compact_test_gap φ h0
  rw [← SourceUnclippedMaxwell.weakCurlPairing_congr_on_support
    (SourceElectricProfiles.electric (SourceUnclippedMaxwell.reclip d c hc) p)
    (SourceUnclippedMaxwell.electric d p) φ
    (fun x hx => SourceUnclippedMaxwell.electric_agrees d c hc p x (hs hx))]
  rw [clipped_first_weak_maxwell (SourceUnclippedMaxwell.reclip d c hc) p φ hφ hcompact hs]
  ext i
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x∈tsupport φ
  · rw [SourceUnclippedMaxwell.magnetic_agrees d c hc p x (hs hx)]
    rfl
  · rw [image_eq_zero_of_nmem_tsupport hx,mul_zero,mul_zero]

theorem weakCurlPairing_neg (F : Field) (φ : Space → ℂ) :
    weakCurlPairing (fun x i => -F x i) φ=fun j => -weakCurlPairing F φ j := by
  ext j
  fin_cases j <;> simp [weakCurlPairing, neg_mul, integral_neg] <;> ring

def teElectric (d : Data) (p : HarmonicPolynomial.Poly) : Field := SourceUnclippedMaxwell.magnetic d p
def teMagnetic (d : Data) (p : HarmonicPolynomial.Poly) : Field := fun x i => -SourceUnclippedMaxwell.electric d p x i

theorem te_first_weak_maxwell (d : Data) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ)
    (h0 : 0∉tsupport φ) :
    weakCurlPairing (teElectric d p) φ=fun i => ∫ x,
      (Complex.I*sigma d ‖x‖*teMagnetic d p x i)*φ x := by
  rw [teElectric,SourceUnclippedMaxwell.second_weak_maxwell d p hp hh φ hφ hcompact h0]
  ext i
  apply integral_congr_ae
  filter_upwards with x
  simp only [teMagnetic]
  ring

theorem te_second_weak_maxwell (d : Data) (p : HarmonicPolynomial.Poly)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ)
    (h0 : 0∉tsupport φ) :
    weakCurlPairing (teMagnetic d p) φ=fun i => ∫ x,
      (-Complex.I*mu d ‖x‖*teElectric d p x i)*φ x := by
  change weakCurlPairing (fun x i => -SourceUnclippedMaxwell.electric d p x i) φ=_
  rw [weakCurlPairing_neg,first_weak_maxwell d p φ hφ hcompact h0]
  ext i
  simp only [teElectric]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  ring

end OQ14.SourceGeneralMaxwell

#print axioms OQ14.SourceGeneralMaxwell.layer_dispersion
#print axioms OQ14.SourceGeneralMaxwell.dispersion_identity
#print axioms OQ14.SourceGeneralMaxwell.curl_coefficient
#print axioms OQ14.SourceGeneralMaxwell.clipped_first_weak_maxwell
#print axioms OQ14.SourceGeneralMaxwell.first_weak_maxwell
#print axioms OQ14.SourceGeneralMaxwell.weakCurlPairing_neg
#print axioms OQ14.SourceGeneralMaxwell.te_first_weak_maxwell
#print axioms OQ14.SourceGeneralMaxwell.te_second_weak_maxwell
