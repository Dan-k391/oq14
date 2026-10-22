import SourceElectricProfiles
import RadialToroidalCurl

/-! Magnetic weak matching for the actual source state through every radial boundary. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.SourceMagneticProfiles
open MeasureTheory Set Filter OQ14.Maxwell OQ14.SourceRadialSystem
  OQ14.SourceElectricProfiles OQ14.RadialGluing
open OQ14.ClippedLayerProfiles (radius radius_pos)
open OQ14.LayerElectricProfiles (quotient quotient_continuous)
open scoped Topology

def eta (d : Data) : ℝ → ℂ := quotient (d.l+1) (value d) d.c
def etaD (d : Data) (r : ℝ) : ℂ :=
  if d.c<r then sigma d (radius d.c r)*quotient (d.l+1) (momentum d) d.c r-
    (d.l+1 : ℂ)*quotient (d.l+2) (value d) d.c r else 0

theorem eta_continuous (d : Data) : Continuous (eta d) :=
  quotient_continuous (d.l+1) _ (state_continuous d).fst d.c d.hc

theorem etaD_locallyIntegrable (d : Data) : LocallyIntegrable (fun x : Space => etaD d ‖x‖) := by
  have hi := sigma_locallyIntegrable d (fun x : Space => radius d.c ‖x‖)
    ((ClippedLayerProfiles.radius_continuous d.c).comp continuous_norm).measurable
  have hq : Continuous (fun x : Space => quotient (d.l+1) (momentum d) d.c ‖x‖) :=
    (quotient_continuous (d.l+1) _ (state_continuous d).snd d.c d.hc).comp continuous_norm
  have hv : Continuous (fun x : Space => quotient (d.l+2) (value d) d.c ‖x‖) :=
    (quotient_continuous (d.l+2) _ (state_continuous d).fst d.c d.hc).comp continuous_norm
  have ht : LocallyIntegrable (fun x : Space =>
      sigma d (radius d.c ‖x‖)*quotient (d.l+1) (momentum d) d.c ‖x‖-
        (d.l+1 : ℂ)*quotient (d.l+2) (value d) d.c ‖x‖) :=
    (RadialInterface.locallyIntegrable_mul_continuous _ _ hi hq).sub
    ((continuous_const.mul hv).locallyIntegrable)
  exact ht.indicator (measurableSet_lt measurable_const continuous_norm.measurable)

theorem eta_hasDerivAt (d : Data) (r : ℝ) (hr : r∉interfaces d) :
    HasDerivAt (eta d) (etaD d r) r := by
  rcases lt_or_gt_of_ne (off_interfaces d hr).1 with hlt|hgt
  · have he : eta d =ᶠ[𝓝 r] fun _ => (raw d d.c).1/(d.c : ℂ)^(d.l+1) := by
      filter_upwards [Iio_mem_nhds hlt] with t ht
      simp only [eta,quotient,value,SourceRadialSystem.state,radius,max_eq_left (show t≤d.c from le_of_lt ht)]
    simpa only [etaD,if_neg (not_lt.mpr hlt.le)] using
      (hasDerivAt_const r ((raw d d.c).1/(d.c : ℂ)^(d.l+1))).congr_of_eventuallyEq he
  · have he : eta d =ᶠ[𝓝 r] fun t => (raw d t).1/(t : ℂ)^(d.l+1) := by
      filter_upwards [Ioi_mem_nhds hgt] with t ht
      simp only [eta,quotient,value,SourceRadialSystem.state,radius,max_eq_right (show d.c≤t from le_of_lt ht)]
    have hd := RadialQuotient.profile_hasDerivAt d.l (fun t => (raw d t).1)
      (fun t => sigma d t*(raw d t).2) r (d.hc.trans hgt).ne' (raw_ode d r (d.hc.trans hgt) hr).1
    convert hd.congr_of_eventuallyEq he using 1
    simp only [etaD,if_pos hgt,quotient,value,momentum,SourceRadialSystem.state,radius,max_eq_right hgt.le,
      RadialQuotient.profileD,Nat.cast_add,Nat.cast_one]
    ring

theorem magnetic_weak_curl (d : Data) (p : HarmonicPolynomial.Poly)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) :
    weakCurlPairing (magnetic d p) φ=fun j => ∫ x,curl (magnetic d p) x j*φ x := by
  exact RadialMultiplierWeak.weak_curl
    (fun r => -Complex.I*eta d r) (fun r => -Complex.I*etaD d r)
    (DebyeRadialTrace.angularToroidal p) (interfaces d) (interfaces_countable d)
    (continuous_const.mul (eta_continuous d))
    (fun j => (LayerMagneticProfiles.angular_smooth p j).of_le (by simp))
    (by
      have hi := RadialInterface.locallyIntegrable_mul_continuous _ _ (etaD_locallyIntegrable d)
        (show Continuous (fun _ : Space => -Complex.I) from continuous_const)
      simpa only [mul_comm] using hi)
    (fun r _ hr => (eta_hasDerivAt d r hr).const_mul _) φ hφ hcompact

theorem sigma_inverse (d : Data) (r : ℝ) (hr : r∉interfaces d) :
    sigma d r*inverseSigma d r=1 := by
  by_cases hR : r≤d.R
  · simp only [sigma,inverseSigma,SourceRadialSystem.extend,if_pos hR,one_mul]
  · by_cases hX : r≤d.X
    · obtain ⟨g,_,α,β,_,hσ,hi⟩ := LayerMagneticMaxwell.profile_layer_germ d.l d.chain
        (0,0) r (not_le.mp hR) hX (off_interfaces d hr).2.2.2
      simp only [sigma,inverseSigma,SourceRadialSystem.extend,if_neg hR,if_pos hX,hσ,hi]
      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr g.σ_pos.ne')
    · simp only [sigma,inverseSigma,SourceRadialSystem.extend,if_neg hR,if_neg hX,one_mul]

theorem curl_coefficients (d : Data) (r : ℝ) (hcr : d.c<r) (hr : r∉interfaces d) :
    (r : ℂ)*etaD d r+(d.l+1 : ℂ)*eta d r=sigma d r*a d r ∧
      -(d.l : ℂ)*etaD d r/(r : ℂ)=sigma d r*b d r := by
  have hn : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (d.hc.trans hcr).ne'
  have hs := sigma_inverse d r hr
  constructor
  · simp only [etaD,if_pos hcr,eta,a,quotient,radius,max_eq_right hcr.le,pow_succ]
    generalize he : (r : ℂ)^d.l=z
    have hz : z≠0 := he ▸ pow_ne_zero d.l hn
    field_simp [hn,hz]
    ring_nf
    field_simp [hn,hz]
    ring
  · rw [b,mul_sub,← mul_assoc (sigma d r) (inverseSigma d (radius d.c r)),
      show radius d.c r=r from max_eq_right hcr.le,hs,one_mul]
    simp only [etaD,if_pos hcr,quotient,radius,max_eq_right hcr.le,pow_succ]
    generalize he : (r : ℂ)^d.l=z
    have hz : z≠0 := he ▸ pow_ne_zero d.l hn
    field_simp [hn,hz]
    ring_nf
    field_simp [hn,hz]
    ring

theorem second_pointwise (d : Data) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) (x : Space)
    (hcx : d.c<‖x‖) (hi : ‖x‖∉interfaces d) :
    curl (magnetic d p) x=fun j => -Complex.I*sigma d ‖x‖*electric d p x j := by
  have hx : x≠0 := norm_pos_iff.mp (d.hc.trans hcx)
  obtain ⟨ha,hb⟩ := curl_coefficients d ‖x‖ hcx hi
  ext j
  have ht := RadialToroidalCurl.curl_formula (fun r => -Complex.I*eta d r)
    (-Complex.I*etaD d ‖x‖) p d.l hp hh x hx ((eta_hasDerivAt d ‖x‖ hi).const_mul _) j
  change curl (magnetic d p) x j=_ at ht
  rw [ht]
  calc
    _ = -Complex.I*(((‖x‖ : ℂ)*etaD d ‖x‖+(d.l+1 : ℂ)*eta d ‖x‖)*
        dcoord (HarmonicPolynomial.complexEvaluate p) x j+
        (-(d.l : ℂ)*etaD d ‖x‖/(‖x‖ : ℂ))*(x j : ℂ)*HarmonicPolynomial.complexEvaluate p x) := by ring
    _ = _ := by rw [ha,hb]; simp only [electric,RadialNormalPrimitive.electric]; ring

theorem second_weak_maxwell (d : Data) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {x : Space | d.c<‖x‖}) :
    weakCurlPairing (magnetic d p) φ=fun j => ∫ x,
      (-Complex.I*sigma d ‖x‖*electric d p x j)*φ x := by
  rw [magnetic_weak_curl d p φ hφ hcompact]
  ext j
  apply integral_congr_ae
  filter_upwards [SphericalInterfaces.ae_off_interfaces _ (interfaces_countable d)] with x hx
  by_cases ht : x∈tsupport φ
  · rw [second_pointwise d p hp hh x (hs ht) hx]
  · rw [image_eq_zero_of_nmem_tsupport ht,mul_zero,mul_zero]

end OQ14.SourceMagneticProfiles

#print axioms OQ14.SourceMagneticProfiles.eta_continuous
#print axioms OQ14.SourceMagneticProfiles.etaD_locallyIntegrable
#print axioms OQ14.SourceMagneticProfiles.eta_hasDerivAt
#print axioms OQ14.SourceMagneticProfiles.magnetic_weak_curl
#print axioms OQ14.SourceMagneticProfiles.sigma_inverse
#print axioms OQ14.SourceMagneticProfiles.curl_coefficients
#print axioms OQ14.SourceMagneticProfiles.second_pointwise
#print axioms OQ14.SourceMagneticProfiles.second_weak_maxwell
