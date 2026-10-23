import SourceRadialSystem

/-! Electric weak Maxwell matching through the core, every layer, and the exterior. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.SourceElectricProfiles
open MeasureTheory Set Filter OQ14.Maxwell OQ14.SourceRadialSystem
open OQ14.ClippedLayerProfiles (radius radius_continuous radius_pos)
open OQ14.LayerElectricProfiles (quotient quotient_continuous)
open scoped Topology

def value (d : Data) (r : ℝ) : ℂ := (state d r).1
def momentum (d : Data) (r : ℝ) : ℂ := (state d r).2
def a (d : Data) : ℝ → ℂ := quotient d.l (momentum d) d.c
def b (d : Data) (r : ℝ) : ℂ :=
  inverseSigma d (radius d.c r)*((d.l : ℂ)*(d.l+1)*quotient (d.l+3) (value d) d.c r)-
    (d.l : ℂ)*quotient (d.l+2) (momentum d) d.c r
def aD (d : Data) (r : ℝ) : ℂ :=
  if d.c<r then potential d (radius d.c r)*quotient d.l (value d) d.c r-
    (d.l : ℂ)*quotient (d.l+1) (momentum d) d.c r else 0

theorem a_continuous (d : Data) : Continuous (a d) :=
  quotient_continuous d.l _ (state_continuous d).snd d.c d.hc

theorem b_measurable (d : Data) : Measurable (b d) :=
  (((inverseSigma_measurable d).comp (radius_continuous d.c).measurable).mul
    ((continuous_const.mul (quotient_continuous (d.l+3) _ (state_continuous d).fst d.c d.hc)).measurable)).sub
    ((continuous_const.mul (quotient_continuous (d.l+2) _ (state_continuous d).snd d.c d.hc)).measurable)

private theorem real_mul_locallyIntegrable (f g : ℝ → ℂ)
    (hf : LocallyIntegrable f) (hg : Continuous g) : LocallyIntegrable (fun r => f r*g r) := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (hf.integrableOn_isCompact hK).mul_continuousOn hg.continuousOn hK

theorem b_locallyIntegrable_real (d : Data) : LocallyIntegrable (b d) := by
  have hi := inverseSigma_locallyIntegrable volume d (radius d.c) (radius_continuous d.c).measurable
  exact (real_mul_locallyIntegrable _ _ hi
    (continuous_const.mul (quotient_continuous (d.l+3) _ (state_continuous d).fst d.c d.hc))).sub
    ((continuous_const.mul (quotient_continuous (d.l+2) _ (state_continuous d).snd d.c d.hc)).locallyIntegrable)

theorem primitive_intervalIntegrable (d : Data) (e f : ℝ) :
    IntervalIntegrable (RadialNormalPrimitive.radialDerivative (b d)) volume e f := by
  have hi := real_mul_locallyIntegrable _ _ (b_locallyIntegrable_real d) Complex.continuous_ofReal
  have he : (fun r => b d r*(r : ℂ))=RadialNormalPrimitive.radialDerivative (b d) := by
    funext r
    exact mul_comm _ _
  rw [he] at hi
  exact (hi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

theorem b_locallyIntegrable_space (d : Data) : LocallyIntegrable (fun x : Space => b d ‖x‖) := by
  have hi := inverseSigma_locallyIntegrable volume d (fun x : Space => radius d.c ‖x‖)
    ((radius_continuous d.c).comp continuous_norm).measurable
  exact (RadialInterface.locallyIntegrable_mul_continuous _ _ hi
    ((continuous_const.mul (quotient_continuous (d.l+3) _ (state_continuous d).fst d.c d.hc)).comp continuous_norm)).sub
    (((continuous_const.mul (quotient_continuous (d.l+2) _ (state_continuous d).snd d.c d.hc)).comp continuous_norm).locallyIntegrable)

theorem aD_locallyIntegrable_space (d : Data) : LocallyIntegrable (fun x : Space => aD d ‖x‖) := by
  have hi : LocallyIntegrable (fun x : Space =>
      potential d (radius d.c ‖x‖)*quotient d.l (value d) d.c ‖x‖-
        (d.l : ℂ)*quotient (d.l+1) (momentum d) d.c ‖x‖) :=
    (RadialInterface.locallyIntegrable_mul_continuous _ _
    (potential_locallyIntegrable d (fun x : Space => ‖x‖) continuous_norm)
    ((quotient_continuous d.l _ (state_continuous d).fst d.c d.hc).comp continuous_norm)).sub
    (((continuous_const.mul (quotient_continuous (d.l+1) _ (state_continuous d).snd d.c d.hc)).comp continuous_norm).locallyIntegrable)
  exact hi.indicator (measurableSet_lt measurable_const continuous_norm.measurable)

private theorem quotient_hasDerivAt (n : ℕ) (f : ℝ → ℂ) (fD : ℂ) (r : ℝ)
    (hr : r≠0) (hf : HasDerivAt f fD r) :
    HasDerivAt (fun t => f t/(t : ℂ)^n)
      (fD/(r : ℂ)^n-(n : ℂ)*f r/(r : ℂ)^(n+1)) r := by
  cases n with
  | zero => simpa using hf
  | succ n =>
    simpa only [RadialQuotient.profile,RadialQuotient.profileD,Nat.succ_eq_add_one,
      Nat.cast_add,Nat.cast_one,Nat.add_assoc] using
      RadialQuotient.profile_hasDerivAt n f (fun _ => fD) r hr hf

theorem a_hasDerivAt (d : Data) (r : ℝ) (hr : r∉interfaces d) :
    HasDerivAt (a d) (aD d r) r := by
  rcases lt_or_gt_of_ne (off_interfaces d hr).1 with hlt|hgt
  · have he : a d =ᶠ[𝓝 r] fun _ => (raw d d.c).2/(d.c : ℂ)^d.l := by
      filter_upwards [Iio_mem_nhds hlt] with t ht
      simp only [a,quotient,momentum,state,radius,max_eq_left (show t≤d.c from le_of_lt ht)]
    simpa only [aD,if_neg (not_lt.mpr hlt.le)] using
      (hasDerivAt_const r ((raw d d.c).2/(d.c : ℂ)^d.l)).congr_of_eventuallyEq he
  · have he : a d =ᶠ[𝓝 r] fun t => (raw d t).2/(t : ℂ)^d.l := by
      filter_upwards [Ioi_mem_nhds hgt] with t ht
      simp only [a,quotient,momentum,state,radius,max_eq_right (show d.c≤t from le_of_lt ht)]
    have hd := quotient_hasDerivAt d.l (fun t => (raw d t).2)
      (potential d r*(raw d r).1) r (d.hc.trans hgt).ne' (raw_ode d r (d.hc.trans hgt) hr).2
    convert hd.congr_of_eventuallyEq he using 1
    simp only [aD,if_pos hgt,quotient,value,momentum,state,radius,max_eq_right hgt.le]
    ring

theorem b_continuousAt (d : Data) (r : ℝ) (hr : r∉interfaces d) : ContinuousAt (b d) r := by
  have hq := quotient_continuous (d.l+3) _ (state_continuous d).fst d.c d.hc
  have hp := quotient_continuous (d.l+2) _ (state_continuous d).snd d.c d.hc
  have hi : ContinuousAt (fun t => inverseSigma d (radius d.c t)) r := by
    rcases lt_or_gt_of_ne (off_interfaces d hr).1 with hlt|hgt
    · apply (show ContinuousAt (fun _ : ℝ => inverseSigma d d.c) r from continuousAt_const).congr
      filter_upwards [Iio_mem_nhds hlt] with t ht
      simp only [radius,max_eq_left (show t≤d.c from le_of_lt ht)]
    · apply (inverseSigma_continuousAt d r hr).congr
      filter_upwards [Ioi_mem_nhds hgt] with t ht
      simp only [radius,max_eq_right (show d.c≤t from le_of_lt ht)]
  exact (hi.mul (continuousAt_const.mul hq.continuousAt)).sub (continuousAt_const.mul hp.continuousAt)

def electric (d : Data) (p : HarmonicPolynomial.Poly) : Field :=
  RadialNormalPrimitive.electric (a d) (b d) p

def magnetic (d : Data) (p : HarmonicPolynomial.Poly) : Field :=
  fun x i => -Complex.I*quotient (d.l+1) (value d) d.c ‖x‖*DebyeRadialTrace.angularToroidal p x i

theorem electric_weak_curl (d : Data) (p : HarmonicPolynomial.Poly)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    weakCurlPairing (electric d p) φ=fun i => ∫ x,
      ((b d ‖x‖-aD d ‖x‖/(‖x‖ : ℂ))*DebyeRadialTrace.angularToroidal p x i)*φ x :=
  RadialElectricCurl.electric_weak_curl _ _ _ p (interfaces d) (interfaces_countable d)
    (a_continuous d).continuousOn (primitive_intervalIntegrable d)
    ((Complex.measurable_ofReal.mul (b_measurable d)).stronglyMeasurable)
    (b_locallyIntegrable_space d) (aD_locallyIntegrable_space d)
    (fun r _ hr => b_continuousAt d r hr) (fun r _ hr => a_hasDerivAt d r hr) φ hφ hs

theorem curl_coefficient (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (r : ℝ) (hr : d.c<r) :
    b d r-aD d r/(r : ℂ)=quotient (d.l+1) (value d) d.c r := by
  have hn : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (d.hc.trans hr).ne'
  calc
    _ = (inverseSigma d r*((d.l : ℂ)*(d.l+1)/(r : ℂ)^2)-potential d r)*
        quotient (d.l+1) (value d) d.c r := by
      simp only [b,aD,if_pos hr,quotient,radius,max_eq_right hr.le,pow_succ]
      generalize he : (r : ℂ)^d.l=z
      have hz : z≠0 := he ▸ pow_ne_zero d.l hn
      field_simp [hn,hz]
      ring_nf
      field_simp [hn,hz]
      ring
    _ = _ := by rw [dispersion_identity d hdisp,one_mul]

theorem first_weak_maxwell (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (p : HarmonicPolynomial.Poly)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {x : Space | d.c<‖x‖}) :
    weakCurlPairing (electric d p) φ=fun i => ∫ x, (Complex.I*magnetic d p x i)*φ x := by
  rw [electric_weak_curl d p φ hφ hcompact]
  ext i
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x∈tsupport φ
  · rw [curl_coefficient d hdisp ‖x‖ (hs hx)]
    simp only [magnetic]
    linear_combination quotient (d.l+1) (value d) d.c ‖x‖*
      DebyeRadialTrace.angularToroidal p x i*φ x*Complex.I_sq
  · rw [image_eq_zero_of_nmem_tsupport hx,mul_zero,mul_zero]

end OQ14.SourceElectricProfiles

#print axioms OQ14.SourceElectricProfiles.a_continuous
#print axioms OQ14.SourceElectricProfiles.b_measurable
#print axioms OQ14.SourceElectricProfiles.b_locallyIntegrable_real
#print axioms OQ14.SourceElectricProfiles.primitive_intervalIntegrable
#print axioms OQ14.SourceElectricProfiles.b_locallyIntegrable_space
#print axioms OQ14.SourceElectricProfiles.aD_locallyIntegrable_space
#print axioms OQ14.SourceElectricProfiles.a_hasDerivAt
#print axioms OQ14.SourceElectricProfiles.b_continuousAt
#print axioms OQ14.SourceElectricProfiles.electric_weak_curl
#print axioms OQ14.SourceElectricProfiles.curl_coefficient
#print axioms OQ14.SourceElectricProfiles.first_weak_maxwell
