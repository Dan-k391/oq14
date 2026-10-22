import ClippedLayerProfiles
import RadialQuotient

/-! The actual electric radial coefficients of a finite Riccati layer chain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.LayerElectricProfiles
open MeasureTheory Set Filter OQ14.Maxwell OQ14.RadialStack OQ14.RadialGluing
  OQ14.ClippedLayerProfiles
open scoped Topology

def value (l : ℕ) (gs : List Layer) (s : State) (c r : ℝ) : ℂ := (state l gs s c r).1
def momentum (l : ℕ) (gs : List Layer) (s : State) (c r : ℝ) : ℂ := (state l gs s c r).2
def quotient (n : ℕ) (f : ℝ → ℂ) (c r : ℝ) : ℂ := f r/(radius c r : ℂ)^n
def a (l : ℕ) (gs : List Layer) (s : State) (c : ℝ) : ℝ → ℂ :=
  quotient l (momentum l gs s c) c
def b (l : ℕ) (gs : List Layer) (s : State) (c r : ℝ) : ℂ :=
  inverseSigma gs (radius c r)*((l : ℂ)*(l+1)*quotient (l+3) (value l gs s c) c r)-
    (l : ℂ)*quotient (l+2) (momentum l gs s c) c r
def aD (l : ℕ) (gs : List Layer) (s : State) (c r : ℝ) : ℂ :=
  if c < r then potential l gs (radius c r)*quotient l (value l gs s c) c r-
    (l : ℂ)*quotient (l+1) (momentum l gs s c) c r else 0

theorem quotient_continuous (n : ℕ) (f : ℝ → ℂ) (hf : Continuous f) (c : ℝ) (hc : 0 < c) :
    Continuous (quotient n f c) :=
  hf.div ((Complex.continuous_ofReal.comp (radius_continuous c)).pow n)
    (fun r => pow_ne_zero n (Complex.ofReal_ne_zero.mpr (radius_pos c r hc).ne'))

theorem a_continuous (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (c : ℝ) (hc : 0 < c) : Continuous (a l gs s c) :=
  quotient_continuous l _ (state_continuous l h s c).snd c hc

theorem b_measurable (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (c : ℝ) (hc : 0 < c) : Measurable (b l gs s c) :=
  (((inverseSigma_measurable gs).comp (radius_continuous c).measurable).mul
    ((continuous_const.mul (quotient_continuous (l+3) _ (state_continuous l h s c).fst c hc)).measurable)).sub
    ((continuous_const.mul (quotient_continuous (l+2) _ (state_continuous l h s c).snd c hc)).measurable)

private theorem real_mul_locallyIntegrable (f g : ℝ → ℂ)
    (hf : LocallyIntegrable f) (hg : Continuous g) : LocallyIntegrable (fun r => f r*g r) := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (hf.integrableOn_isCompact hK).mul_continuousOn hg.continuousOn hK

theorem b_locallyIntegrable_real (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (c : ℝ) (hc : 0 < c) : LocallyIntegrable (b l gs s c) := by
  have hi : LocallyIntegrable (fun r => inverseSigma gs (radius c r)) :=
    select_comp_locallyIntegrable volume gs _ _ _ (radius_continuous c).measurable
      (fun _ => continuous_const.locallyIntegrable) continuous_const.locallyIntegrable
  exact (real_mul_locallyIntegrable _ _ hi
    (continuous_const.mul (quotient_continuous (l+3) _ (state_continuous l h s c).fst c hc))).sub
    ((continuous_const.mul (quotient_continuous (l+2) _ (state_continuous l h s c).snd c hc)).locallyIntegrable)

theorem primitive_intervalIntegrable (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (c : ℝ) (hc : 0 < c) (d e : ℝ) :
    IntervalIntegrable (RadialNormalPrimitive.radialDerivative (b l gs s c)) volume d e := by
  have hi := real_mul_locallyIntegrable _ _ (b_locallyIntegrable_real l h s c hc) Complex.continuous_ofReal
  have he : (fun r => b l gs s c r*(r : ℂ))=RadialNormalPrimitive.radialDerivative (b l gs s c) := by
    funext r
    exact mul_comm _ _
  rw [he] at hi
  exact (hi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

theorem b_locallyIntegrable_space (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (c : ℝ) (hc : 0 < c) : LocallyIntegrable (fun x : Space => b l gs s c ‖x‖) := by
  have hi := inverseSigma_comp_locallyIntegrable gs (fun x : Space => radius c ‖x‖)
    ((radius_continuous c).comp continuous_norm)
  exact (RadialInterface.locallyIntegrable_mul_continuous _ _ hi
    ((continuous_const.mul (quotient_continuous (l+3) _ (state_continuous l h s c).fst c hc)).comp continuous_norm)).sub
    (((continuous_const.mul (quotient_continuous (l+2) _ (state_continuous l h s c).snd c hc)).comp continuous_norm).locallyIntegrable)

theorem aD_locallyIntegrable_space (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (c : ℝ) (hc : 0 < c) : LocallyIntegrable (fun x : Space => aD l gs s c ‖x‖) := by
  have hi : LocallyIntegrable (fun x : Space =>
      potential l gs (radius c ‖x‖)*quotient l (value l gs s c) c ‖x‖-
        (l : ℂ)*quotient (l+1) (momentum l gs s c) c ‖x‖) :=
    (RadialInterface.locallyIntegrable_mul_continuous _ _
    (potential_comp_locallyIntegrable l gs c hc (fun x : Space => ‖x‖) continuous_norm)
    ((quotient_continuous l _ (state_continuous l h s c).fst c hc).comp continuous_norm)).sub
    (((continuous_const.mul (quotient_continuous (l+1) _ (state_continuous l h s c).snd c hc)).comp continuous_norm).locallyIntegrable)
  exact hi.indicator (measurableSet_lt measurable_const continuous_norm.measurable)

private theorem unclipped_quotient_hasDerivAt (n : ℕ) (f : ℝ → ℂ) (fD : ℂ) (r : ℝ)
    (hr : r ≠ 0) (hf : HasDerivAt f fD r) :
    HasDerivAt (fun t => f t/(t : ℂ)^n)
      (fD/(r : ℂ)^n-(n : ℂ)*f r/(r : ℂ)^(n+1)) r := by
  cases n with
  | zero => simpa using hf
  | succ n =>
    simpa only [RadialQuotient.profile,RadialQuotient.profileD,Nat.succ_eq_add_one,
      Nat.cast_add,Nat.cast_one,Nat.add_assoc] using
      RadialQuotient.profile_hasDerivAt n f (fun _ => fD) r hr hf

theorem a_hasDerivAt (l : ℕ) (gs : List Layer) (s : State) (c r : ℝ) (hc : 0 < c)
    (hrc : r ≠ c) (hr : r ∉ cuts gs) : HasDerivAt (a l gs s c) (aD l gs s c r) r := by
  rcases lt_or_gt_of_ne hrc with hlt|hgt
  · have he : a l gs s c =ᶠ[𝓝 r] fun _ => (profile l gs s c).2/(c : ℂ)^l := by
      filter_upwards [Iio_mem_nhds hlt] with t ht
      simp only [a,quotient,momentum,state,radius,max_eq_left (show t ≤ c from le_of_lt ht)]
    simpa only [aD,if_neg (not_lt.mpr hlt.le)] using
      (hasDerivAt_const r ((profile l gs s c).2/(c : ℂ)^l)).congr_of_eventuallyEq he
  · have he : a l gs s c =ᶠ[𝓝 r] fun t => (profile l gs s t).2/(t : ℂ)^l := by
      filter_upwards [Ioi_mem_nhds hgt] with t ht
      simp only [a,quotient,momentum,state,radius,max_eq_right (show c ≤ t from le_of_lt ht)]
    have hd := unclipped_quotient_hasDerivAt l (fun t => (profile l gs s t).2)
      ((potentialAt l gs r : ℂ)*(profile l gs s r).1) r (hc.trans hgt).ne'
      (profile_hasDerivAt l gs s r hr).2
    convert hd.congr_of_eventuallyEq he using 1
    simp only [aD,if_pos hgt,quotient,value,momentum,state,radius,max_eq_right hgt.le,potential_eq]
    ring

theorem b_continuousAt (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (c r : ℝ) (hc : 0 < c) (hrc : r ≠ c) (hr : r ∉ cuts gs) :
    ContinuousAt (b l gs s c) r := by
  have hq := quotient_continuous (l+3) _ (state_continuous l h s c).fst c hc
  have hp := quotient_continuous (l+2) _ (state_continuous l h s c).snd c hc
  have hi : ContinuousAt (fun t => inverseSigma gs (radius c t)) r := by
    rcases lt_or_gt_of_ne hrc with hlt|hgt
    · apply (show ContinuousAt (fun _ : ℝ => inverseSigma gs c) r from continuousAt_const).congr
      filter_upwards [Iio_mem_nhds hlt] with t ht
      simp only [radius,max_eq_left (show t ≤ c from le_of_lt ht)]
    · apply (inverseSigma_continuousAt gs r hr).congr
      filter_upwards [Ioi_mem_nhds hgt] with t ht
      simp only [radius,max_eq_right (show c ≤ t from le_of_lt ht)]
  exact (hi.mul (continuousAt_const.mul hq.continuousAt)).sub (continuousAt_const.mul hp.continuousAt)

theorem electric_weak_curl (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (c : ℝ) (hc : 0 < c) (p : HarmonicPolynomial.Poly)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hs : HasCompactSupport φ) :
    weakCurlPairing (RadialNormalPrimitive.electric (a l gs s c) (b l gs s c) p) φ=
      fun i => ∫ x, ((b l gs s c ‖x‖-aD l gs s c ‖x‖/(‖x‖ : ℂ))*
        DebyeRadialTrace.angularToroidal p x i)*φ x := by
  let S : Set ℝ := {c} ∪ {r | r ∈ cuts gs}
  have he : {r : ℝ | r ∈ cuts gs}=(cuts gs).toFinset := by ext r; simp
  have hS : S.Countable := Set.Countable.union (Set.countable_singleton c)
    (he ▸ (List.toFinset (cuts gs)).finite_toSet.countable)
  have hcut (r : ℝ) (hr : r ∉ S) : r ≠ c ∧ r ∉ cuts gs := by
    simpa only [S,mem_union,mem_singleton_iff,mem_setOf_eq,not_or] using hr
  exact RadialElectricCurl.electric_weak_curl _ _ _ p S hS
    (a_continuous l h s c hc).continuousOn (primitive_intervalIntegrable l h s c hc)
    ((Complex.measurable_ofReal.mul (b_measurable l h s c hc)).stronglyMeasurable)
    (b_locallyIntegrable_space l h s c hc) (aD_locallyIntegrable_space l h s c hc)
    (fun r _ hr => b_continuousAt l h s c r hc (hcut r hr).1 (hcut r hr).2)
    (fun r _ hr => a_hasDerivAt l gs s c r hc (hcut r hr).1 (hcut r hr).2) φ hφ hs

end OQ14.LayerElectricProfiles

#print axioms OQ14.LayerElectricProfiles.quotient_continuous
#print axioms OQ14.LayerElectricProfiles.a_continuous
#print axioms OQ14.LayerElectricProfiles.b_measurable
#print axioms OQ14.LayerElectricProfiles.b_locallyIntegrable_real
#print axioms OQ14.LayerElectricProfiles.primitive_intervalIntegrable
#print axioms OQ14.LayerElectricProfiles.b_locallyIntegrable_space
#print axioms OQ14.LayerElectricProfiles.aD_locallyIntegrable_space
#print axioms OQ14.LayerElectricProfiles.a_hasDerivAt
#print axioms OQ14.LayerElectricProfiles.b_continuousAt
#print axioms OQ14.LayerElectricProfiles.electric_weak_curl
