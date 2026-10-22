import LayerElectricMaxwell
import RadialMultiplierWeak

/-! Actual magnetic profiles and integrable weak curls through the finite layer chain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.LayerMagneticProfiles
open MeasureTheory Set Filter OQ14.Maxwell OQ14.RadialStack OQ14.RadialGluing
  OQ14.ClippedLayerProfiles OQ14.LayerElectricProfiles OQ14.HarmonicPolynomial
open scoped Topology

def eta (l : ℕ) (gs : List Layer) (s : State) (c : ℝ) : ℝ → ℂ :=
  quotient (l+1) (value l gs s c) c

def etaD (l : ℕ) (gs : List Layer) (s : State) (c r : ℝ) : ℂ :=
  if c<r then (sigmaAt gs (radius c r) : ℂ)*quotient (l+1) (momentum l gs s c) c r-
    (l+1 : ℂ)*quotient (l+2) (value l gs s c) c r else 0

theorem eta_continuous (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (c : ℝ) (hc : 0<c) : Continuous (eta l gs s c) :=
  quotient_continuous (l+1) _ (state_continuous l h s c).fst c hc

theorem sigma_select (gs : List Layer) (r : ℝ) :
    (sigmaAt gs r : ℂ)=select gs (fun g _ => (g.σ : ℂ)) (fun _ => 0) r := by
  induction gs with
  | nil => simp [sigmaAt,select]
  | cons g gs ih => simp only [sigmaAt,select]; split_ifs <;> simp_all

theorem etaD_locallyIntegrable (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (c : ℝ) (hc : 0<c) : LocallyIntegrable (fun x : Space => etaD l gs s c ‖x‖) := by
  have hi : LocallyIntegrable (fun x : Space => (sigmaAt gs (radius c ‖x‖) : ℂ)) := by
    simp_rw [sigma_select]
    exact select_comp_locallyIntegrable volume gs _ _ _
      ((radius_continuous c).comp continuous_norm).measurable
      (fun _ => continuous_const.locallyIntegrable) continuous_const.locallyIntegrable
  have hq : Continuous (fun x : Space => quotient (l+1) (momentum l gs s c) c ‖x‖) :=
    (quotient_continuous (l+1) _ (state_continuous l h s c).snd c hc).comp continuous_norm
  have hv : Continuous (fun x : Space => quotient (l+2) (value l gs s c) c ‖x‖) :=
    (quotient_continuous (l+2) _ (state_continuous l h s c).fst c hc).comp continuous_norm
  have ht : LocallyIntegrable (fun x : Space =>
      (sigmaAt gs (radius c ‖x‖) : ℂ)*quotient (l+1) (momentum l gs s c) c ‖x‖-
        (l+1 : ℂ)*quotient (l+2) (value l gs s c) c ‖x‖) :=
    (RadialInterface.locallyIntegrable_mul_continuous _ _ hi hq).sub
    ((continuous_const.mul hv).locallyIntegrable)
  exact ht.indicator (measurableSet_lt measurable_const continuous_norm.measurable)

theorem eta_hasDerivAt (l : ℕ) (gs : List Layer) (s : State) (c r : ℝ) (hc : 0<c)
    (hrc : r≠c) (hr : r∉cuts gs) : HasDerivAt (eta l gs s c) (etaD l gs s c r) r := by
  rcases lt_or_gt_of_ne hrc with hlt|hgt
  · have he : eta l gs s c =ᶠ[𝓝 r] fun _ => (profile l gs s c).1/(c : ℂ)^(l+1) := by
      filter_upwards [Iio_mem_nhds hlt] with t ht
      simp only [eta,quotient,value,state,radius,max_eq_left (show t≤c from le_of_lt ht)]
    simpa only [etaD,if_neg (not_lt.mpr hlt.le)] using
      (hasDerivAt_const r ((profile l gs s c).1/(c : ℂ)^(l+1))).congr_of_eventuallyEq he
  · have he : eta l gs s c =ᶠ[𝓝 r] fun t => (profile l gs s t).1/(t : ℂ)^(l+1) := by
      filter_upwards [Ioi_mem_nhds hgt] with t ht
      simp only [eta,quotient,value,state,radius,max_eq_right (show c≤t from le_of_lt ht)]
    have hd := RadialQuotient.profile_hasDerivAt l (fun t => (profile l gs s t).1)
      (fun t => (sigmaAt gs t : ℂ)*(profile l gs s t).2) r (hc.trans hgt).ne'
      (profile_hasDerivAt l gs s r hr).1
    convert hd.congr_of_eventuallyEq he using 1
    simp only [etaD,if_pos hgt,quotient,value,momentum,state,radius,max_eq_right hgt.le,
      RadialQuotient.profileD,Nat.cast_add,Nat.cast_one]
    ring

theorem angular_smooth (p : Poly) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => DebyeRadialTrace.angularToroidal p x j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hd (i : Fin 3) := ExteriorClassical.partial_smooth (x := x) (complexEvaluate_regular p).contDiffAt i
  have hx (i : Fin 3) : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => (y i : ℂ)) x :=
    (Maxwell.coordinate i).contDiff.contDiffAt
  fin_cases j <;> dsimp [DebyeRadialTrace.angularToroidal]
  · exact ((hd 1).mul (hx 2)).sub ((hd 2).mul (hx 1))
  · exact ((hd 2).mul (hx 0)).sub ((hd 0).mul (hx 2))
  · exact ((hd 0).mul (hx 1)).sub ((hd 1).mul (hx 0))

theorem magnetic_weak_curl (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (c k : ℝ) (hc : 0<c) (p : Poly)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) :
    weakCurlPairing (LayerElectricMaxwell.magnetic l gs s c k p) φ=
      fun j => ∫ x,curl (LayerElectricMaxwell.magnetic l gs s c k p) x j*φ x := by
  let S : Set ℝ := {c} ∪ {r | r∈cuts gs}
  have he : {r : ℝ | r∈cuts gs}=(cuts gs).toFinset := by ext r; simp
  have hS : S.Countable := Set.Countable.union (Set.countable_singleton c)
    (he ▸ (List.toFinset (cuts gs)).finite_toSet.countable)
  have hcut (r : ℝ) (hr : r∉S) : r≠c ∧ r∉cuts gs := by
    simpa only [S,mem_union,mem_singleton_iff,mem_setOf_eq,not_or] using hr
  exact RadialMultiplierWeak.weak_curl
    (fun r => (-Complex.I*(k : ℂ))*eta l gs s c r)
    (fun r => (-Complex.I*(k : ℂ))*etaD l gs s c r)
    (DebyeRadialTrace.angularToroidal p) S hS
    (continuous_const.mul (eta_continuous l h s c hc))
    (fun j => (angular_smooth p j).of_le (by simp))
    (by
      have hi := RadialInterface.locallyIntegrable_mul_continuous _ _
        (etaD_locallyIntegrable l h s c hc)
        (show Continuous (fun _ : Space => -Complex.I*(k : ℂ)) from continuous_const)
      simpa only [mul_comm] using hi)
    (fun r _ hr => (eta_hasDerivAt l gs s c r hc (hcut r hr).1 (hcut r hr).2).const_mul _)
    φ hφ hcompact

end OQ14.LayerMagneticProfiles

#print axioms OQ14.LayerMagneticProfiles.eta_continuous
#print axioms OQ14.LayerMagneticProfiles.sigma_select
#print axioms OQ14.LayerMagneticProfiles.etaD_locallyIntegrable
#print axioms OQ14.LayerMagneticProfiles.eta_hasDerivAt
#print axioms OQ14.LayerMagneticProfiles.angular_smooth
#print axioms OQ14.LayerMagneticProfiles.magnetic_weak_curl
