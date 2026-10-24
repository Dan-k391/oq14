import RadialFlux

/-! Radial Poynting flux of a global weak Maxwell solution with real bounded permittivity:
the flux vanishes for almost every radius. The identity comes from `testMaxwell_power` with
radial tests `x ↦ θ(‖x‖^2)`, polar coordinates, and a du Bois-Reymond type argument. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.LosslessSphereFluxConstancy

open MeasureTheory Metric Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.FarFieldPower OQ14.RadialPowerTest OQ14.WeakConservation OQ14.RadialFlux
open scoped Topology ENNReal

/-- Radial weight `2 r θ'(r^2)` of the test `x ↦ θ(‖x‖^2)`. -/
def profile (θ : ℝ → ℝ) (r : ℝ) : ℝ := 2*r*deriv θ (r^2)

theorem ray_testPower_radial (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ) (T : ℝ) (hT : 0 ≤ T)
    (hz : ∀ q, T^2 ≤ q → θ q=0) (E H : Field) (r : ℝ) (hr : 0<r) (n : Sphere) :
    r^2 * testPower (radialTest θ hθ T hT hz) E H (r • (n : Space)) =
      profile θ r * (r^2 * radialPower (n : Space) (E (r • (n : Space))) (H (r • (n : Space)))) := by
  rw [radial_testPower]
  have hn : ‖r • (n : Space)‖=r := by
    simp [norm_smul,sphere_norm,abs_of_pos hr]
  have hd := MaxwellFarField.ray_direction (n : Space) (sphere_norm n) r hr
  simp only [hn,radialPower,hd,profile]
  ring

theorem weak_radial (k : ℝ) (ε : Space → ℝ) (hε : Measurable ε) (M : ℝ) (hb : ∀ x,‖ε x‖ ≤ M)
    (E H : Field)
    (hE : ∀ T i,MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i,MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell k ε E H)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ) (T : ℝ) (hT : 0 ≤ T) (hz : ∀ q, T^2 ≤ q → θ q=0) :
    IntegrableOn (fun r => profile θ r * flux E H r) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi 0, profile θ r * flux E H r)=0 := by
  obtain ⟨hi,hz'⟩ := MaterialPower.testMaxwell_power k ε hε M hb E H hE hH hMax
    (radial θ) (radial_regular θ hθ) (radial_compact θ T hT hz)
  have hi' : Integrable (testPower (radialTest θ hθ T hT hz) E H) := hi
  have hz'' : (∫ x,testPower (radialTest θ hθ T hT hz) E H x)=0 := hz'
  have he (r : ℝ) (hr : r∈Set.Ioi (0 : ℝ)) :
      r^2 * (∫ n : Sphere,testPower (radialTest θ hθ T hT hz) E H (r • (n : Space)) ∂angularMeasure) =
        profile θ r * flux E H r := by
    rw [←integral_const_mul]
    simp_rw [ray_testPower_radial θ hθ T hT hz E H r hr]
    rw [integral_const_mul]
    rfl
  have hin := (integrable_polar _ hi').congr_fun he measurableSet_Ioi
  refine ⟨hin,?_⟩
  rw [PolarIntegration.integral_polar _ hi'] at hz''
  rw [←setIntegral_congr_fun (μ := (volume : Measure ℝ)) measurableSet_Ioi he]
  exact hz''

/-- `g(√s)/(2√s)`, the derivative profile reproducing the radial weight `g`. -/
def tildeG (g : ℝ → ℝ) (s : ℝ) : ℝ := g (Real.sqrt s)/(2*Real.sqrt s)

def thetaG (g : ℝ → ℝ) (T : ℝ) (q : ℝ) : ℝ := ∫ t in (T^2)..q,tildeG g t

theorem tildeG_continuous (g : ℝ → ℝ) (hg : Continuous g) (δ : ℝ) (hδ : 0<δ)
    (h0 : ∀ r,r<δ → g r=0) : Continuous (tildeG g) := by
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : 0<s
  · have hq : 0<Real.sqrt s := Real.sqrt_pos.mpr hs
    exact ((hg.comp Real.continuous_sqrt).continuousAt).div
      (continuous_const.mul Real.continuous_sqrt).continuousAt (by positivity)
  · have hs' : s<δ^2 := by nlinarith [not_lt.mp hs]
    have hev : tildeG g =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hs'] with t ht
      simp only [Set.mem_Iio] at ht
      unfold tildeG
      by_cases ht0 : t ≤ 0
      · rw [Real.sqrt_eq_zero_of_nonpos ht0]
        simp
      · have : Real.sqrt t<δ := by
          rw [Real.sqrt_lt' hδ]
          exact ht
        rw [h0 _ this]
        simp
    exact continuousAt_const.congr hev.symm

theorem thetaG_hasDerivAt (g : ℝ → ℝ) (hc : Continuous (tildeG g)) (T q : ℝ) :
    HasDerivAt (thetaG g T) (tildeG g q) q :=
  (hc.integral_hasStrictDerivAt (T^2) q).hasDerivAt

theorem thetaG_regular (g : ℝ → ℝ) (hc : Continuous (tildeG g)) (T : ℝ) :
    ContDiff ℝ 1 (thetaG g T) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun q => (thetaG_hasDerivAt g hc T q).differentiableAt,?_⟩
  have : deriv (thetaG g T)=tildeG g := funext fun q => (thetaG_hasDerivAt g hc T q).deriv
  rw [this]
  exact hc

theorem thetaG_zero (g : ℝ → ℝ) (T : ℝ) (hz : ∀ r,T ≤ r → g r=0) (q : ℝ)
    (hq : T^2 ≤ q) : thetaG g T q=0 := by
  unfold thetaG
  have : ∀ t∈Set.uIcc (T^2) q,tildeG g t=0 := by
    intro t ht
    rw [Set.uIcc_of_le hq] at ht
    have hTt : T ≤ Real.sqrt t := Real.le_sqrt_of_sq_le ht.1
    unfold tildeG
    rw [hz _ hTt]
    simp
  rw [intervalIntegral.integral_congr this]
  simp

theorem profile_thetaG (g : ℝ → ℝ) (hc : Continuous (tildeG g)) (T r : ℝ) (hr : 0<r) :
    profile (thetaG g T) r=g r := by
  unfold profile
  rw [(thetaG_hasDerivAt g hc T (r^2)).deriv]
  unfold tildeG
  rw [Real.sqrt_sq hr.le]
  field_simp

/-- Weak form against every continuous compactly supported weight vanishing near `0`. -/
theorem weak_smooth (k : ℝ) (ε : Space → ℝ) (hε : Measurable ε) (M : ℝ) (hb : ∀ x,‖ε x‖ ≤ M)
    (E H : Field)
    (hE : ∀ T i,MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i,MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell k ε E H)
    (g : ℝ → ℝ) (hg : Continuous g) (hc : HasCompactSupport g) (hs : tsupport g ⊆ Set.Ioi 0) :
    IntegrableOn (fun r => g r * flux E H r) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi 0, g r * flux E H r)=0 := by
  have hout : ∀ r : ℝ,r ∉ Set.Ioi 0 → g r=0 := fun r hr =>
    image_eq_zero_of_nmem_tsupport (fun h => hr (hs h))
  obtain ⟨T0,hT0⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  set T : ℝ := max T0 0+1 with hTdef
  have hT : 0 ≤ T := by positivity
  have hz : ∀ r,T ≤ r → g r=0 := by
    intro r hr
    apply image_eq_zero_of_nmem_tsupport
    intro h
    have := hT0 h
    rw [mem_closedBall,Real.dist_eq,sub_zero] at this
    have h1 := le_abs_self r
    have h2 : T0 ≤ max T0 0 := le_max_left _ _
    linarith
  have h0 : (0 : ℝ) ∉ tsupport g := fun h => absurd (hs h) (by simp)
  obtain ⟨δ,hδ,hδ0⟩ := Metric.eventually_nhds_iff.mp (not_mem_tsupport_iff_eventuallyEq.mp h0)
  have hδ' : ∀ r : ℝ,r<δ → g r=0 := by
    intro r hr
    by_cases hr0 : r ≤ 0
    · exact hout r (by simpa using hr0)
    · have := hδ0 (y := r) (by rw [Real.dist_eq,sub_zero,abs_of_pos (not_le.mp hr0)]; exact hr)
      simpa using this
  have hcont := tildeG_continuous g hg δ hδ hδ'
  obtain ⟨hi,hz'⟩ := weak_radial k ε hε M hb E H hE hH hMax (thetaG g T) (thetaG_regular g hcont T) T hT
    (fun q hq => thetaG_zero g T hz q hq)
  have he : ∀ r∈Set.Ioi (0 : ℝ),profile (thetaG g T) r * flux E H r=g r * flux E H r := by
    intro r hr
    rw [profile_thetaG g hcont T r hr]
  exact ⟨hi.congr_fun he measurableSet_Ioi,by rw [←setIntegral_congr_fun measurableSet_Ioi he]; exact hz'⟩

theorem flux_locallyIntegrableOn (k : ℝ) (ε : Space → ℝ) (hε : Measurable ε) (M : ℝ)
    (hb : ∀ x,‖ε x‖ ≤ M) (E H : Field)
    (hE : ∀ T i,MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i,MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell k ε E H) :
    LocallyIntegrableOn (flux E H) (Set.Ioi 0) volume := by
  intro x hx
  have hx' : 0<x := hx
  let b : ContDiffBump x := ⟨x/4,x/2,by positivity,by linarith⟩
  have hsub : tsupport b ⊆ Set.Ioi 0 := by
    rw [b.tsupport_eq]
    intro y hy
    rw [mem_closedBall,Real.dist_eq] at hy
    have := (abs_le.mp hy).1
    change 0<y
    have h2 : (b.rOut : ℝ)=x/2 := rfl
    linarith
  obtain ⟨hi,_⟩ := weak_smooth k ε hε M hb E H hE hH hMax b b.continuous b.hasCompactSupport hsub
  refine ⟨Set.Ioi 0 ∩ Metric.closedBall x (x/4),?_,?_⟩
  · exact inter_mem_nhdsWithin (Set.Ioi 0) (closedBall_mem_nhds x (by positivity))
  · have hsubset : Set.Ioi 0 ∩ Metric.closedBall x (x/4) ⊆ Set.Ioi 0 := Set.inter_subset_left
    refine (hi.mono_set hsubset).congr_fun ?_ (measurableSet_Ioi.inter measurableSet_closedBall)
    intro y hy
    have hb1 : b y=1 := b.one_of_mem_closedBall hy.2
    show b y * flux E H y=flux E H y
    rw [hb1,one_mul]

/-- The radial Poynting flux of a global weak Maxwell pair with real bounded permittivity vanishes
for almost every positive radius. -/
theorem flux_ae_zero (k : ℝ) (ε : Space → ℝ) (hε : Measurable ε) (M : ℝ) (hb : ∀ x,‖ε x‖ ≤ M)
    (E H : Field)
    (hE : ∀ T i,MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i,MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell k ε E H) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),flux E H r=0 := by
  have h := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := (volume : Measure ℝ))
    (f := flux E H) isOpen_Ioi (flux_locallyIntegrableOn k ε hε M hb E H hE hH hMax) (by
      intro g hg hc hs
      have hout : ∀ r : ℝ,r ∉ Set.Ioi 0 → g r * flux E H r=0 := fun r hr => by
        rw [image_eq_zero_of_nmem_tsupport (fun h => hr (hs h)),zero_mul]
      obtain ⟨_,hz⟩ := weak_smooth k ε hε M hb E H hE hH hMax g hg.continuous hc hs
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hout] at hz
      simpa only [smul_eq_mul] using hz)
  rw [ae_restrict_iff' measurableSet_Ioi]
  exact h

/-- Constancy of the flux beyond any radius `R0 ≥ 0`: the constant is zero. -/
theorem flux_ae_constant (k : ℝ) (ε : Space → ℝ) (hε : Measurable ε) (M : ℝ) (hb : ∀ x,‖ε x‖ ≤ M)
    (E H : Field)
    (hE : ∀ T i,MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i,MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell k ε E H) (R0 : ℝ) (hR0 : 0 ≤ R0) :
    ∃ P : ℝ,∀ᵐ r ∂(volume.restrict (Set.Ioi R0)),flux E H r=P :=
  ⟨0,ae_restrict_of_ae_restrict_of_subset (Set.Ioi_subset_Ioi hR0)
    (flux_ae_zero k ε hε M hb E H hE hH hMax)⟩

end OQ14.LosslessSphereFluxConstancy
#print axioms OQ14.LosslessSphereFluxConstancy.ray_testPower_radial
#print axioms OQ14.LosslessSphereFluxConstancy.weak_radial
#print axioms OQ14.LosslessSphereFluxConstancy.tildeG_continuous
#print axioms OQ14.LosslessSphereFluxConstancy.thetaG_regular
#print axioms OQ14.LosslessSphereFluxConstancy.thetaG_zero
#print axioms OQ14.LosslessSphereFluxConstancy.profile_thetaG
#print axioms OQ14.LosslessSphereFluxConstancy.weak_smooth
#print axioms OQ14.LosslessSphereFluxConstancy.flux_locallyIntegrableOn
#print axioms OQ14.LosslessSphereFluxConstancy.flux_ae_zero
#print axioms OQ14.LosslessSphereFluxConstancy.flux_ae_constant
