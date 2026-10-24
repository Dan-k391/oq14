import SourceRadiatedSeries
import ExteriorGreen
import ExteriorClassical
import CompactTestUniformLimit
import UniformHelmholtzEquation
import TEFiniteCalculus
import ExteriorSmooth

/-! The magnetic analogue of the mode-series representation of the radiated field.  A general theorem
passes the classical curl through uniform limits of smooth fields (through the distributional curl on
compactly supported smooth tests supported in an open set).  With the swapped uniform majorant of the
magnetic dyad series this identifies the free magnetic field of a compactly supported current density as
the series of its moments times the vacuum magnetic and TE magnetic modes.  The magnetic field of the shell
polarization of the shell mode solutions is identified outside the shell with the actual regular
corrections through the exterior Maxwell equations and the classical Maxwell equations of the layered
modes there; the free and shell parts add to the series of the moments times the actual layered TM
magnetic mode and the actual layered TE magnetic mode of the TE chain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.SourceRadiatedMagnetic
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.SphereHarmonicBasis
open OQ14.VectorHarmonicNormalization
open OQ14.OutgoingDyadBounds OQ14.OutgoingGeometricTail OQ14.AngularExteriorBounds
open scoped Topology

/-! ### Classical curl from the distributional curl, locally, and curl of uniform limits -/

theorem dcoord_eq_zero_of_not_tsupport (φ : Space → ℂ) (x : Space) (hx : x ∉ tsupport φ) (a : Fin 3) :
    dcoord φ x a = 0 := by
  have h := ExteriorGreen.zero_nhds_of_not_tsupport hx
  unfold dcoord
  rw [h.fderiv_eq]
  simp

theorem tsupport_dcoord_subset (φ : Space → ℂ) (a : Fin 3) :
    tsupport (fun x => dcoord φ x a) ⊆ tsupport φ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  exact hx (dcoord_eq_zero_of_not_tsupport φ x hn a)

/-- Local integration by parts: for a field smooth on an open set and a test function supported in it. -/
theorem local_curl_ibp {Ω : Set Space} (hΩ : IsOpen Ω) (F : Field)
    (hF : ∀ x ∈ Ω, ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F y j) x)
    (φ : Space → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (fun j => ∫ x, curl F x j * φ x) = weakCurlPairing F φ := by
  choose g hg hgc he using fun j : Fin 3 =>
    ExteriorGreen.smooth_localization hΩ hc hs (fun y => F y j) (fun x hx => hF x hx j)
  let G : Field := fun y j => g j y
  have hG : ∀ j, ContDiff ℝ 1 (fun x => G x j) := fun j => (hg j).of_le (by simp)
  have hmain := curl_integration_by_parts G hG (hφ.of_le (by simp)) hc
  have hcurl : ∀ x ∈ tsupport φ, curl F x = curl G x := by
    intro x hx
    have hev : G =ᶠ[𝓝 x] F := by
      have := Filter.eventually_all.2 (fun j : Fin 3 => (he j x hx))
      filter_upwards [this] with y hy
      funext j
      exact hy j
    exact (ExteriorClassical.curl_congr_nhds hev.symm)
  have hint : (fun j => ∫ x, curl F x j * φ x) = fun j => ∫ x, curl G x j * φ x := by
    funext j
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport φ
    · rw [hcurl x hx]
    · rw [image_eq_zero_of_nmem_tsupport hx]
      simp
  have hweak : weakCurlPairing F φ = weakCurlPairing G φ := by
    have hpt : ∀ (k a : Fin 3) (x : Space), F x k * dcoord φ x a = G x k * dcoord φ x a := by
      intro k a x
      by_cases hx : x ∈ tsupport φ
      · have : g k x = F x k := (he k x hx).eq_of_nhds
        change F x k * _ = g k x * _
        rw [this]
      · rw [dcoord_eq_zero_of_not_tsupport φ x hx a]
        simp
    unfold weakCurlPairing
    ext j
    fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, hpt]
  rw [hint, hmain, hweak]

/-- A field smooth on an open set whose distributional curl against every test function supported there
is the integral of `I G`, with `G` continuous, satisfies `curl F = I G` pointwise there. -/
theorem curl_eq_of_weak {Ω : Set Space} (hΩ : IsOpen Ω) (F G : Field)
    (hF : ∀ x ∈ Ω, ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F y j) x)
    (hG : ∀ j, ContinuousOn (fun y => G y j) Ω)
    (hw : ∀ φ : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      weakCurlPairing F φ = fun j => ∫ x, (Complex.I * G x j) * φ x) :
    ∀ x ∈ Ω, curl F x = fun j => Complex.I * G x j := by
  have hcurl (j : Fin 3) : ContinuousOn (fun y => curl F y j) Ω := fun y hy =>
    ((ExteriorClassical.curl_smooth F (fun k => hF y hy k) j).continuousAt).continuousWithinAt
  have hD (j : Fin 3) : ContinuousOn (fun y => curl F y j - Complex.I * G y j) Ω :=
    (hcurl j).sub (continuousOn_const.mul (hG j))
  have hzero (j : Fin 3) : ∀ y ∈ Ω, curl F y j - Complex.I * G y j = 0 := by
    have hae : ∀ᵐ y ∂volume, y ∈ Ω → curl F y j - Complex.I * G y j = 0 :=
      hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((hD j).locallyIntegrableOn hΩ.measurableSet) (by
          intro η hη hc hs
          let φ : Space → ℂ := fun y => (η y : ℂ)
          have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := Complex.ofRealCLM.contDiff.comp hη
          have hcφ : HasCompactSupport φ := hc.comp_left (g := Complex.ofReal) (by simp)
          have hsφ : tsupport φ ⊆ Ω := by
            have he : tsupport φ = tsupport η := by
              apply congrArg closure
              ext y
              exact not_congr Complex.ofReal_eq_zero
            rwa [he]
          have h1 := congrFun (local_curl_ibp hΩ F hF φ hφ hcφ hsφ) j
          have h2 := congrFun (hw φ hφ hcφ hsφ) j
          have h3 : ∫ x, curl F x j * φ x = ∫ x, (Complex.I * G x j) * φ x := by rw [h1, h2]
          have hi1 : Integrable (fun x => curl F x j * φ x) := by
            have hl : IntegrableOn (fun x => curl F x j * φ x) (tsupport φ) := by
              apply ContinuousOn.integrableOn_compact hcφ
              exact ((hcurl j).mono hsφ).mul hφ.continuous.continuousOn
            exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport _ |>.trans' (by
              intro x hx
              exact fun h => hx (by simp [h]))) |>.mp hl)
          have hi2 : Integrable (fun x => (Complex.I * G x j) * φ x) := by
            have hl : IntegrableOn (fun x => (Complex.I * G x j) * φ x) (tsupport φ) := by
              apply ContinuousOn.integrableOn_compact hcφ
              exact ((continuousOn_const.mul ((hG j).mono hsφ))).mul hφ.continuous.continuousOn
            exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport _ |>.trans' (by
              intro x hx
              exact fun h => hx (by simp [h]))) |>.mp hl)
          have : ∫ x, η x • (curl F x j - Complex.I * G x j) = 0 := by
            have e : (fun x => η x • (curl F x j - Complex.I * G x j)) =
                fun x => curl F x j * φ x - (Complex.I * G x j) * φ x := by
              funext x
              simp only [Complex.real_smul, φ]
              ring
            rw [e, integral_sub hi1 hi2, h3, sub_self]
          exact this)
    have hae' : (fun y => curl F y j - Complex.I * G y j) =ᵐ[volume.restrict Ω] 0 :=
      (ae_restrict_iff' hΩ.measurableSet).mpr hae
    exact fun y hy => Measure.eqOn_open_of_ae_eq hae' hΩ (hD j) continuousOn_const hy
  intro x hx
  funext j
  exact sub_eq_zero.mp (hzero j x hx)

/-- The distributional curl pairing passes to uniform limits on the support of the test function. -/
theorem pairing_tendsto {ι : Type*} (l : Filter ι) {Ω : Set Space} (hΩ : IsOpen Ω)
    (S : ι → Field) (F : Field)
    (hSc : ∀ n j, ContinuousOn (fun y => S n y j) Ω) (hFc : ∀ j, ContinuousOn (fun y => F y j) Ω)
    (φ : Space → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω)
    (hlim : ∀ j, TendstoUniformlyOn (fun n y => S n y j) (fun y => F y j) l (tsupport φ)) (j : Fin 3) :
    Tendsto (fun n => weakCurlPairing (S n) φ j) l (𝓝 (weakCurlPairing F φ j)) := by
  have hq (a : Fin 3) : Continuous (fun x => dcoord φ x a) := by
    unfold dcoord
    exact ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hqc (a : Fin 3) : HasCompactSupport (fun x => dcoord φ x a) := hc.fderiv_apply ℝ (basis a)
  have hqs (a : Fin 3) : tsupport (fun x => dcoord φ x a) ⊆ Ω := (tsupport_dcoord_subset φ a).trans hs
  have hT (k a : Fin 3) : Tendsto (fun n => ∫ y, S n y k * dcoord φ y a) l
      (𝓝 (∫ y, F y k * dcoord φ y a)) :=
    CompactTestUniformLimit.integral_mul_tendsto l Ω hΩ (fun n y => S n y k) (fun y => F y k)
      (fun y => dcoord φ y a) (hSc · k) (hFc k) (hq a) (hqc a) (hqs a)
      ((hlim k).mono (tsupport_dcoord_subset φ a))
  unfold weakCurlPairing
  fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  · exact (hT 1 2).sub (hT 2 1)
  · exact (hT 2 0).sub (hT 0 2)
  · exact (hT 0 1).sub (hT 1 0)

/-- **Curl of a uniform limit.**  If smooth fields `S n` satisfy `curl (S n) = I T n` on an open set and
converge uniformly there together with `T n`, then the limit field `F` (smooth there) satisfies
`curl F = I G` for the limit `G` of the `T n`. -/
theorem curl_limit {ι : Type*} (l : Filter ι) [NeBot l] {Ω : Set Space} (hΩ : IsOpen Ω)
    (S T : ι → Field) (F G : Field)
    (hS : ∀ n, ∀ x ∈ Ω, ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => S n y j) x)
    (hMax : ∀ n, ∀ x ∈ Ω, curl (S n) x = fun j => Complex.I * T n x j)
    (hTc : ∀ n j, ContinuousOn (fun y => T n y j) Ω)
    (hF : ∀ x ∈ Ω, ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => F y j) x)
    (hlimS : ∀ j, TendstoUniformlyOn (fun n y => S n y j) (fun y => F y j) l Ω)
    (hlimT : ∀ j, TendstoUniformlyOn (fun n y => T n y j) (fun y => G y j) l Ω) :
    ∀ x ∈ Ω, curl F x = fun j => Complex.I * G x j := by
  have hSc (n : ι) (j : Fin 3) : ContinuousOn (fun y => S n y j) Ω := fun y hy =>
    (hS n y hy j).continuousAt.continuousWithinAt
  have hFc (j : Fin 3) : ContinuousOn (fun y => F y j) Ω := fun y hy =>
    (hF y hy j).continuousAt.continuousWithinAt
  have hGc (j : Fin 3) : ContinuousOn (fun y => G y j) Ω :=
    (hlimT j).continuousOn (Eventually.of_forall (hTc · j))
  refine curl_eq_of_weak hΩ F G hF hGc ?_
  intro φ hφ hc hs
  funext j
  have h1 := pairing_tendsto l hΩ S F hSc hFc φ hφ hc hs (fun k => (hlimS k).mono hs) j
  have hu : UniformContinuous (fun z : ℂ => Complex.I * z) :=
    (ContinuousLinearMap.mul ℂ ℂ Complex.I).uniformContinuous
  have h2 : Tendsto (fun n => ∫ x, (Complex.I * T n x j) * φ x) l
      (𝓝 (∫ x, (Complex.I * G x j) * φ x)) :=
    CompactTestUniformLimit.integral_mul_tendsto l Ω hΩ (fun n y => Complex.I * T n y j)
      (fun y => Complex.I * G y j) φ (fun n => continuousOn_const.mul (hTc n j))
      (continuousOn_const.mul (hGc j)) hφ.continuous hc hs
      (hu.comp_tendstoUniformlyOn ((hlimT j).mono hs))
  have h3 : ∀ n, weakCurlPairing (S n) φ j = ∫ x, (Complex.I * T n x j) * φ x := by
    intro n
    rw [← congrFun (local_curl_ibp hΩ (S n) (hS n) φ hφ hc hs) j]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport φ
    · rw [hMax n x (hs hx)]
    · rw [image_eq_zero_of_nmem_tsupport hx]
      simp
  exact tendsto_nhds_unique (h1.congr h3) h2

/-! ### Classical Maxwell equations of the vacuum outgoing modes -/

theorem vacuum_sigma (l : ℕ) (r : ℝ) : SourceRadialSystem.sigma (VacuumOutgoingBounds.data l) r = 1 := by
  simp [SourceRadialSystem.sigma, SourceRadialSystem.extend, RadialGluing.sigmaAt,
    VacuumOutgoingBounds.data]

theorem vacuum_hdisp (l : ℕ) :
    ∀ g ∈ (VacuumOutgoingBounds.data l).gs, g.q^2 = g.σ := by
  intro g hg
  exact (List.not_mem_nil hg).elim

/-- The vacuum TM mode satisfies the first Maxwell equation classically away from the origin. -/
theorem vacuum_tm_curl (l : ℕ) (m : Index l) (x : Space) (hx : x ≠ 0) :
    curl (SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l) (representative l m)) x =
      fun j => Complex.I * SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data l)
        (representative l m) x j := by
  have hΩ : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  refine curl_eq_of_weak hΩ _ _ ?_ ?_ ?_ x hx
  · intro y hy j
    exact VacuumOutgoingHelmholtz.electric_smooth l _ (representative_homogeneous l m)
      (representative_harmonic l m) y hy j
  · intro j y hy
    exact (VacuumOutgoingHelmholtz.magnetic_smooth l _ y hy j).continuousAt.continuousWithinAt
  · intro φ hφ hc hs
    have h0 : (0 : Space) ∉ tsupport φ := fun h => hs h rfl
    exact SourceUnclippedMaxwell.first_weak_maxwell (VacuumOutgoingBounds.data l) (vacuum_hdisp l) _ φ
      (hφ.of_le (by norm_cast)) hc h0

/-- The vacuum magnetic profile satisfies the second Maxwell equation classically away from the origin. -/
theorem vacuum_te_curl (l : ℕ) (m : Index l) (x : Space) (hx : x ≠ 0) :
    curl (SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data l) (representative l m)) x =
      fun j => Complex.I * (-SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l)
        (representative l m) x j) := by
  have hΩ : IsOpen {y : Space | y ≠ 0} := isOpen_ne
  refine curl_eq_of_weak hΩ _ (fun y j => -SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l)
    (representative l m) y j) ?_ ?_ ?_ x hx
  · intro y hy j
    exact VacuumOutgoingHelmholtz.magnetic_smooth l _ y hy j
  · intro j y hy
    exact (VacuumOutgoingHelmholtz.electric_smooth l _ (representative_homogeneous l m)
      (representative_harmonic l m) y hy j).continuousAt.continuousWithinAt.neg
  · intro φ hφ hc hs
    have h0 : (0 : Space) ∉ tsupport φ := fun h => hs h rfl
    rw [SourceUnclippedMaxwell.second_weak_maxwell (VacuumOutgoingBounds.data l) _
      (representative_homogeneous l m) (representative_harmonic l m) φ (hφ.of_le (by norm_cast)) hc h0]
    funext j
    apply integral_congr_ae
    filter_upwards with y
    rw [vacuum_sigma]
    ring

/-! ### The magnetic dyad series: the swapped uniform majorant -/

/-- The magnetic term of the free dyad series of degree `a.1+1` at `x` for the dipole at `y`:
the TM coefficient times the vacuum magnetic profile plus the TE coefficient times the TE magnetic
profile, which is minus the vacuum electric profile. -/
def mterm (a : PositiveIndex) (x y : Space) (i j : Fin 3) : ℂ :=
  FreeSourceCoefficients.tmCoefficient a y j * SourceUnclippedMaxwell.magnetic
      (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
    FreeSourceCoefficients.teCoefficient a y j * (-SourceUnclippedMaxwell.electric
      (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i)

def tmMagWeighted (a : PositiveIndex) (r : ℝ) (n : Sphere) (y : Space) (i j : Fin 3) : ℂ :=
  FreeSourceCoefficients.tmCoefficient a y j * SourceFarAmplitude.magneticWeighted
    (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) (r • (n : Space)) i

def teElWeighted (a : PositiveIndex) (r : ℝ) (n : Sphere) (y : Space) (i j : Fin 3) : ℂ :=
  FreeSourceCoefficients.teCoefficient a y j * (-SourceFarAmplitude.electricWeighted
    (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) (r • (n : Space)) i)

theorem tm_mag_radial_bound (a : PositiveIndex) (b B r : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hr : 1 < r)
    (n : Sphere) (y : Space) (hy : ‖y‖ ≤ b) (i j : Fin 3) :
    ‖tmMagWeighted a r n y i j‖ ≤ 2*DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*
      (a.1+2 : ℝ)^6*(RiccatiSeriesCoefficients.amplitude (a.1+1) 0*(B*base)^(a.1+1)*
        ‖ModalAlgebra.xi (a.1+1) r‖) := by
  have hreg := (regular_coefficient_bound a b B hb hB hscale y hy j).1
  have hout := VacuumOutgoingBounds.magnetic_weighted_bound (a.1+1) a.2 n r hr i
  rw [tmMagWeighted, norm_mul]
  apply (mul_le_mul hreg hout (norm_nonneg _) (by
    have h := DebyeJetBounds.scale_nonnegative 0 b hb
    have h' := (RiccatiSeriesCoefficients.amplitude_pos (a.1+1) 0).le
    positivity)).trans_eq
  simp only [envelope, Nat.cast_add, Nat.cast_one, mul_pow]
  ring

theorem te_el_radial_bound (a : PositiveIndex) (b B r : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hr : 1 < r)
    (n : Sphere) (y : Space) (hy : ‖y‖ ≤ b) (i j : Fin 3) :
    ‖teElWeighted a r n y i j‖ ≤ DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*
      (a.1+2 : ℝ)^8*(RiccatiSeriesCoefficients.amplitude (a.1+1) 0*(B*base)^(a.1+1)*
        (‖ModalAlgebra.xiD (a.1+1) r‖+‖ModalAlgebra.xi (a.1+1) r‖)) := by
  have hreg := (regular_coefficient_bound a b B hb hB hscale y hy j).2
  have hout := VacuumOutgoingBounds.electric_weighted_bound (a.1+1) a.2 n r hr i
  rw [teElWeighted, norm_mul, norm_neg]
  apply (mul_le_mul hreg hout (norm_nonneg _) (by
    have h := DebyeJetBounds.scale_nonnegative 0 b hb
    have h' := (RiccatiSeriesCoefficients.amplitude_pos (a.1+1) 0).le
    positivity)).trans_eq
  simp only [envelope, Nat.cast_add, Nat.cast_one, mul_pow]
  ring

theorem mag_uniform_bound (a : PositiveIndex) (b B R r : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*base) ≤ R) (hr : R ≤ r)
    (n : Sphere) (y : Space) (hy : ‖y‖ ≤ b) (i j : Fin 3) :
    ‖tmMagWeighted a r n y i j + teElWeighted a r n y i j‖ ≤ majorant b R a := by
  have hbase : 0 ≤ base := by dsimp [base, HarmonicSpatialMajorant.angularScale]; positivity
  have hC := DebyeJetBounds.scale_nonnegative 0 b hb
  have hS : 0 ≤ AngularExteriorBounds.scale := by
    dsimp [AngularExteriorBounds.scale, HarmonicSpatialMajorant.areaScale]; positivity
  have hrad := HankelExteriorBounds.regular_outgoing_geometric (a.1+1) (B*base) R r
    (mul_nonneg hB hbase) (by linarith) hBR hr
  have ht := tm_mag_radial_bound a b B r hb hB hscale (by linarith) n y hy i j
  have he := te_el_radial_bound a b B r hb hB hscale (by linarith) n y hy i j
  have ht' : ‖tmMagWeighted a r n y i j‖ ≤
      2*DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*(a.1+2 : ℝ)^8*Real.exp R*
        (1/2 : ℝ)^(a.1+1) := by
    apply ht.trans
    apply le_trans (mul_le_mul_of_nonneg_left hrad.1 (by positivity))
    have hp : (a.1+2 : ℝ)^6 ≤ (a.1+2 : ℝ)^8 := by
      apply pow_le_pow_right₀ (by have h := Nat.cast_nonneg (α := ℝ) a.1; linarith)
      norm_num
    calc
      _ = (2*DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*Real.exp R*(1/2 : ℝ)^(a.1+1))*
          (a.1+2 : ℝ)^6 := by ring
      _ ≤ (2*DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*Real.exp R*(1/2 : ℝ)^(a.1+1))*
          (a.1+2 : ℝ)^8 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  have he' : ‖teElWeighted a r n y i j‖ ≤
      2*DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*(a.1+2 : ℝ)^8*Real.exp R*
        (1/2 : ℝ)^(a.1+1) := by
    apply he.trans
    calc
      _ = (DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*(a.1+2 : ℝ)^8)*
          (RiccatiSeriesCoefficients.amplitude (a.1+1) 0*(B*base)^(a.1+1)*‖ModalAlgebra.xiD (a.1+1) r‖+
           RiccatiSeriesCoefficients.amplitude (a.1+1) 0*(B*base)^(a.1+1)*‖ModalAlgebra.xi (a.1+1) r‖) := by
        ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left (add_le_add hrad.2 hrad.1) (by positivity)).trans_eq
        (by ring)
  exact (norm_add_le _ _).trans ((add_le_add ht' he').trans_eq
    (by dsimp [majorant, prefactor]; ring))

theorem mag_weighted_term (a : PositiveIndex) (r : ℝ) (n : Sphere) (y : Space) (i j : Fin 3) :
    OutgoingSpatialSeries.factor (r • (n : Space)) * mterm a (r • (n : Space)) y i j =
      tmMagWeighted a r n y i j + teElWeighted a r n y i j := by
  simp only [mterm, tmMagWeighted, teElWeighted, SourceFarAmplitude.electricWeighted,
    SourceFarAmplitude.magneticWeighted, Pi.smul_apply, smul_eq_mul, OutgoingSpatialSeries.factor,
    Pi.neg_apply]
  ring

theorem mterm_bound (a : PositiveIndex) (b B R : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R)
    (x y : Space) (hx : R ≤ ‖x‖) (hy : ‖y‖ ≤ b) (i j : Fin 3) :
    ‖mterm a x y i j‖ ≤ OutgoingGeometricTail.majorant b R a := by
  have hx0 : x ≠ 0 := by intro he; simp only [he, norm_zero] at hx; linarith
  have h := mag_uniform_bound a b B R ‖x‖ hb hB hscale hR hBR hx (OutgoingSpatialSeries.direction x hx0)
    y hy i j
  rw [← mag_weighted_term, OutgoingSpatialSeries.direction_ray, norm_mul,
    OutgoingSpatialSeries.factor_norm] at h
  exact (le_mul_of_one_le_left (norm_nonneg _) (by linarith : 1 ≤ ‖x‖)).trans h

/-! ### The moment-level series of the free electric and magnetic fields -/

/-- The electric moment term of the free-field series. -/
def Ft (ρ : Fin 3 → Space → ℂ) (a : PositiveIndex) (x : Space) (j : Fin 3) : ℂ :=
  SourceRadiatedSeries.tmMoment a ρ * SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data (a.1+1))
      (representative (a.1+1) a.2) x j +
    SourceRadiatedSeries.teMoment a ρ * SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data (a.1+1))
      (representative (a.1+1) a.2) x j

/-- The magnetic moment term of the free-field series. -/
def Gt (ρ : Fin 3 → Space → ℂ) (a : PositiveIndex) (x : Space) (j : Fin 3) : ℂ :=
  SourceRadiatedSeries.tmMoment a ρ * SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data (a.1+1))
      (representative (a.1+1) a.2) x j +
    SourceRadiatedSeries.teMoment a ρ * (-SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data (a.1+1))
      (representative (a.1+1) a.2) x j)

theorem integral_sum_norm_le (b : ℝ) (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (f : Space → Fin 3 → ℂ) (u : ℝ)
    (hf : ∀ y, ‖y‖ ≤ b → ∀ j, ‖f y j‖ ≤ u) :
    ‖∑ j, ∫ y, ρ j y * f y j‖ ≤ u * SourceRadiatedSeries.mass ρ := by
  unfold SourceRadiatedSeries.mass
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hρ j).norm.const_mul _) (Eventually.of_forall fun y => ?_)
  by_cases hy : ‖y‖ ≤ b
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hf y hy j) (norm_nonneg _)).trans_eq (by ring)
  · rw [hsupp j y (not_le.mp hy)]
    simp

theorem Ft_eq_integral (b : ℝ) (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (a : PositiveIndex) (x : Space) (i : Fin 3) :
    Ft ρ a x i = ∑ j, ∫ y, ρ j y * OutgoingSpatialSeries.term a x y i j := by
  unfold Ft SourceRadiatedSeries.tmMoment SourceRadiatedSeries.teMoment
  simp only [SourceRadiatedSeries.integral_term_split b ρ hρ hsupp a x i, Finset.sum_add_distrib,
    Finset.sum_mul]

theorem Gt_eq_integral (b : ℝ) (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (a : PositiveIndex) (x : Space) (i : Fin 3) :
    Gt ρ a x i = ∑ j, ∫ y, ρ j y * mterm a x y i j := by
  have h (j : Fin 3) : ∫ y, ρ j y * mterm a x y i j =
      (∫ y, FreeSourceCoefficients.tmCoefficient a y j * ρ j y) * SourceUnclippedMaxwell.magnetic
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
      (∫ y, FreeSourceCoefficients.teCoefficient a y j * ρ j y) * (-SourceUnclippedMaxwell.electric
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i) := by
    have h1 := SourceRadiatedSeries.coefficient_mul_integrable
      (SourceRadiatedSeries.tmCoefficient_continuous a j) (hρ j) b (hsupp j)
    have h2 := SourceRadiatedSeries.coefficient_mul_integrable
      (SourceRadiatedSeries.teCoefficient_continuous a j) (hρ j) b (hsupp j)
    have : (fun y => ρ j y * mterm a x y i j) =
        fun y => (FreeSourceCoefficients.tmCoefficient a y j * ρ j y) * SourceUnclippedMaxwell.magnetic
          (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
        (FreeSourceCoefficients.teCoefficient a y j * ρ j y) * (-SourceUnclippedMaxwell.electric
          (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i) := by
      funext y
      unfold mterm
      ring
    rw [this, integral_add (h1.mul_const _) (h2.mul_const _), integral_mul_const, integral_mul_const]
  unfold Gt SourceRadiatedSeries.tmMoment SourceRadiatedSeries.teMoment
  simp only [h, Finset.sum_add_distrib, Finset.sum_mul]

theorem Ft_bound (b B R : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (a : PositiveIndex) (x : Space) (hx : R ≤ ‖x‖) (i : Fin 3) :
    ‖Ft ρ a x i‖ ≤ OutgoingGeometricTail.majorant b R a * SourceRadiatedSeries.mass ρ := by
  rw [Ft_eq_integral b ρ hρ hsupp]
  exact integral_sum_norm_le b ρ hρ hsupp (fun y j => OutgoingSpatialSeries.term a x y i j) _
    (fun y hy j => OutgoingSpatialSeries.term_bound a b B R hb hB hscale hR hBR x y hx hy i j)

theorem Gt_bound (b B R : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (a : PositiveIndex) (x : Space) (hx : R ≤ ‖x‖) (i : Fin 3) :
    ‖Gt ρ a x i‖ ≤ OutgoingGeometricTail.majorant b R a * SourceRadiatedSeries.mass ρ := by
  rw [Gt_eq_integral b ρ hρ hsupp]
  exact integral_sum_norm_le b ρ hρ hsupp (fun y j => mterm a x y i j) _
    (fun y hy j => mterm_bound a b B R hb hB hscale hR hBR x y hx hy i j)

/-- The finite partial sum fields of the free electric series. -/
def partialE (ρ : Fin 3 → Space → ℂ) (s : Finset PositiveIndex) : Field :=
  fun x j => ∑ a ∈ s, Ft ρ a x j

/-- The finite partial sum fields of the free magnetic series. -/
def partialH (ρ : Fin 3 → Space → ℂ) (s : Finset PositiveIndex) : Field :=
  fun x j => ∑ a ∈ s, Gt ρ a x j

theorem partialE_smooth (ρ : Fin 3 → Space → ℂ) (s : Finset PositiveIndex) (x : Space) (hx : x ≠ 0)
    (j : Fin 3) : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => partialE ρ s y j) x := by
  unfold partialE Ft
  refine ContDiffAt.sum fun a _ => ?_
  exact (contDiffAt_const.mul (VacuumOutgoingHelmholtz.electric_smooth (a.1+1) _
    (representative_homogeneous _ _) (representative_harmonic _ _) x hx j)).add
    (contDiffAt_const.mul (VacuumOutgoingHelmholtz.magnetic_smooth (a.1+1) _ x hx j))

theorem partialH_smooth (ρ : Fin 3 → Space → ℂ) (s : Finset PositiveIndex) (x : Space) (hx : x ≠ 0)
    (j : Fin 3) : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => partialH ρ s y j) x := by
  unfold partialH Gt
  refine ContDiffAt.sum fun a _ => ?_
  exact (contDiffAt_const.mul (VacuumOutgoingHelmholtz.magnetic_smooth (a.1+1) _ x hx j)).add
    (contDiffAt_const.mul (VacuumOutgoingHelmholtz.electric_smooth (a.1+1) _
    (representative_homogeneous _ _) (representative_harmonic _ _) x hx j).neg)

theorem partial_curl (ρ : Fin 3 → Space → ℂ) (s : Finset PositiveIndex) (x : Space) (hx : x ≠ 0) :
    curl (partialE ρ s) x = fun j => Complex.I * partialH ρ s x j := by
  have hE (a : PositiveIndex) (j : Fin 3) : DifferentiableAt ℝ (fun y =>
      SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) y j) x :=
    (VacuumOutgoingHelmholtz.electric_smooth (a.1+1) _ (representative_homogeneous _ _)
      (representative_harmonic _ _) x hx j).differentiableAt (by simp)
  have hM (a : PositiveIndex) (j : Fin 3) : DifferentiableAt ℝ (fun y =>
      SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) y j) x :=
    (VacuumOutgoingHelmholtz.magnetic_smooth (a.1+1) _ x hx j).differentiableAt (by simp)
  have hsplit : partialE ρ s = fun y j =>
      (∑ a ∈ s, SourceRadiatedSeries.tmMoment a ρ * SourceUnclippedMaxwell.electric
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) y j) +
      (∑ a ∈ s, SourceRadiatedSeries.teMoment a ρ * SourceUnclippedMaxwell.magnetic
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) y j) := by
    funext y j
    unfold partialE Ft
    rw [Finset.sum_add_distrib]
  rw [hsplit]
  funext i
  have h1 := OQ14.TEFiniteCalculus.curl_sum s (fun a => SourceUnclippedMaxwell.electric
    (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2))
    (fun a => SourceRadiatedSeries.tmMoment a ρ) x (fun a _ j => hE a j) i
  have h2 := OQ14.TEFiniteCalculus.curl_sum s (fun a => SourceUnclippedMaxwell.magnetic
    (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2))
    (fun a => SourceRadiatedSeries.teMoment a ρ) x (fun a _ j => hM a j) i
  have hadd := curl_add
    (fun y j => ∑ a ∈ s, SourceRadiatedSeries.tmMoment a ρ * SourceUnclippedMaxwell.electric
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) y j)
    (fun y j => ∑ a ∈ s, SourceRadiatedSeries.teMoment a ρ * SourceUnclippedMaxwell.magnetic
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) y j) x
    (fun j => DifferentiableAt.sum fun a _ => (hE a j).const_mul _)
    (fun j => DifferentiableAt.sum fun a _ => (hM a j).const_mul _)
  rw [hadd]
  beta_reduce at h1 h2
  show curl _ x i + curl _ x i = _
  rw [h1, h2]
  unfold partialH Gt
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [congrFun (vacuum_tm_curl (a.1+1) a.2 x hx) i, congrFun (vacuum_te_curl (a.1+1) a.2 x hx) i]
  ring

/-- **The free magnetic field of a compactly supported current density as a vacuum mode series.**
Outside the support and the threshold radius, the magnetic field of the free source equals the series
over the positive degrees and real modes of the TM moment times the vacuum magnetic mode plus the TE
moment times the TE magnetic mode (minus the vacuum electric profile). -/
theorem free_magnetic_series_outside (b B T : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hT : 2 ≤ T)
    (hBT : 2*(B*AngularExteriorBounds.base) ≤ T)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (x : Space) (hx : max T b < ‖x‖) (i : Fin 3) :
    HasSum (fun a : PositiveIndex => Gt ρ a x i) (MagneticResponse.magnetic 1 ρ x i) := by
  have hΩ : IsOpen {y : Space | max T b < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hc : ∀ j y, y ∉ closedBall (0 : Space) b → ρ j y = 0 := fun j y hy =>
    hsupp j y (by rw [mem_closedBall, dist_zero_right, not_le] at hy; exact hy)
  have hmass := SourceRadiatedSeries.mass_nonneg ρ
  have hu : Summable (fun a : PositiveIndex => OutgoingGeometricTail.majorant b T a *
      SourceRadiatedSeries.mass ρ) := (OutgoingGeometricTail.majorant_summable b T hb).mul_right _
  have hne (y : Space) (hy : y ∈ {y : Space | max T b < ‖y‖}) : y ≠ 0 := by
    intro h0
    have : max T b < ‖y‖ := hy
    rw [h0, norm_zero] at this
    have := (le_max_left T b)
    linarith
  have hTy (y : Space) (hy : y ∈ {y : Space | max T b < ‖y‖}) : T ≤ ‖y‖ :=
    ((le_max_left T b).trans_lt hy).le
  have hlimS (j : Fin 3) : TendstoUniformlyOn (fun s y => partialE ρ s y j)
      (fun y => ExteriorContinuity.electric 1 ρ y j) atTop {y : Space | max T b < ‖y‖} := by
    have h := tendstoUniformlyOn_tsum (f := fun a y => Ft ρ a y j) hu (s := {y : Space | max T b < ‖y‖})
      (fun a y hy => Ft_bound b B T hb hB hscale hT hBT ρ hρ hsupp a y (hTy y hy) j)
    refine h.congr_right fun y hy => ?_
    exact (SourceRadiatedSeries.free_field_series_outside b B T hb hB hscale hT hBT ρ hρ hsupp y hy j).tsum_eq
  have hlimT (j : Fin 3) : TendstoUniformlyOn (fun s y => partialH ρ s y j)
      (fun y => ∑' a, Gt ρ a y j) atTop {y : Space | max T b < ‖y‖} :=
    tendstoUniformlyOn_tsum (f := fun a y => Gt ρ a y j) hu (s := {y : Space | max T b < ‖y‖})
      (fun a y hy => Gt_bound b B T hb hB hscale hT hBT ρ hρ hsupp a y (hTy y hy) j)
  have hcurl := curl_limit atTop hΩ (partialE ρ) (partialH ρ) (ExteriorContinuity.electric 1 ρ)
    (fun y j => ∑' a, Gt ρ a y j)
    (fun s y hy j => partialE_smooth ρ s y (hne y hy) j)
    (fun s y hy => partial_curl ρ s y (hne y hy))
    (fun s j y hy => (partialH_smooth ρ s y (hne y hy) j).continuousAt.continuousWithinAt)
    (fun y hy j => (contDiffAt_pi.mp (ExteriorSmooth.electric_contDiffAt 1 ρ hρ b hc y
      ((le_max_right T b).trans_lt hy))) j)
    hlimS hlimT x hx
  have hmax := (ExteriorClassical.exterior_maxwell 1 ρ hρ b hc x ((le_max_right T b).trans_lt hx)).1
  have hfin := congrFun (hcurl.symm.trans hmax) i
  have hHi : MagneticResponse.magnetic 1 ρ x i = ∑' a, Gt ρ a x i := by
    simp only [Complex.ofReal_one, mul_one] at hfin
    exact (mul_left_cancel₀ Complex.I_ne_zero hfin).symm
  rw [hHi]
  exact (Summable.of_norm_bounded _ hu (fun a => Gt_bound b B T hb hB hscale hT hBT ρ hρ hsupp a x
    (hTy x hx) i)).hasSum

/-! ### Classical Maxwell equations of the layered modes and of their regular corrections outside the shell -/

theorem curl_sub_field (A B : Field) (x : Space) (hA : ∀ j, DifferentiableAt ℝ (fun y => A y j) x)
    (hB : ∀ j, DifferentiableAt ℝ (fun y => B y j) x) :
    curl (fun y j => A y j - B y j) x = fun j => curl A x j - curl B x j := by
  have h := curl_add A (fun y j => (-1 : ℂ) * B y j) x hA (fun j => (hB j).const_mul _)
  have h2 := curl_const_mul B x (-1 : ℂ) hB
  have e : (fun y j => A y j - B y j) = fun y j => A y j + (-1 : ℂ) * B y j := by
    funext y j; ring
  rw [e, h, h2]
  funext j
  ring

theorem vacuum_electric_diff (l : ℕ) (m : Index l) (x : Space) (hx : x ≠ 0) (j : Fin 3) :
    DifferentiableAt ℝ (fun y => SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l)
      (representative l m) y j) x :=
  (VacuumOutgoingHelmholtz.electric_smooth l _ (representative_homogeneous l m)
    (representative_harmonic l m) x hx j).differentiableAt (by simp)

theorem vacuum_magnetic_diff (l : ℕ) (m : Index l) (x : Space) (hx : x ≠ 0) (j : Fin 3) :
    DifferentiableAt ℝ (fun y => SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data l)
      (representative l m) y j) x :=
  (VacuumOutgoingHelmholtz.magnetic_smooth l _ x hx j).differentiableAt (by simp)

theorem exterior_ne_zero (d : SourceRadialSystem.Data) (x : Space) (hx : d.X < ‖x‖) : x ≠ 0 := by
  intro h0
  rw [h0, norm_zero] at hx
  have := d.hR
  have := RadialStack.chain_ordered d.chain
  linarith

theorem exterior_nhds (d : SourceRadialSystem.Data) (x : Space) (hx : d.X < ‖x‖) :
    {y : Space | d.X < ‖y‖} ∈ 𝓝 x :=
  (isOpen_lt continuous_const continuous_norm).mem_nhds hx

/-- In the exterior the layered TM electric mode satisfies the first Maxwell equation classically. -/
theorem layered_tm_curl (d : SourceRadialSystem.Data) (m : Index d.l) (x : Space) (hx : d.X < ‖x‖) :
    curl (SourceUnclippedMaxwell.electric d (representative d.l m)) x =
      fun j => Complex.I * SourceUnclippedMaxwell.magnetic d (representative d.l m) x j := by
  have hx0 := exterior_ne_zero d x hx
  have hev : SourceUnclippedMaxwell.electric d (representative d.l m) =ᶠ[𝓝 x]
      fun y j => (Complex.I * SourceRadiation.amplitude d) *
        SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data d.l) (representative d.l m) y j := by
    filter_upwards [exterior_nhds d x hx] with y hy
    funext j
    have := congrFun (SourceExteriorSmooth.electric_exterior d (representative d.l m) y hy) j
    simpa only [Pi.smul_apply, smul_eq_mul] using this
  rw [ExteriorClassical.curl_congr_nhds hev, curl_const_mul _ x _ (vacuum_electric_diff d.l m x hx0),
    vacuum_tm_curl d.l m x hx0]
  funext j
  have := congrFun (SourceExteriorSmooth.magnetic_exterior d (representative d.l m) x hx) j
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [this]
  ring

/-- In the exterior the layered magnetic profile satisfies the TE form of the second Maxwell equation. -/
theorem layered_te_curl (d : SourceRadialSystem.Data) (m : Index d.l) (x : Space) (hx : d.X < ‖x‖) :
    curl (SourceUnclippedMaxwell.magnetic d (representative d.l m)) x =
      fun j => Complex.I * (-SourceUnclippedMaxwell.electric d (representative d.l m) x j) := by
  have hx0 := exterior_ne_zero d x hx
  have hev : SourceUnclippedMaxwell.magnetic d (representative d.l m) =ᶠ[𝓝 x]
      fun y j => (Complex.I * SourceRadiation.amplitude d) *
        SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data d.l) (representative d.l m) y j := by
    filter_upwards [exterior_nhds d x hx] with y hy
    funext j
    have := congrFun (SourceExteriorSmooth.magnetic_exterior d (representative d.l m) y hy) j
    simpa only [Pi.smul_apply, smul_eq_mul] using this
  rw [ExteriorClassical.curl_congr_nhds hev, curl_const_mul _ x _ (vacuum_magnetic_diff d.l m x hx0),
    vacuum_te_curl d.l m x hx0]
  funext j
  have := congrFun (SourceExteriorSmooth.electric_exterior d (representative d.l m) x hx) j
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [this]
  ring

theorem layered_electric_diff (d : SourceRadialSystem.Data) (m : Index d.l) (x : Space)
    (hx : d.X < ‖x‖) (j : Fin 3) :
    DifferentiableAt ℝ (fun y => SourceUnclippedMaxwell.electric d (representative d.l m) y j) x :=
  (SourceExteriorSmooth.electric_smooth d _ (representative_homogeneous d.l m)
    (representative_harmonic d.l m) x hx j).differentiableAt (by simp)

theorem layered_magnetic_diff (d : SourceRadialSystem.Data) (m : Index d.l) (x : Space)
    (hx : d.X < ‖x‖) (j : Fin 3) :
    DifferentiableAt ℝ (fun y => SourceUnclippedMaxwell.magnetic d (representative d.l m) y j) x :=
  (SourceExteriorSmooth.magnetic_smooth d _ x hx j).differentiableAt (by simp)

theorem correction_electric_eq (d : SourceRadialSystem.Data) (m : Index d.l) (y : Space) (hy : y ≠ 0)
    (j : Fin 3) :
    SourceRegularCorrection.electric d (representative d.l m) y j =
      SourceUnclippedMaxwell.electric d (representative d.l m) y j -
        SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data d.l) (representative d.l m) y j := by
  have h := congrFun (SourceRegularCorrection.electric_away d (representative d.l m)
    (representative_homogeneous d.l m) (representative_harmonic d.l m) y hy) j
  rw [SourceDielectricModes.vacuum_electric] at h
  exact h

theorem correction_magnetic_eq (d : SourceRadialSystem.Data) (m : Index d.l) (y : Space) (hy : y ≠ 0)
    (j : Fin 3) :
    SourceRegularCorrection.magnetic d (representative d.l m) y j =
      SourceUnclippedMaxwell.magnetic d (representative d.l m) y j -
        SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data d.l) (representative d.l m) y j := by
  have h := congrFun (SourceRegularCorrection.magnetic_away d (representative d.l m) y hy) j
  rw [SourceDielectricModes.vacuum_magnetic] at h
  exact h

/-- Outside the shell the actual TM regular correction satisfies the first Maxwell equation classically. -/
theorem correction_tm_curl (d : SourceRadialSystem.Data) (m : Index d.l) (x : Space) (hx : d.X < ‖x‖) :
    curl (SourceRegularCorrection.electric d (representative d.l m)) x =
      fun j => Complex.I * SourceRegularCorrection.magnetic d (representative d.l m) x j := by
  have hx0 := exterior_ne_zero d x hx
  have hev : SourceRegularCorrection.electric d (representative d.l m) =ᶠ[𝓝 x]
      fun y j => SourceUnclippedMaxwell.electric d (representative d.l m) y j -
        SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data d.l) (representative d.l m) y j := by
    filter_upwards [(show IsOpen {y : Space | y ≠ 0} from isOpen_ne).mem_nhds hx0] with y hy
    funext j
    exact correction_electric_eq d m y hy j
  rw [ExteriorClassical.curl_congr_nhds hev, curl_sub_field _ _ x (layered_electric_diff d m x hx)
    (vacuum_electric_diff d.l m x hx0), layered_tm_curl d m x hx, vacuum_tm_curl d.l m x hx0]
  funext j
  rw [correction_magnetic_eq d m x hx0 j]
  ring

/-- Outside the shell the actual TE regular correction satisfies the second Maxwell equation classically. -/
theorem correction_te_curl (d : SourceRadialSystem.Data) (m : Index d.l) (x : Space) (hx : d.X < ‖x‖) :
    curl (SourceRegularCorrection.magnetic d (representative d.l m)) x =
      fun j => Complex.I * (-SourceRegularCorrection.electric d (representative d.l m) x j) := by
  have hx0 := exterior_ne_zero d x hx
  have hev : SourceRegularCorrection.magnetic d (representative d.l m) =ᶠ[𝓝 x]
      fun y j => SourceUnclippedMaxwell.magnetic d (representative d.l m) y j -
        SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data d.l) (representative d.l m) y j := by
    filter_upwards [(show IsOpen {y : Space | y ≠ 0} from isOpen_ne).mem_nhds hx0] with y hy
    funext j
    exact correction_magnetic_eq d m y hy j
  rw [ExteriorClassical.curl_congr_nhds hev, curl_sub_field _ _ x (layered_magnetic_diff d m x hx)
    (vacuum_magnetic_diff d.l m x hx0), layered_te_curl d m x hx, vacuum_te_curl d.l m x hx0]
  funext j
  rw [correction_electric_eq d m x hx0 j]
  ring

/-! ### The magnetic field of the shell polarization of the mode solutions outside the shell -/

theorem magnetic_of_electric_eq (cs : SourceRadiatedSeries.Coefficient) (w : SourceRadiatedSeries.VectorL2)
    (X : ℝ) (hc : ∀ x : Space, x ∉ closedBall 0 X → cs.value (VectorFourier.coordinateMap x) = 0)
    (Fld : Field) (hFld : ∀ y : Space, X < ‖y‖ →
      ExteriorContinuity.electric 1 (DynamicVolume.source cs w) y = Fld y)
    (Hfld : Field) (hcurl : ∀ y : Space, X < ‖y‖ → curl Fld y = fun j => Complex.I * Hfld y j)
    (x : Space) (hx : X < ‖x‖) (i : Fin 3) :
    MagneticResponse.magnetic 1 (DynamicVolume.source cs w) x i = Hfld x i := by
  have hρ : ∀ j, Integrable (DynamicVolume.source cs w j) volume :=
    fun j => DynamicVolume.source_integrable cs w X hc j
  have hρc : ∀ j y, y ∉ closedBall (0 : Space) X → DynamicVolume.source cs w j y = 0 :=
    fun j y hy => DynamicVolume.source_zero cs w X hc j y hy
  have hmax := (ExteriorClassical.exterior_maxwell 1 (DynamicVolume.source cs w) hρ X hρc x hx).1
  have hev : ExteriorContinuity.electric 1 (DynamicVolume.source cs w) =ᶠ[𝓝 x] Fld := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact hFld y hy
  rw [ExteriorClassical.curl_congr_nhds hev, hcurl x hx] at hmax
  have h := congrFun hmax i
  simp only [Complex.ofReal_one, mul_one] at h
  exact mul_left_cancel₀ Complex.I_ne_zero h.symm

theorem magnetic_tm_mode (cs : SourceRadiatedSeries.Coefficient) (d : SourceRadialSystem.Data)
    (hm : ∀ x : Space, (cs.value (VectorFourier.coordinateMap x) : ℂ) = SourceRadialSystem.sigma d ‖x‖ - 1)
    (hdisp : ∀ g ∈ d.gs, g.q^2 = g.σ) (hu : IsUnit (DynamicVolume.volumeBlock cs 1 d.X))
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (a : PositiveIndex) (x : Space) (hx : d.X < ‖x‖) (i : Fin 3) :
    MagneticResponse.magnetic 1 (DynamicVolume.source cs
      (MaterialField.solution cs 1 d.X (SourceModeDatum.tmIncident cs d hc a))) x i =
      SourceRegularCorrection.magnetic (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i :=
  magnetic_of_electric_eq cs _ d.X hc
    (SourceRegularCorrection.electric (SourceDielectricModes.tmData d (a.1+1)) (representative (a.1+1) a.2))
    (fun y hy => funext fun j => SourceRadiatedSeries.exterior_tm_mode cs d hm hdisp hu hc a y hy j)
    (SourceRegularCorrection.magnetic (SourceDielectricModes.tmData d (a.1+1)) (representative (a.1+1) a.2))
    (fun y hy => correction_tm_curl (SourceDielectricModes.tmData d (a.1+1)) a.2 y hy) x hx i

theorem magnetic_te_mode (cs : SourceRadiatedSeries.Coefficient) (d : SourceRadialSystem.Data)
    (hm : ∀ x : Space, (cs.value (VectorFourier.coordinateMap x) : ℂ) = SourceRadialSystem.sigma d ‖x‖ - 1)
    (hdisp : ∀ g ∈ d.gs, g.q^2 = g.σ) (hu : IsUnit (DynamicVolume.volumeBlock cs 1 d.X))
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (a : PositiveIndex) (x : Space) (hx : d.X < ‖x‖) (i : Fin 3) :
    MagneticResponse.magnetic 1 (DynamicVolume.source cs
      (MaterialField.solution cs 1 d.X (SourceModeDatum.teIncident cs d hc a))) x i =
      SourceTECorrection.magnetic (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i :=
  magnetic_of_electric_eq cs _ d.X hc
    (SourceTECorrection.electric (SourceDielectricModes.teData d (a.1+1)) (representative (a.1+1) a.2))
    (fun y hy => funext fun j => SourceRadiatedSeries.exterior_te_mode cs d hm hdisp hu hc a y hy j)
    (SourceTECorrection.magnetic (SourceDielectricModes.teData d (a.1+1)) (representative (a.1+1) a.2))
    (fun y hy => correction_te_curl (SourceDielectricModes.teData d (a.1+1)) a.2 y hy) x hx i

/-- For an observation point outside the shell the magnetic field of the shell polarization is a bounded
linear functional of the shell vector. -/
theorem exists_exterior_magnetic_functional (cs : SourceRadiatedSeries.Coefficient) (Rin X : ℝ)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (x : Space) (hx : X < ‖x‖) (i : Fin 3) :
    ∃ Ψ : SourceRadiatedSeries.VectorL2 →L[ℂ] ℂ, ∀ w : SourceRadiatedSeries.VectorL2,
      Ψ w = MagneticResponse.magnetic 1 (DynamicVolume.source cs w) x i := by
  let dd := CoreMaterialEvaluation.supportData cs Rin X hcs
  have hδ : 0 < ‖x‖ - X := by linarith
  have hB : ∀ y ∈ dd.carrier, ∀ i j : Fin 3,
      ‖SphereMagneticKernel.magneticDyadic 1 (x - y) i j‖ ≤
        max 0 (2 * NewtonStripMaxwell.gradientBound 1 (‖x‖ - X)) := by
    intro y hy i j
    have hyX : ‖y‖ ≤ X := by simpa using hy.1
    have hz : (‖x‖ - X) / 2 ≤ ‖x - y‖ := by
      have := norm_sub_norm_le x y
      linarith
    exact (SourcePairedPlaneIdentification.magneticDyadic_bound (x - y) (‖x‖ - X) hδ hz i j).trans
      (le_max_right _ _)
  exact ⟨SourcePairedPlaneIdentification.magneticEvaluation cs dd x _ (le_max_left _ _) hB i,
    fun w => SourcePairedPlaneIdentification.magneticEvaluation_apply cs dd x _ (le_max_left _ _) hB i w⟩

/-- **The magnetic reaction field of the shell outside the shell as a series.** -/
theorem shell_reaction_magnetic_series_outside (cs ci : SourceRadiatedSeries.Coefficient)
    (d : SourceRadialSystem.Data) (b B T : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hT : 2 ≤ T)
    (hBT : 2*(B*AngularExteriorBounds.base) ≤ T) (hTR : T < d.R) (hbR : b < d.R)
    (hm : ∀ x : Space, (cs.value (VectorFourier.coordinateMap x) : ℂ) = SourceRadialSystem.sigma d ‖x‖ - 1)
    (hdisp : ∀ g ∈ d.gs, g.q^2 = g.σ) (hu : IsUnit (DynamicVolume.volumeBlock cs 1 d.X))
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (hi : ∀ x : Space, ‖x‖ ≤ d.R → cs.value (VectorFourier.coordinateMap x) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (v : SourceRadiatedSeries.VectorL2) (x : Space) (hx : d.X < ‖x‖) (i : Fin 3) :
    HasSum (fun a : PositiveIndex =>
      SourceRadiatedSeries.tmMoment a (fun j => DynamicVolume.source ci v j) *
          SourceRegularCorrection.magnetic (SourceDielectricModes.tmData d (a.1+1))
            (representative (a.1+1) a.2) x i +
        SourceRadiatedSeries.teMoment a (fun j => DynamicVolume.source ci v j) *
          SourceTECorrection.magnetic (SourceDielectricModes.teData d (a.1+1))
            (representative (a.1+1) a.2) x i)
      (MagneticResponse.magnetic 1 (DynamicVolume.source cs
        (MaterialField.solution cs 1 d.X (StaticCoefficient.sqrtMultiplier cs
          (ShellInclusionVolume.kernel 1 d.X (StaticCoefficient.sqrtMultiplier ci v))))) x i) := by
  have hcs : ∀ y : Space, y ∉ closedBall (0 : Space) d.X \ ball (0 : Space) d.R →
      cs.value (VectorFourier.coordinateMap y) = 0 := SourceModeDatum.annulus_support cs d hc hi
  obtain ⟨Ψ, hΨ⟩ := exists_exterior_magnetic_functional cs d.R d.X hcs x hx i
  have h := (SourceRadiatedSeries.shell_solution_series cs ci d b B T hb hB hscale hT hBT hTR hbR hc hi
    hci v).mapL Ψ
  have h2 : HasSum (fun a : PositiveIndex =>
      SourceRadiatedSeries.tmMoment a (fun j => DynamicVolume.source ci v j) *
          SourceRegularCorrection.magnetic (SourceDielectricModes.tmData d (a.1+1))
            (representative (a.1+1) a.2) x i +
        SourceRadiatedSeries.teMoment a (fun j => DynamicVolume.source ci v j) *
          SourceTECorrection.magnetic (SourceDielectricModes.teData d (a.1+1))
            (representative (a.1+1) a.2) x i)
      (Ψ (MaterialField.solution cs 1 d.X (StaticCoefficient.sqrtMultiplier cs
          (ShellInclusionVolume.kernel 1 d.X (StaticCoefficient.sqrtMultiplier ci v))))) := by
    convert h using 1
    funext a
    simp only [Function.comp_apply, map_add, map_smul, smul_eq_mul]
    rw [hΨ, hΨ, magnetic_tm_mode cs d hm hdisp hu hc a x hx i, magnetic_te_mode cs d hm hdisp hu hc a x hx i]
  rw [hΨ] at h2
  exact h2

theorem tm_total_mag_eq (d : SourceRadialSystem.Data) (a : PositiveIndex) (x : Space) (hx : x ≠ 0)
    (i : Fin 3) :
    SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
      SourceRegularCorrection.magnetic (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i =
      SourceUnclippedMaxwell.magnetic (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i := by
  have h : SourceRegularCorrection.magnetic (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i =
      SourceUnclippedMaxwell.magnetic (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i -
      SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data (a.1+1))
        (representative (a.1+1) a.2) x i :=
    correction_magnetic_eq (SourceDielectricModes.tmData d (a.1+1)) a.2 x hx i
  rw [h]
  ring

theorem te_total_mag_eq (d : SourceRadialSystem.Data) (a : PositiveIndex) (x : Space) (hx : x ≠ 0)
    (i : Fin 3) :
    -SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
      SourceTECorrection.magnetic (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i =
      SourceGeneralMaxwell.teMagnetic (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i := by
  have h : SourceRegularCorrection.electric (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i =
      SourceUnclippedMaxwell.electric (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i -
      SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data (a.1+1))
        (representative (a.1+1) a.2) x i :=
    correction_electric_eq (SourceDielectricModes.teData d (a.1+1)) a.2 x hx i
  change _ + -SourceRegularCorrection.electric (SourceDielectricModes.teData d (a.1+1))
    (representative (a.1+1) a.2) x i = -SourceUnclippedMaxwell.electric
      (SourceDielectricModes.teData d (a.1+1)) (representative (a.1+1) a.2) x i
  rw [h]
  ring

/-- **The radiated magnetic field of the inclusion outside the shell as a layered mode series.**
For `x` outside the shell, the magnetic field radiated by the inclusion source `v` (free field of the
inclusion source plus the field of the shell polarization driven by `Ss T Si v`) is the sum over the
positive degrees and real modes of the TM moment times the actual layered TM magnetic mode plus the TE
moment times the actual layered TE magnetic mode (the TE chain mode `teMagnetic (teData d (a.1+1))`). -/
theorem radiated_magnetic_series_outside (cs ci : SourceRadiatedSeries.Coefficient)
    (d : SourceRadialSystem.Data) (b B T : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hT : 2 ≤ T)
    (hBT : 2*(B*AngularExteriorBounds.base) ≤ T) (hTR : T < d.R) (hbR : b < d.R)
    (hm : ∀ x : Space, (cs.value (VectorFourier.coordinateMap x) : ℂ) = SourceRadialSystem.sigma d ‖x‖ - 1)
    (hdisp : ∀ g ∈ d.gs, g.q^2 = g.σ) (hu : IsUnit (DynamicVolume.volumeBlock cs 1 d.X))
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (hi : ∀ x : Space, ‖x‖ ≤ d.R → cs.value (VectorFourier.coordinateMap x) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (v : SourceRadiatedSeries.VectorL2) (x : Space) (hx : d.X < ‖x‖) (i : Fin 3) :
    HasSum (fun a : PositiveIndex =>
      SourceRadiatedSeries.tmMoment a (fun j => DynamicVolume.source ci v j) *
          SourceUnclippedMaxwell.magnetic (SourceDielectricModes.tmData d (a.1+1))
            (representative (a.1+1) a.2) x i +
        SourceRadiatedSeries.teMoment a (fun j => DynamicVolume.source ci v j) *
          SourceGeneralMaxwell.teMagnetic (SourceDielectricModes.teData d (a.1+1))
            (representative (a.1+1) a.2) x i)
      (MagneticResponse.magnetic 1 (fun j => DynamicVolume.source ci v j) x i +
        MagneticResponse.magnetic 1 (DynamicVolume.source cs
          (MaterialField.solution cs 1 d.X (StaticCoefficient.sqrtMultiplier cs
            (ShellInclusionVolume.kernel 1 d.X (StaticCoefficient.sqrtMultiplier ci v))))) x i) := by
  have hRX : d.R ≤ d.X := RadialStack.chain_ordered d.chain
  have hxT : max T b < ‖x‖ := max_lt (by linarith) (by linarith)
  have hx0 := exterior_ne_zero d x hx
  have h1 := free_magnetic_series_outside b B T hb hB hscale hT hBT
    (fun j => DynamicVolume.source ci v j) (fun j => DynamicVolume.source_integrable ci v b hci j)
    (fun j y hy => DynamicVolume.source_zero ci v b hci j y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy)) x hxT i
  have h2 := shell_reaction_magnetic_series_outside cs ci d b B T hb hB hscale hT hBT hTR hbR hm hdisp hu
    hc hi hci v x hx i
  convert h1.add h2 using 1
  funext a
  have e1 := tm_total_mag_eq d a x hx0 i
  have e2 := te_total_mag_eq d a x hx0 i
  rw [← e1, ← e2]
  unfold Gt
  ring

end OQ14.SourceRadiatedMagnetic

#print axioms OQ14.SourceRadiatedMagnetic.dcoord_eq_zero_of_not_tsupport
#print axioms OQ14.SourceRadiatedMagnetic.tsupport_dcoord_subset
#print axioms OQ14.SourceRadiatedMagnetic.local_curl_ibp
#print axioms OQ14.SourceRadiatedMagnetic.curl_eq_of_weak
#print axioms OQ14.SourceRadiatedMagnetic.pairing_tendsto
#print axioms OQ14.SourceRadiatedMagnetic.curl_limit
#print axioms OQ14.SourceRadiatedMagnetic.vacuum_sigma
#print axioms OQ14.SourceRadiatedMagnetic.vacuum_hdisp
#print axioms OQ14.SourceRadiatedMagnetic.vacuum_tm_curl
#print axioms OQ14.SourceRadiatedMagnetic.vacuum_te_curl
#print axioms OQ14.SourceRadiatedMagnetic.tm_mag_radial_bound
#print axioms OQ14.SourceRadiatedMagnetic.te_el_radial_bound
#print axioms OQ14.SourceRadiatedMagnetic.mag_uniform_bound
#print axioms OQ14.SourceRadiatedMagnetic.mag_weighted_term
#print axioms OQ14.SourceRadiatedMagnetic.mterm_bound
#print axioms OQ14.SourceRadiatedMagnetic.integral_sum_norm_le
#print axioms OQ14.SourceRadiatedMagnetic.Ft_eq_integral
#print axioms OQ14.SourceRadiatedMagnetic.Gt_eq_integral
#print axioms OQ14.SourceRadiatedMagnetic.Ft_bound
#print axioms OQ14.SourceRadiatedMagnetic.Gt_bound
#print axioms OQ14.SourceRadiatedMagnetic.partialE_smooth
#print axioms OQ14.SourceRadiatedMagnetic.partialH_smooth
#print axioms OQ14.SourceRadiatedMagnetic.partial_curl
#print axioms OQ14.SourceRadiatedMagnetic.free_magnetic_series_outside
#print axioms OQ14.SourceRadiatedMagnetic.curl_sub_field
#print axioms OQ14.SourceRadiatedMagnetic.vacuum_electric_diff
#print axioms OQ14.SourceRadiatedMagnetic.vacuum_magnetic_diff
#print axioms OQ14.SourceRadiatedMagnetic.exterior_ne_zero
#print axioms OQ14.SourceRadiatedMagnetic.exterior_nhds
#print axioms OQ14.SourceRadiatedMagnetic.layered_tm_curl
#print axioms OQ14.SourceRadiatedMagnetic.layered_te_curl
#print axioms OQ14.SourceRadiatedMagnetic.layered_electric_diff
#print axioms OQ14.SourceRadiatedMagnetic.layered_magnetic_diff
#print axioms OQ14.SourceRadiatedMagnetic.correction_electric_eq
#print axioms OQ14.SourceRadiatedMagnetic.correction_magnetic_eq
#print axioms OQ14.SourceRadiatedMagnetic.correction_tm_curl
#print axioms OQ14.SourceRadiatedMagnetic.correction_te_curl
#print axioms OQ14.SourceRadiatedMagnetic.magnetic_of_electric_eq
#print axioms OQ14.SourceRadiatedMagnetic.magnetic_tm_mode
#print axioms OQ14.SourceRadiatedMagnetic.magnetic_te_mode
#print axioms OQ14.SourceRadiatedMagnetic.exists_exterior_magnetic_functional
#print axioms OQ14.SourceRadiatedMagnetic.shell_reaction_magnetic_series_outside
#print axioms OQ14.SourceRadiatedMagnetic.tm_total_mag_eq
#print axioms OQ14.SourceRadiatedMagnetic.te_total_mag_eq
#print axioms OQ14.SourceRadiatedMagnetic.radiated_magnetic_series_outside
