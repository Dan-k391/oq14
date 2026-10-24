import RestrictedTEActualPiecewise
import ChannelMaterialThroughput
import NewtonStripMaxwell
import MagneticLocal
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! The TE background pair as the actual total fields of the shell solution outside the core.

The actual shell solution `shellSol` for the datum of a coefficient vector `A` has total electric field
`MaterialField.total` (a.e. the TE background electric field `bgFieldE`, `shell_te_response`) and total magnetic field
`MaterialMaxwell.totalMagnetic`.  This module identifies the TE background magnetic field `bgFieldH` (the family
`famBackgroundH`, minus the TM-structure electric background) with the total magnetic field, and records the
consequences for the plane fields.

* `WeakFirst`, `magnetic_ae_unique`: the first weak Maxwell equation `curl E = i k H` against compactly supported
  Schwartz tests determines a locally integrable `H` almost everywhere from `E` (no permittivity enters); proved with
  the fundamental lemma `ae_eq_of_integral_contDiff_smul_eq`.
* `famBackground_forced`, `famBackground_weakFirst`: the TE background pair of a finite family of regular modes over
  a stack with unit `sigma` is a forced weak Maxwell pair (the per-mode `te_background_forced` summed over the
  family, by induction on the support).
* `shell_testMaxwell`, `shell_totalMagnetic_loc`, `famBackground_ae`, `famBackgroundH_ae`: the actual shell
  solution is a weak Maxwell pair with the dielectric permittivity of the shell
  (`MaterialMaxwell.volume_solution_testMaxwell` with the volume equation of `shell_isUnit`), and the TE background
  magnetic field equals its total magnetic field almost everywhere.
* `bgFieldE_continuousOn`, `bgFieldH_continuousOn` (with the mode-formula lemmas `hform_continuousOn`,
  `eform_continuousOn` and `inverseSigma_one`): the TE background pair is continuous on `x != 0` (the layered mode
  profiles are continuous through the interface spheres, `backgroundState_continuousOn`).
* `magnetic_continuous_of_bounded` (from `response_continuous_of_bounded`: the response of an integrable, a.e.
  bounded, compactly supported source for a locally integrable kernel is continuous, by `L1` approximation of the
  truncated kernel by continuous compactly supported kernels and translation invariance), `shell_source_ae` (the
  induced source is a.e. the bounded explicit force `famForce`, `famBackgroundDatum_source`),
  `shell_totalMagnetic_continuous`: the total magnetic field of the actual shell solution is continuous on all
  of space.  Hence `famBackgroundH_eq`: pointwise, for every `x != 0` and every coordinate, the TE background
  magnetic field is the total magnetic field of the actual shell solution, interface spheres included.
* `bgFieldE_eq_exterior`, `backgroundElectric_eq_bgFieldE_exterior`: for `X < ||x||` the continuous representative
  of the total electric field (incident plus the literal dyadic integral of the induced source) is the TE
  background electric field.  Inside the shell annulus the literal dyadic integral of a source supported there is
  not a field (the kernel is not absolutely integrable), so on the annulus the electric statement is the almost
  everywhere identity `famBackground_ae` with the continuous representative `bgFieldE`.
* `bgOutE`, `bgOutH`: the outside background pair on the plane (`bgLinE`, `bgLinH` composed with the plane embedding),
  `FieldMap`s with continuous (away from the origin) and almost everywhere strongly measurable coordinates, equal to
  the literal backgrounds of the shell (`backgroundElectric_eq_bgOutE`, `backgroundMagnetic_eq_bgOutH`);
  `outFieldE`, `outFieldH` add a linear radiated field, for which `OutsideDecomposition` holds by definition
  (`outsideDecomposition_of_radiated`) as soon as the radiated fields satisfy the uniform decomposition, and the
  outside majorant follows (`outside_majorant_of_radiated`). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEBackgroundOutside
open MeasureTheory Filter Topology Metric Set
open scoped ComplexConjugate

abbrev FieldMap := OQ14.RestrictedTEActualFields.FieldMap
abbrev Vec := OQ14.RestrictedTEActualCore.Vec
abbrev Sp := FourierL2.Space
abbrev VectorL2 := VectorFourier.VectorL2

/-! ### Uniqueness of the magnetic field from the first weak Maxwell equation -/

section WeakFirst
open OQ14.MaterialMaxwell OQ14.MagneticResponse

/-- The first weak Maxwell equation `curl E = i k H` against all compactly supported Schwartz tests. -/
def WeakFirst (k : ℝ) (E H : Maxwell.Field) : Prop :=
  ∀ (i : Fin 3) (f : DynamicSource.Test),
    curlPair (fieldPair E) i f = Complex.I * (k : ℂ) * fieldPair H i f

theorem weakFirst_of_testMaxwell {k : ℝ} {ε : Sp → ℝ} {E H : Maxwell.Field}
    (h : TestMaxwell k ε E H) : WeakFirst k E H := fun i f => (h i f).1

theorem weakFirst_of_forced {k : ℝ} {ρ : Fin 3 → Sp → ℂ} {E H : Maxwell.Field}
    (h : OQ14.ForcedMaxwellResponse.TestForced k ρ E H) : WeakFirst k E H := fun i f => (h i f).1

/-- **Almost-everywhere uniqueness of the magnetic field.**  Two locally integrable magnetic fields that satisfy
the first weak Maxwell equation with electric fields that agree almost everywhere agree almost everywhere
(no permittivity enters: `curl E = i k H` alone determines `H` from `E`). -/
theorem magnetic_ae_unique (k : ℝ) (hk : k ≠ 0) (E E' H H' : Maxwell.Field)
    (hE : ∀ j, (fun x => E x j) =ᵐ[volume] fun x => E' x j)
    (hH : ∀ j, LocallyIntegrable (fun x => H x j)) (hH' : ∀ j, LocallyIntegrable (fun x => H' x j))
    (h : WeakFirst k E H) (h' : WeakFirst k E' H') (i : Fin 3) :
    (fun x => H x i) =ᵐ[volume] fun x => H' x i := by
  have hpair : ∀ (j : Fin 3) (f : DynamicSource.Test), fieldPair E j f = fieldPair E' j f := by
    intro j f
    unfold fieldPair
    apply integral_congr_ae
    filter_upwards [hE j] with x hx
    rw [hx]
  have hcurl : ∀ (j : Fin 3) (f : DynamicSource.Test),
      curlPair (fieldPair E) j f = curlPair (fieldPair E') j f := by
    intro j f
    unfold curlPair
    rw [hpair, hpair]
  have hHH : ∀ (j : Fin 3) (f : DynamicSource.Test), fieldPair H j f = fieldPair H' j f := by
    intro j f
    have e := ((h j f).symm.trans ((hcurl j f).trans (h' j f)))
    have hc : Complex.I * (k : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)
    exact mul_left_cancel₀ hc e
  apply ae_eq_of_integral_contDiff_smul_eq (hH i) (hH' i)
  intro φ hφ hφc
  have hφc2 : HasCompactSupport (fun x => (φ x : ℂ)) :=
    hφc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz
    (fun x => (φ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ) hφc2, hφc2⟩
  have hp := hHH i f
  unfold fieldPair at hp
  have e1 : (∫ x, φ x • H x i) = ∫ x, H x i * f.val x := by
    apply integral_congr_ae
    filter_upwards with x
    change φ x • H x i = H x i * (φ x : ℂ)
    rw [Complex.real_smul, mul_comm]
  have e2 : (∫ x, φ x • H' x i) = ∫ x, H' x i * f.val x := by
    apply integral_congr_ae
    filter_upwards with x
    change φ x • H' x i = H' x i * (φ x : ℂ)
    rw [Complex.real_smul, mul_comm]
  rw [e1, e2]
  exact hp

end WeakFirst

/-! ### The TE background pair of a finite family satisfies the weak Maxwell equations -/

section Family
open OQ14.BackgroundModeTE OQ14.BackgroundModeMaxwell OQ14.BackgroundFluxMajorant OQ14.ForcedMaxwellResponse
  OQ14.SourceRadialSystem OQ14.HarmonicPolynomial

variable {ι : Type*}

theorem famBackgroundH_apply (d0 : Data) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly)
    (x : Sp) (i : Fin 3) :
    famBackgroundH d0 s c lq P x i =
      ∑ q ∈ s, c q * (-(backgroundElectric { d0 with l := lq q } (P q) x i)) := by
  simp [famBackgroundH, Finset.sum_apply]

theorem famBackground_loc (d0 : Data) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => famBackground d0 s c lq P x i) := by
  have e : (fun x => famBackground d0 s c lq P x i) =
      fun x => ∑ q ∈ s, c q * backgroundMagnetic { d0 with l := lq q } (P q) x i := by
    funext x
    exact famBackground_apply d0 s c lq P x i
  rw [e]
  exact locallyIntegrable_finset_sum s (fun q _ => by
    simpa only [smul_eq_mul] using (backgroundMagnetic_locallyIntegrable { d0 with l := lq q } (P q) i).smul (c q))

theorem famBackgroundH_loc (d0 : Data) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => famBackgroundH d0 s c lq P x i) := by
  have e : (fun x => famBackgroundH d0 s c lq P x i) =
      fun x => ∑ q ∈ s, c q * (-(backgroundElectric { d0 with l := lq q } (P q) x i)) := by
    funext x
    exact famBackgroundH_apply d0 s c lq P x i
  rw [e]
  exact locallyIntegrable_finset_sum s (fun q _ => by
    simpa only [smul_eq_mul] using
      (backgroundElectric_locallyIntegrable { d0 with l := lq q } (P q) i).neg.smul (c q))

theorem famForce_loc (d0 : Data) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) (i : Fin 3) :
    LocallyIntegrable (famForce d0 s c lq P i) := by
  have e : famForce d0 s c lq P i =
      fun x => ∑ q ∈ s, c q * teBackgroundPolarization { d0 with l := lq q } (P q) i x := rfl
  rw [e]
  exact locallyIntegrable_finset_sum s (fun q _ => by
    simpa only [smul_eq_mul] using (teBackgroundPolarization_loc { d0 with l := lq q } (P q) i).smul (c q))

/-- **The TE background pair of a finite family is a forced weak Maxwell pair.**  The electric field `famBackground`
and the magnetic field `famBackgroundH` of a finite family of regular TE modes over a stack with unit `sigma`
satisfy both weak Maxwell equations with the (TE) force `famForce`, by summing the per-mode statement
`te_background_forced`. -/
theorem famBackground_forced [DecidableEq ι] (d0 : Data) (hσ : ∀ g ∈ d0.gs, g.σ = 1) (s : Finset ι)
    (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) (hp : ∀ q, (P q).IsHomogeneous (lq q))
    (hh : ∀ q, HarmonicPolynomial.formalLaplacian (P q) = 0) :
    TestForced 1 (famForce d0 s c lq P) (famBackground d0 s c lq P) (famBackgroundH d0 s c lq P) := by
  induction s using Finset.induction_on with
  | empty =>
    have hE : famBackground d0 ∅ c lq P = 0 := by simp [famBackground]
    have hH : famBackgroundH d0 ∅ c lq P = 0 := by simp [famBackgroundH]
    have hρ : famForce d0 ∅ c lq P = fun _ _ => 0 := by
      funext i x
      simp [famForce]
    rw [hE, hH, hρ]
    intro i f
    simp [MaterialMaxwell.fieldPair, MagneticResponse.curlPair]
  | insert a s ha ih =>
    have e1 : famBackground d0 (insert a s) c lq P =
        c a • backgroundMagnetic { d0 with l := lq a } (P a) + famBackground d0 s c lq P := by
      unfold famBackground
      exact Finset.sum_insert ha
    have e2 : famBackgroundH d0 (insert a s) c lq P =
        c a • (-(backgroundElectric { d0 with l := lq a } (P a))) + famBackgroundH d0 s c lq P := by
      unfold famBackgroundH
      exact Finset.sum_insert ha
    have e3 : famForce d0 (insert a s) c lq P = fun i x =>
        c a * teBackgroundPolarization { d0 with l := lq a } (P a) i x + famForce d0 s c lq P i x := by
      funext i x
      exact Finset.sum_insert ha
    rw [e1, e2, e3]
    have ha' := testForced_smul 1 (c a) _ _ _ (te_background_forced { d0 with l := lq a } hσ (P a) (hp a) (hh a))
    refine testForced_add 1 _ _ _ _ _ _ ?_ (famForce_loc d0 s c lq P) ?_ ?_ (famBackground_loc d0 s c lq P)
      (famBackgroundH_loc d0 s c lq P) ha' ih
    · intro i
      simpa only [smul_eq_mul] using (teBackgroundPolarization_loc { d0 with l := lq a } (P a) i).smul (c a)
    · exact locallyIntegrable_smul (c a) _ (backgroundMagnetic_locallyIntegrable { d0 with l := lq a } (P a))
    · exact locallyIntegrable_smul (c a) _ (fun i => (backgroundElectric_locallyIntegrable { d0 with l := lq a } (P a) i).neg)

theorem famBackground_weakFirst [DecidableEq ι] (d0 : Data) (hσ : ∀ g ∈ d0.gs, g.σ = 1) (s : Finset ι)
    (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) (hp : ∀ q, (P q).IsHomogeneous (lq q))
    (hh : ∀ q, HarmonicPolynomial.formalLaplacian (P q) = 0) :
    WeakFirst 1 (famBackground d0 s c lq P) (famBackgroundH d0 s c lq P) :=
  weakFirst_of_forced (famBackground_forced d0 hσ s c lq P hp hh)

end Family

/-! ### The actual shell solution and the identification of the background pair almost everywhere -/

section Shell
open OQ14.RestrictedTEActualCore OQ14.BackgroundShellCoefficient OQ14.BackgroundModeTE
  OQ14.BackgroundFluxMajorant OQ14.RestrictedTEActualPiecewise
variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ)

/-- The actual shell solution for the datum of the coefficient vector `A`. -/
def shellSol (A : Vec) : VectorL2 :=
  MaterialField.solution (SourcePairedInclusion.shell q hq n r) 1 (SourcePairedInclusion.data q hq n r).X
    (fsLin q hq n r A)

/-- The volume equation of the actual shell solution. -/
theorem shellSol_equation (A : Vec) :
    DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1 (SourcePairedInclusion.data q hq n r).X
      (shellSol q hq n r A) = fsLin q hq n r A :=
  congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (fsLin q hq n r A))
    (Ring.mul_inverse_cancel _ (SourcePairedInclusion.shell_isUnit q hq n r))

/-- **The actual shell solution is a weak Maxwell pair.**  The total electric field of the shell solution and its
total magnetic field `totalMagnetic` (the incident magnetic field plus the magnetic response of the induced
source) satisfy both weak Maxwell equations with the dielectric permittivity of the shell. -/
theorem shell_testMaxwell (A : Vec) :
    MaterialMaxwell.TestMaxwell 1 (MaterialMaxwell.dielectric (SourcePairedInclusion.shell q hq n r))
      (MaterialField.total (SourcePairedInclusion.shell q hq n r) 1 (shellSol q hq n r A)
        (RestrictedTEPlaneLocal.electric A))
      (MaterialMaxwell.totalMagnetic (SourcePairedInclusion.shell q hq n r) 1 (shellSol q hq n r A)
        (RestrictedTEPlaneLocal.magnetic A)) :=
  MaterialMaxwell.volume_solution_testMaxwell (SourcePairedInclusion.shell q hq n r) 1
    (SourcePairedInclusion.data q hq n r).X (shellSol q hq n r A) (fsLin q hq n r A)
    (RestrictedTEPlaneLocal.electric A) (RestrictedTEPlaneLocal.magnetic A) (shell_vanish_outer q hq n r)
    (fun i => RestrictedTEMaterial.datum_actual _ _ A i) (shellSol_equation q hq n r A)
    (fun i => (RestrictedTEMaterial.electric_smooth A i).continuous.locallyIntegrable)
    (fun i => (RestrictedTEMaterial.magnetic_smooth A i).continuous.locallyIntegrable)
    (RestrictedTEMaterial.testMaxwell A)

/-- The total magnetic field of the shell solution is locally integrable. -/
theorem shell_totalMagnetic_loc (A : Vec) (i : Fin 3) :
    LocallyIntegrable (fun x => MaterialMaxwell.totalMagnetic (SourcePairedInclusion.shell q hq n r) 1
      (shellSol q hq n r A) (RestrictedTEPlaneLocal.magnetic A) x i) := by
  have h1 : LocallyIntegrable (fun x : Sp => RestrictedTEPlaneLocal.magnetic A x i) volume :=
    (RestrictedTEMaterial.magnetic_smooth A i).continuous.locallyIntegrable
  have h2 := MagneticLocal.magnetic_locallyIntegrable 1 (SourcePairedInclusion.data q hq n r).X
    (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r) (shellSol q hq n r A))
    (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) (shellSol q hq n r A))
    (DynamicVolume.source_integrable _ _ (SourcePairedInclusion.data q hq n r).X (shell_vanish_outer q hq n r))
    (DynamicVolume.source_zero _ _ (SourcePairedInclusion.data q hq n r).X (shell_vanish_outer q hq n r))
    (StaticNewton.material_source_ae _ _) i
  exact h1.add h2

/-- **Electric side, almost everywhere.**  The total electric field of the actual shell solution is almost
everywhere the TE background electric field `bgFieldE` (restatement of `shell_te_response`). -/
theorem famBackground_ae (A : Vec) :
    MaterialField.total (SourcePairedInclusion.shell q hq n r) 1 (shellSol q hq n r A)
      (RestrictedTEPlaneLocal.electric A) =ᵐ[volume] bgFieldE q hq n r A :=
  shell_te_response q hq n r A

/-- **Magnetic side, almost everywhere.**  The TE background magnetic field `bgFieldH` (the family
`famBackgroundH` of the physical TE stack) is almost everywhere the total magnetic field of the actual shell
solution. -/
theorem famBackgroundH_ae (A : Vec) (i : Fin 3) :
    (fun x => bgFieldH q hq n r A x i) =ᵐ[volume]
      fun x => MaterialMaxwell.totalMagnetic (SourcePairedInclusion.shell q hq n r) 1 (shellSol q hq n r A)
        (RestrictedTEPlaneLocal.magnetic A) x i := by
  classical
  have hT := shell_testMaxwell q hq n r A
  have hF := famBackground_forced (physicalTE q (zero_lt_one.trans_le hq) n r)
    (physicalTE_sigma q (zero_lt_one.trans_le hq) n r) A.support (teCoeff A) (fun q => q.val.1)
    RestrictedTEIncoming.polynomial (fun q => polynomial_homogeneous q) (fun q => polynomial_harmonic q)
  have hE : ∀ j, (fun x => MaterialField.total (SourcePairedInclusion.shell q hq n r) 1 (shellSol q hq n r A)
      (RestrictedTEPlaneLocal.electric A) x j) =ᵐ[volume] fun x => bgFieldE q hq n r A x j := by
    intro j
    exact (famBackground_ae q hq n r A).mono (fun x hx => congrFun hx j)
  exact (magnetic_ae_unique 1 one_ne_zero _ _ _ _ hE (shell_totalMagnetic_loc q hq n r A)
    (famBackgroundH_loc _ _ _ _ _) (weakFirst_of_testMaxwell hT) (weakFirst_of_forced hF) i).symm

end Shell

/-! ### Continuity of the TE background pair away from the origin -/

section Continuity
open OQ14.BackgroundModeMaxwell OQ14.BackgroundFluxMajorant OQ14.BackgroundModeTE OQ14.SourceRadialSystem
  OQ14.HarmonicPolynomial OQ14.BackgroundCoreTransmission

variable {ι : Type*}

/-- For a stack with unit `sigma` the clipped inverse permittivity is `1` on `R < r ≤ X`. -/
theorem clipped_inverseSigma_one {gs : List OQ14.RadialStack.Layer} {X R : ℝ}
    (h : OQ14.RadialStack.Chain gs X R) :
    (∀ g ∈ gs, g.σ = 1) → ∀ r : ℝ, R < r → r ≤ X → OQ14.ClippedLayerProfiles.inverseSigma gs r = 1 := by
  induction h with
  | nil R =>
    intro _ r hr hrX
    exact absurd (hr.trans_le hrX) (lt_irrefl _)
  | cons g gs R hch ih =>
    intro hσ r hr hrX
    unfold OQ14.ClippedLayerProfiles.inverseSigma OQ14.ClippedLayerProfiles.select
    by_cases hg : g.a < r
    · rw [if_pos hg, hσ g List.mem_cons_self]
      simp
    · rw [if_neg hg]
      exact ih (fun g' hg' => hσ g' (List.mem_cons_of_mem _ hg')) r hr (not_lt.mp hg)

/-- For a stack with unit `sigma` the inverse permittivity profile of the source system is identically `1`. -/
theorem inverseSigma_one (d : Data) (hσ : ∀ g ∈ d.gs, g.σ = 1) (r : ℝ) :
    OQ14.SourceRadialSystem.inverseSigma d r = 1 := by
  unfold OQ14.SourceRadialSystem.inverseSigma OQ14.SourceRadialSystem.extend
  split_ifs with h1 h2
  · rfl
  · exact clipped_inverseSigma_one d.chain hσ r (not_le.mp h1) h2
  · rfl

/-- The half background state is continuous on the positive reals. -/
theorem bgHalf_continuousOn (d : Data) : ContinuousOn (bgHalf d) (Ioi 0) := by
  unfold bgHalf
  exact (backgroundState_continuousOn d.l d.chain d.hR).const_smul (1 / 2 : ℂ)

theorem hform_continuousOn (l : ℕ) (P : Poly) (u : ℝ → ℂ) (hu : ContinuousOn u (Ioi 0)) (i : Fin 3) :
    ContinuousOn (fun x : Sp => Hform l P (u ‖x‖) x i) {x : Sp | x ≠ 0} := by
  have hnorm : ContinuousOn (fun x : Sp => u ‖x‖) {x : Sp | x ≠ 0} :=
    hu.comp continuous_norm.continuousOn (fun x hx => norm_pos_iff.mpr hx)
  have hden : ContinuousOn (fun x : Sp => ((‖x‖ : ℝ) : ℂ) ^ (l + 1)) {x : Sp | x ≠ 0} :=
    ((Complex.continuous_ofReal.comp continuous_norm).pow (l + 1)).continuousOn
  have hang : Continuous (fun x : Sp => DebyeRadialTrace.angularToroidal P x i) :=
    (continuous_apply i).comp (HarmonicRadiationGeometry.angularToroidal_continuous P)
  unfold Hform
  refine (continuousOn_const.mul (hnorm.div hden (fun x hx => ?_))).mul hang.continuousOn
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx))

theorem eform_continuousOn (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l) (s : ℂ) (u p : ℝ → ℂ)
    (hu : ContinuousOn u (Ioi 0)) (hpp : ContinuousOn p (Ioi 0)) (i : Fin 3) :
    ContinuousOn (fun x : Sp => Eform l P s (u ‖x‖) (p ‖x‖) x i) {x : Sp | x ≠ 0} := by
  have hun : ContinuousOn (fun x : Sp => u ‖x‖) {x : Sp | x ≠ 0} :=
    hu.comp continuous_norm.continuousOn (fun x hx => norm_pos_iff.mpr hx)
  have hpn : ContinuousOn (fun x : Sp => p ‖x‖) {x : Sp | x ≠ 0} :=
    hpp.comp continuous_norm.continuousOn (fun x hx => norm_pos_iff.mpr hx)
  have hden : ∀ k : ℕ, ContinuousOn (fun x : Sp => ((‖x‖ : ℝ) : ℂ) ^ k) {x : Sp | x ≠ 0} :=
    fun k => ((Complex.continuous_ofReal.comp continuous_norm).pow k).continuousOn
  have hne : ∀ k : ℕ, ∀ x ∈ {x : Sp | x ≠ 0}, ((‖x‖ : ℝ) : ℂ) ^ k ≠ 0 := fun k x hx =>
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx))
  have hpol : Continuous (fun x : Sp => HarmonicRadiationFactors.poloidal P x i) :=
    (continuous_apply i).comp (HarmonicRadiationFactors.poloidal_continuous P)
  have hev : Continuous (fun x : Sp => complexEvaluate P x) := (complexEvaluate_regular P).continuous
  have hxi : Continuous (fun x : Sp => ((x i : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous
  have h1 : ContinuousOn (fun x : Sp => (p ‖x‖ / ((‖x‖ : ℝ) : ℂ) ^ (l + 2)) *
      HarmonicRadiationFactors.poloidal P x i) {x : Sp | x ≠ 0} :=
    (hpn.div (hden _) (hne _)).mul hpol.continuousOn
  have h2 : ContinuousOn (fun x : Sp => (s * ((l : ℂ) * (l + 1) * u ‖x‖ / ((‖x‖ : ℝ) : ℂ) ^ (l + 3)) *
      complexEvaluate P x) * ((x i : ℝ) : ℂ)) {x : Sp | x ≠ 0} :=
    ((continuousOn_const.mul ((continuousOn_const.mul hun).div (hden _) (hne _))).mul
      hev.continuousOn).mul hxi.continuousOn
  refine (h1.add h2).congr (fun x hx => ?_)
  have h := congrFun (eform_split l P hp s (u ‖x‖) (p ‖x‖) x hx) i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, DebyeRadialTrace.position] at h
  exact h

theorem backgroundMagnetic_continuousOn (d : Data) (P : Poly) (i : Fin 3) :
    ContinuousOn (fun x : Sp => backgroundMagnetic d P x i) {x : Sp | x ≠ 0} :=
  (hform_continuousOn d.l P (fun r => (bgHalf d r).1)
    (continuous_fst.comp_continuousOn (bgHalf_continuousOn d)) i).congr
    (fun x hx => backgroundMagnetic_eq_form d P x hx i)

theorem backgroundElectric_continuousOn (d : Data) (hσ : ∀ g ∈ d.gs, g.σ = 1) (P : Poly)
    (hp : P.IsHomogeneous d.l) (hh : HarmonicPolynomial.formalLaplacian P = 0) (i : Fin 3) :
    ContinuousOn (fun x : Sp => backgroundElectric d P x i) {x : Sp | x ≠ 0} := by
  refine (eform_continuousOn d.l P hp 1 (fun r => (bgHalf d r).1) (fun r => (bgHalf d r).2)
    (continuous_fst.comp_continuousOn (bgHalf_continuousOn d))
    (continuous_snd.comp_continuousOn (bgHalf_continuousOn d)) i).congr (fun x hx => ?_)
  rw [backgroundElectric_eq_form d P hp hh x hx i, inverseSigma_one d hσ]

theorem famBackground_continuousOn (d0 : Data) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly)
    (i : Fin 3) : ContinuousOn (fun x : Sp => famBackground d0 s c lq P x i) {x : Sp | x ≠ 0} := by
  have e : (fun x : Sp => famBackground d0 s c lq P x i) =
      fun x => ∑ q ∈ s, c q * backgroundMagnetic { d0 with l := lq q } (P q) x i :=
    funext fun x => famBackground_apply d0 s c lq P x i
  rw [e]
  exact continuousOn_finset_sum s (fun q _ =>
    continuousOn_const.mul (backgroundMagnetic_continuousOn _ _ i))

theorem famBackgroundH_continuousOn (d0 : Data) (hσ : ∀ g ∈ d0.gs, g.σ = 1) (s : Finset ι) (c : ι → ℂ)
    (lq : ι → ℕ) (P : ι → Poly) (hp : ∀ q, (P q).IsHomogeneous (lq q))
    (hh : ∀ q, HarmonicPolynomial.formalLaplacian (P q) = 0) (i : Fin 3) :
    ContinuousOn (fun x : Sp => famBackgroundH d0 s c lq P x i) {x : Sp | x ≠ 0} := by
  have e : (fun x : Sp => famBackgroundH d0 s c lq P x i) =
      fun x => ∑ q ∈ s, c q * (-(backgroundElectric { d0 with l := lq q } (P q) x i)) :=
    funext fun x => famBackgroundH_apply d0 s c lq P x i
  rw [e]
  exact continuousOn_finset_sum s (fun q _ =>
    continuousOn_const.mul (backgroundElectric_continuousOn { d0 with l := lq q } hσ _ (hp q) (hh q) i).neg)

end Continuity

/-! ### The outside background pair on the plane and the outside decomposition -/

section Plane
open OQ14.BackgroundModeTE OQ14.RestrictedTEActualPiecewise
variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ)

/-- The outside TE background electric field on the plane: the background electric field of the physical stack at
shell index `r`, linear in the coefficient vector, evaluated at the plane points. -/
def bgOutE : FieldMap :=
  (LinearMap.funLeft ℂ Maxwell.Vector MaxwellPlaneTail.planePoint).comp (bgLinE q hq n r)

/-- The outside TE background magnetic field on the plane. -/
def bgOutH : FieldMap :=
  (LinearMap.funLeft ℂ Maxwell.Vector MaxwellPlaneTail.planePoint).comp (bgLinH q hq n r)

theorem bgOutE_apply (x : Vec) (ξ : PlaneInverseCube.Plane) :
    bgOutE q hq n r x ξ = bgFieldE q hq n r x (MaxwellPlaneTail.planePoint ξ) := rfl

theorem bgOutH_apply (x : Vec) (ξ : PlaneInverseCube.Plane) :
    bgOutH q hq n r x ξ = bgFieldH q hq n r x (MaxwellPlaneTail.planePoint ξ) := rfl

theorem bgOutE_famBackground (A : Vec) (ξ : PlaneInverseCube.Plane) :
    bgOutE q hq n r A ξ = famBackground (physicalTE q (zero_lt_one.trans_le hq) n r) A.support (teCoeff A)
      (fun q => q.val.1) RestrictedTEIncoming.polynomial (MaxwellPlaneTail.planePoint ξ) := rfl

theorem bgOutH_famBackgroundH (A : Vec) (ξ : PlaneInverseCube.Plane) :
    bgOutH q hq n r A ξ = OQ14.BackgroundFluxMajorant.famBackgroundH (physicalTE q (zero_lt_one.trans_le hq) n r)
      A.support (teCoeff A) (fun q => q.val.1) RestrictedTEIncoming.polynomial
      (MaxwellPlaneTail.planePoint ξ) := rfl

theorem planePoint_ne_zero (ξ : PlaneInverseCube.Plane) (hξ : ξ ≠ 0) : MaxwellPlaneTail.planePoint ξ ≠ 0 := by
  have h : ‖MaxwellPlaneTail.planePoint ξ‖ = ‖ξ‖ := MaxwellPlaneTail.planePoint_norm ξ
  exact norm_pos_iff.mp (by rw [h]; exact norm_pos_iff.mpr hξ)

/-- A function of the space point that is continuous away from the origin gives, composed with the plane
embedding, a function with almost everywhere strongly measurable values. -/
theorem plane_aemeas (g : Sp → ℂ) (hg : ContinuousOn g {x : Sp | x ≠ 0}) :
    AEStronglyMeasurable (fun ξ : PlaneInverseCube.Plane => g (MaxwellPlaneTail.planePoint ξ)) volume := by
  have hc : ContinuousOn (fun ξ : PlaneInverseCube.Plane => g (MaxwellPlaneTail.planePoint ξ))
      {ξ : PlaneInverseCube.Plane | ξ ≠ 0} :=
    hg.comp MaxwellPlaneTail.planePoint_continuous.continuousOn (fun ξ hξ => planePoint_ne_zero ξ hξ)
  have h := hc.aestronglyMeasurable (μ := volume) (isOpen_ne.measurableSet : MeasurableSet {ξ : PlaneInverseCube.Plane | ξ ≠ 0})
  have e : (volume : Measure PlaneInverseCube.Plane).restrict {ξ : PlaneInverseCube.Plane | ξ ≠ 0} = volume :=
    restrict_compl_singleton (μ := (volume : Measure PlaneInverseCube.Plane)) (0 : PlaneInverseCube.Plane)
  rwa [e] at h

/-- The coordinates of the outside background electric field are almost everywhere strongly measurable. -/
theorem bgOutE_meas (x : Vec) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ => bgOutE q hq n r x ξ i) volume :=
  plane_aemeas _ (famBackground_continuousOn _ _ _ _ _ i)

theorem bgOutH_meas (x : Vec) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ => bgOutH q hq n r x ξ i) volume :=
  plane_aemeas _ (famBackgroundH_continuousOn _ (physicalTE_sigma q (zero_lt_one.trans_le hq) n r) _ _ _ _
    (fun q => polynomial_homogeneous q) (fun q => polynomial_harmonic q) i)

/-- The coordinates of the outside background fields are continuous on the plane away from the origin. -/
theorem bgOutE_continuousOn (x : Vec) (i : Fin 3) :
    ContinuousOn (fun ξ : PlaneInverseCube.Plane => bgOutE q hq n r x ξ i) {ξ | ξ ≠ 0} :=
  (famBackground_continuousOn (physicalTE q (zero_lt_one.trans_le hq) n r) x.support (teCoeff x)
    (fun q => q.val.1) RestrictedTEIncoming.polynomial i).comp MaxwellPlaneTail.planePoint_continuous.continuousOn
    (fun ξ hξ => planePoint_ne_zero ξ hξ)

theorem bgOutH_continuousOn (x : Vec) (i : Fin 3) :
    ContinuousOn (fun ξ : PlaneInverseCube.Plane => bgOutH q hq n r x ξ i) {ξ | ξ ≠ 0} :=
  (famBackgroundH_continuousOn (physicalTE q (zero_lt_one.trans_le hq) n r)
    (physicalTE_sigma q (zero_lt_one.trans_le hq) n r) x.support (teCoeff x) (fun q => q.val.1)
    RestrictedTEIncoming.polynomial (fun q => polynomial_homogeneous q) (fun q => polynomial_harmonic q) i).comp
    MaxwellPlaneTail.planePoint_continuous.continuousOn (fun ξ hξ => planePoint_ne_zero ξ hξ)

/-- The outside fields: the background plus a linear radiated field. -/
def outFieldE (radE : ℕ → ℕ → FieldMap) : ℕ → ℕ → FieldMap := fun n r => bgOutE q hq n r + radE n r

def outFieldH (radH : ℕ → ℕ → FieldMap) : ℕ → ℕ → FieldMap := fun n r => bgOutH q hq n r + radH n r

theorem outFieldE_apply (radE : ℕ → ℕ → FieldMap) (x : Vec) (ξ : PlaneInverseCube.Plane) :
    outFieldE q hq radE n r x ξ = bgFieldE q hq n r x (MaxwellPlaneTail.planePoint ξ) + radE n r x ξ := rfl

theorem outFieldH_apply (radH : ℕ → ℕ → FieldMap) (x : Vec) (ξ : PlaneInverseCube.Plane) :
    outFieldH q hq radH n r x ξ = bgFieldH q hq n r x (MaxwellPlaneTail.planePoint ξ) + radH n r x ξ := rfl

/-- **The outside decomposition reduces to the radiated decomposition.**  With the outside fields defined as the TE
background plus a radiated field, the sum structure of `OutsideDecomposition` holds by definition (for every plane
point), so the structure holds as soon as the radiated fields satisfy the uniform radial/tangential decomposition. -/
theorem outsideDecomposition_of_radiated (radE radH : ℕ → ℕ → FieldMap)
    (hrad : ∀ᶠ n : ℕ in atTop, ∀ (N : Nat) (B : Fin N → Vec),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (K1 K2 L1 L2 : ℝ) (r2 : ℕ),
        ∀ r ≥ r2, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
          ∀ ξ : PlaneInverseCube.Plane, RadialPhaseLimit.radius r ≤ ‖ξ‖ →
            OQ14.SourceRemotePlaneBand.Decomp K1 K2 (radE n r x ξ) (MaxwellPlaneTail.planePoint ξ) ∧
              OQ14.SourceRemotePlaneBand.Decomp L1 L2 (radH n r x ξ) (MaxwellPlaneTail.planePoint ξ)) :
    OutsideDecomposition q hq (outFieldE q hq radE) (outFieldH q hq radH)
      (fun n r x ξ => radE n r x ξ) (fun n r x ξ => radH n r x ξ) where
  sumE := fun _ _ _ _ _ => rfl
  sumH := fun _ _ _ _ _ => rfl
  rad := hrad

/-- The inverse-cube flux majorant (T2) of the outside fields from the radiated decomposition. -/
theorem outside_majorant_of_radiated (radE radH : ℕ → ℕ → FieldMap)
    (hOD : ∀ᶠ n : ℕ in atTop, ∀ (N : Nat) (B : Fin N → Vec),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (K1 K2 L1 L2 : ℝ) (r2 : ℕ),
        ∀ r ≥ r2, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
          ∀ ξ : PlaneInverseCube.Plane, RadialPhaseLimit.radius r ≤ ‖ξ‖ →
            OQ14.SourceRemotePlaneBand.Decomp K1 K2 (radE n r x ξ) (MaxwellPlaneTail.planePoint ξ) ∧
              OQ14.SourceRemotePlaneBand.Decomp L1 L2 (radH n r x ξ) (MaxwellPlaneTail.planePoint ξ))
    (n : ℕ) (N : Nat) (B : Fin N → Vec)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)))
    (hradn : ∃ (K1 K2 L1 L2 : ℝ) (r2 : ℕ),
      ∀ r ≥ r2, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
        ∀ ξ : PlaneInverseCube.Plane, RadialPhaseLimit.radius r ≤ ‖ξ‖ →
          OQ14.SourceRemotePlaneBand.Decomp K1 K2 (radE n r x ξ) (MaxwellPlaneTail.planePoint ξ) ∧
            OQ14.SourceRemotePlaneBand.Decomp L1 L2 (radH n r x ξ) (MaxwellPlaneTail.planePoint ξ)) :
    ∃ (C2 : ℝ) (r2 : ℕ), ∀ r ≥ r2, ∀ x ∈ Submodule.span ℂ (Set.range B),
      RestrictedTEIncoming.physicalPower x = 1 → ∀ ξ : PlaneInverseCube.Plane, RadialPhaseLimit.radius r ≤ ‖ξ‖ →
        ‖OQ14.RestrictedTEActualFields.fieldFlux (outFieldE q hq radE n r) (outFieldH q hq radH n r) x ξ‖
          ≤ C2 / ‖ξ‖ ^ 3 :=
  outside_majorant_of_pieces q hq (outFieldE q hq radE) (outFieldH q hq radH)
    (fun n r x ξ => radE n r x ξ) (fun n r x ξ => radH n r x ξ)
    (outsideDecomposition_of_radiated q hq radE radH hOD) n N B horth hradn

end Plane

/-! ### Continuity of the magnetic response of a bounded compactly supported source -/

section Convolution

/-- **A bounded compactly supported source has a continuous response for a locally integrable kernel.**  The
response `x ↦ ∫ ρ y * K (x - y)` of a source `ρ` that is integrable, almost everywhere bounded by `M` and zero
outside the ball of radius `S`, is continuous for every locally integrable kernel `K`: on a neighbourhood of a point
the kernel may be replaced by its restriction to a large ball, which is integrable, hence approximable in `L¹` by
continuous compactly supported kernels (whose response is continuous), and the response changes by at most `M`
times the `L¹` error, uniformly in the point (translation invariance of the Lebesgue measure). -/
theorem response_continuous_of_bounded (K ρ : Sp → ℂ) (hK : LocallyIntegrable K volume)
    (hρ : Integrable ρ volume) (M S : ℝ) (hb : ∀ᵐ y ∂(volume : Measure Sp), ‖ρ y‖ ≤ M)
    (hS : ∀ y : Sp, S < ‖y‖ → ρ y = 0) :
    Continuous (KernelConvolution.response K ρ) := by
  rw [continuous_iff_continuousAt]
  intro x0
  set L : ℝ := S + ‖x0‖ + 1 with hL
  let K' : Sp → ℂ := (closedBall (0 : Sp) L).indicator K
  have hK' : Integrable K' volume := by
    have h : IntegrableOn K (closedBall (0 : Sp) L) volume :=
      hK.integrableOn_isCompact (isCompact_closedBall 0 L)
    exact (integrable_indicator_iff measurableSet_closedBall).mpr h
  let G : Sp → ℂ := fun x => ∫ y, ρ y * K' (x - y)
  have hFG : ∀ x ∈ ball x0 1, KernelConvolution.response K ρ x = G x := by
    intro x hx
    unfold KernelConvolution.response
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : ρ y = 0
    · simp [hy]
    · have hyS : ‖y‖ ≤ S := by
        by_contra h
        exact hy (hS y (not_le.mp h))
      have hxx : ‖x - x0‖ < 1 := by simpa [dist_eq_norm] using hx
      have h1 : ‖x - y‖ ≤ L := by
        calc ‖x - y‖ = ‖(x - x0) + x0 - y‖ := by congr 1; abel
          _ ≤ ‖x - x0‖ + ‖x0‖ + ‖y‖ := by
            calc ‖(x - x0) + x0 - y‖ ≤ ‖(x - x0) + x0‖ + ‖y‖ := norm_sub_le _ _
              _ ≤ ‖x - x0‖ + ‖x0‖ + ‖y‖ := add_le_add_right (norm_add_le _ _) ‖y‖
          _ ≤ L := by rw [hL]; linarith
      simp only [K', indicator_of_mem (mem_closedBall_zero_iff.mpr h1)]
  have hG : ContinuousAt G x0 := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hM : 0 ≤ M := by
      obtain ⟨y, hy⟩ := hb.exists
      exact (norm_nonneg _).trans hy
    have hδ : 0 < ε / (4 * (M + 1)) := by positivity
    obtain ⟨Kc, hKcs, hKci, hKcc, hKcint⟩ := hK'.exists_hasCompactSupport_integral_sub_le hδ
    let Gc : Sp → ℂ := fun x => ∫ y, ρ y * Kc (x - y)
    have hGc : Continuous Gc := by
      have h := hKcs.continuous_convolution_right (ContinuousLinearMap.mul ℂ ℂ) hρ.locallyIntegrable hKcc
      exact h
    have hint : ∀ (F : Sp → ℂ), Integrable F volume → ∀ x : Sp,
        Integrable (fun y => ρ y * F (x - y)) volume := by
      intro F hF x
      exact (hF.comp_sub_left x).bdd_mul' hρ.aestronglyMeasurable hb
    have hbound : ∀ x : Sp, ‖G x - Gc x‖ ≤ M * (ε / (4 * (M + 1))) := by
      intro x
      have e : G x - Gc x = ∫ y, ρ y * (K' (x - y) - Kc (x - y)) := by
        simp only [G, Gc, mul_sub]
        rw [integral_sub (hint K' hK' x) (hint Kc hKcint x)]
      rw [e]
      have hdiff : Integrable (fun y => ‖K' (x - y) - Kc (x - y)‖) volume :=
        ((hK'.sub hKcint).norm).comp_sub_left x
      calc ‖∫ y, ρ y * (K' (x - y) - Kc (x - y))‖
          ≤ ∫ y, M * ‖K' (x - y) - Kc (x - y)‖ := by
            apply norm_integral_le_of_norm_le (hdiff.const_mul M)
            filter_upwards [hb] with y hy
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
        _ = M * ∫ y, ‖K' y - Kc y‖ := by
            rw [integral_const_mul]
            congr 1
            exact integral_sub_left_eq_self (fun y => ‖K' y - Kc y‖) volume x
        _ ≤ M * (ε / (4 * (M + 1))) := mul_le_mul_of_nonneg_left hKci hM
    have hsmall : M * (ε / (4 * (M + 1))) ≤ ε / 4 := by
      have h1 : M * (ε / (4 * (M + 1))) = ε / 4 * (M / (M + 1)) := by
        field_simp
        ring
      rw [h1]
      have h2 : M / (M + 1) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith
      nlinarith [h2]
    obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hGc.continuousAt (ε / 2) (by positivity)
    refine ⟨δ, hδ0, fun x hx => ?_⟩
    have h1 := hδ hx
    rw [dist_eq_norm] at h1 ⊢
    calc ‖G x - G x0‖ = ‖(G x - Gc x) + (Gc x - Gc x0) + (Gc x0 - G x0)‖ := by congr 1; ring
      _ ≤ ‖G x - Gc x‖ + ‖Gc x - Gc x0‖ + ‖Gc x0 - G x0‖ := norm_add₃_le
      _ < ε / 4 + ε / 2 + ε / 4 := by
        have a1 := (hbound x).trans hsmall
        have a3 : ‖Gc x0 - G x0‖ ≤ ε / 4 := by
          rw [norm_sub_rev]
          exact (hbound x0).trans hsmall
        linarith
      _ = ε := by ring
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds x0 one_pos] with x hx
  exact hFG x hx

/-- **Continuity of the magnetic response of a bounded compactly supported source.**  -/
theorem magnetic_continuous_of_bounded (k : ℝ) (ρ : Fin 3 → Sp → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (M S : ℝ) (hb : ∀ j, ∀ᵐ y ∂(volume : Measure Sp), ‖ρ j y‖ ≤ M)
    (hS : ∀ j (y : Sp), S < ‖y‖ → ρ j y = 0) (i : Fin 3) :
    Continuous (fun x => MagneticResponse.magnetic k ρ x i) := by
  have hg (j l : Fin 3) := response_continuous_of_bounded (fun z => GreenKernel.phiGradient k z j) (ρ l)
    (KernelGradient.gradient_locallyIntegrable k j) (hρ l) M S (hb l) (hS l)
  exact continuous_const.mul ((hg (WeakCurl.next i) (WeakCurl.previous i)).sub
    (hg (WeakCurl.previous i) (WeakCurl.next i)))

end Convolution

/-! ### Pointwise identification of the background pair with the continuous total fields -/

section Pointwise
open OQ14.RestrictedTEActualCore OQ14.BackgroundShellCoefficient OQ14.BackgroundModeTE
  OQ14.BackgroundFluxMajorant OQ14.RestrictedTEActualPiecewise OQ14.BackgroundModeMaxwell
  OQ14.SourceRadialSystem OQ14.HarmonicPolynomial

variable {ι : Type*}

/-- The TE polarization of one mode is bounded on all of space (zero in the core and outside the shell, a bounded
permeability times a field continuous on the compact annulus in between). -/
theorem polarization_bounded (d : Data) (P : Poly) :
    ∃ B : ℝ, ∀ (i : Fin 3) (x : Sp), ‖SourceTECorrection.polarization d P i x‖ ≤ B := by
  obtain ⟨Mμ, hMμ0, hMμ⟩ := SourceMuMaterial.mu_bound d
  have hcont : ∀ i : Fin 3, ContinuousOn (fun x : Sp => SourceUnclippedMaxwell.magnetic d P x i)
      {x : Sp | x ≠ 0} := fun i =>
    hform_continuousOn d.l P (fun r => (raw d r).1)
      (continuous_fst.comp_continuousOn (OQ14.RadialGluing.sourceState_continuousOn d.l d.chain d.hR)) i
  have hK : IsCompact (closedBall (0 : Sp) d.X \ ball (0 : Sp) d.R) :=
    (isCompact_closedBall 0 d.X).diff isOpen_ball
  have hsub : (closedBall (0 : Sp) d.X \ ball (0 : Sp) d.R) ⊆ {x : Sp | x ≠ 0} := by
    intro x hx h0
    apply hx.2
    rw [h0]
    simpa using d.hR
  choose Bi hBi using fun i : Fin 3 => hK.exists_bound_of_continuousOn ((hcont i).mono hsub)
  refine ⟨(Mμ + 1) * (∑ i, |Bi i|), fun i x => ?_⟩
  have hB0 : 0 ≤ (Mμ + 1) * (∑ i, |Bi i|) := by positivity
  by_cases hx : x ∈ closedBall (0 : Sp) d.X \ ball (0 : Sp) d.R
  · have hm := hBi i x hx
    have hmu : ‖SourceGeneralMaxwell.mu d ‖x‖ - 1‖ ≤ Mμ + 1 :=
      (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add_right (hMμ ‖x‖) 1)
    have hBi' : ‖SourceUnclippedMaxwell.magnetic d P x i‖ ≤ ∑ j, |Bi j| :=
      hm.trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun j => |Bi j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)))
    change ‖(SourceGeneralMaxwell.mu d ‖x‖ - 1) * SourceUnclippedMaxwell.magnetic d P x i‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul hmu hBi' (norm_nonneg _) (by positivity)
  · have h0 : SourceTECorrection.polarization d P i x = 0 := by
      by_cases h1 : ‖x‖ ≤ d.R
      · exact SourceTECorrection.polarization_inner d P x h1 i
      · by_cases h2 : d.X < ‖x‖
        · exact SourceTECorrection.polarization_outer d P x h2 i
        · exact absurd ⟨mem_closedBall_zero_iff.mpr (not_lt.mp h2),
            fun hb => h1 (mem_ball_zero_iff.mp hb).le⟩ hx
    rw [h0, norm_zero]
    exact hB0

theorem teBackgroundPolarization_bounded (d : Data) (P : Poly) :
    ∃ B : ℝ, ∀ (i : Fin 3) (x : Sp), ‖teBackgroundPolarization d P i x‖ ≤ B := by
  obtain ⟨B, hB⟩ := polarization_bounded d P
  refine ⟨‖kappa d‖ * (B + B), fun i x => ?_⟩
  unfold teBackgroundPolarization
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (norm_nonneg _)
  exact add_le_add (hB i x) (by simpa using hB i x)

theorem famForce_bounded (d0 : Data) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) :
    ∃ B : ℝ, ∀ (i : Fin 3) (x : Sp), ‖famForce d0 s c lq P i x‖ ≤ B := by
  choose Bq hBq using fun q : ι => teBackgroundPolarization_bounded { d0 with l := lq q } (P q)
  refine ⟨∑ q ∈ s, ‖c q‖ * |Bq q|, fun i x => ?_⟩
  unfold famForce
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((hBq q i x).trans (le_abs_self _)) (norm_nonneg _)

variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ)

/-- The TE background electric field is continuous away from the origin. -/
theorem bgFieldE_continuousOn (A : Vec) (i : Fin 3) :
    ContinuousOn (fun x : Sp => bgFieldE q hq n r A x i) {x : Sp | x ≠ 0} :=
  famBackground_continuousOn _ _ _ _ _ i

/-- The TE background magnetic field is continuous away from the origin. -/
theorem bgFieldH_continuousOn (A : Vec) (i : Fin 3) :
    ContinuousOn (fun x : Sp => bgFieldH q hq n r A x i) {x : Sp | x ≠ 0} :=
  famBackgroundH_continuousOn _ (physicalTE_sigma q (zero_lt_one.trans_le hq) n r) _ _ _ _
    (fun q => polynomial_homogeneous q) (fun q => polynomial_harmonic q) i

/-- **The source of the actual shell solution is the explicit TE force.**  The weighted source of the actual shell
solution for the datum of `A` agrees almost everywhere with the bounded explicit force of the family
`famForce` of the physical TE stack. -/
theorem shell_source_ae (A : Vec) (j : Fin 3) :
    DynamicVolume.source (SourcePairedInclusion.shell q hq n r) (shellSol q hq n r A) j =ᵐ[volume]
      famForce (physicalTE q (zero_lt_one.trans_le hq) n r) A.support (teCoeff A) (fun q => q.val.1)
        RestrictedTEIncoming.polynomial j := by
  classical
  have hv := te_coefficient_value q hq n r
  have h1 := te_family_solution (physicalTE q (zero_lt_one.trans_le hq) n r)
    (physicalTE_sigma q (zero_lt_one.trans_le hq) n r) (q ^ 2) (one_le_sq' q hq)
    (physicalTE_parameters q (zero_lt_one.trans_le hq) hq n r) A.support (teCoeff A) (fun q => q.val.1)
    RestrictedTEIncoming.polynomial (fun q => polynomial_homogeneous q) (fun q => polynomial_harmonic q)
  rw [te_finite_datum (physicalTE q (zero_lt_one.trans_le hq) n r) (q ^ 2) (one_le_sq' q hq)
    (physicalTE_parameters q (zero_lt_one.trans_le hq) hq n r) A] at h1
  rw [← solution_congr_value hv.symm,
    ← datum_congr_value hv.symm (shellSupport q hq n r)
      (teSupportData _ (physicalTE q (zero_lt_one.trans_le hq) n r).X (SourceTEWeightedDatum.material_outer _ _
        (SourceMuMaterial.value_complex (physicalTE q (zero_lt_one.trans_le hq) n r) (q ^ 2) (one_le_sq' q hq)
          (physicalTE_parameters q (zero_lt_one.trans_le hq) hq n r))))] at h1
  have hs := famBackgroundDatum_source (physicalTE q (zero_lt_one.trans_le hq) n r) (q ^ 2) (one_le_sq' q hq)
    (physicalTE_parameters q (zero_lt_one.trans_le hq) hq n r) A.support (teCoeff A) (fun q => q.val.1)
    RestrictedTEIncoming.polynomial j
  rw [h1] at hs
  rw [source_congr_value hv.symm]
  exact hs

/-- **The total magnetic field of the actual shell solution is continuous.**  The induced source is almost
everywhere the bounded explicit force, so the gradient-kernel response is continuous
(`magnetic_continuous_of_bounded`). -/
theorem shell_totalMagnetic_continuous (A : Vec) (i : Fin 3) :
    Continuous (fun x => MaterialMaxwell.totalMagnetic (SourcePairedInclusion.shell q hq n r) 1
      (shellSol q hq n r A) (RestrictedTEPlaneLocal.magnetic A) x i) := by
  obtain ⟨B, hB⟩ := famForce_bounded (physicalTE q (zero_lt_one.trans_le hq) n r) A.support (teCoeff A)
    (fun q => q.val.1) RestrictedTEIncoming.polynomial
  have hmag : Continuous (fun x : Sp => RestrictedTEPlaneLocal.magnetic A x i) :=
    (RestrictedTEMaterial.magnetic_smooth A i).continuous
  have hcont := magnetic_continuous_of_bounded 1
    (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) (shellSol q hq n r A))
    (fun j => DynamicVolume.source_integrable _ _ (SourcePairedInclusion.data q hq n r).X
      (shell_vanish_outer q hq n r) j)
    B (SourcePairedInclusion.data q hq n r).X
    (fun j => (shell_source_ae q hq n r A j).mono (fun y hy => by rw [hy]; exact hB j y))
    (fun j y hy => DynamicVolume.source_zero _ _ (SourcePairedInclusion.data q hq n r).X
      (shell_vanish_outer q hq n r) j y (by simpa [mem_closedBall, dist_zero_right, not_le] using hy)) i
  exact hmag.add hcont

/-- **Magnetic side, pointwise.**  Away from the origin the TE background magnetic field is exactly the total
magnetic field of the actual shell solution: both are continuous on the open set `x ≠ 0` and they agree almost
everywhere (`famBackgroundH_ae`). -/
theorem famBackgroundH_eq (A : Vec) (x : Sp) (hx : x ≠ 0) (i : Fin 3) :
    bgFieldH q hq n r A x i = MaterialMaxwell.totalMagnetic (SourcePairedInclusion.shell q hq n r) 1
      (shellSol q hq n r A) (RestrictedTEPlaneLocal.magnetic A) x i := by
  have hae := famBackgroundH_ae q hq n r A i
  have h := Measure.eqOn_open_of_ae_eq (μ := volume) (U := {x : Sp | x ≠ 0}) (ae_restrict_of_ae hae)
    (isOpen_ne : IsOpen {x : Sp | x ≠ 0}) (bgFieldH_continuousOn q hq n r A i)
    (shell_totalMagnetic_continuous q hq n r A i).continuousOn
  exact h hx

end Pointwise

/-! ### The background pair against the combined-solution objects, and the exterior electric field -/

section Corollaries
open OQ14.RestrictedTEActualCore OQ14.BackgroundShellCoefficient OQ14.BackgroundModeTE
  OQ14.BackgroundFluxMajorant OQ14.RestrictedTEActualPiecewise
variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ)

/-- The magnetic background of the shell (the object used in the splitting of the combined solution) is the TE
background magnetic field away from the origin. -/
theorem backgroundMagnetic_eq_bgFieldH (A : Vec) (x : Sp) (hx : x ≠ 0) :
    SourcePairedPlaneIdentification.backgroundMagnetic (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.magnetic A) (fsLin q hq n r A) x =
      bgFieldH q hq n r A x := by
  funext i
  exact (famBackgroundH_eq q hq n r A x hx i).symm

/-- The continuous total magnetic field of the shell solution alone is the TE background magnetic field away
from the origin. -/
theorem continuousTotalMagnetic_shell_eq_bgFieldH (A : Vec) (x : Sp) (hx : x ≠ 0) :
    SourcePairedPlaneIdentification.continuousTotalMagnetic (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.magnetic A) (fsLin q hq n r A) x =
      bgFieldH q hq n r A x := by
  funext i
  exact (famBackgroundH_eq q hq n r A x hx i).symm

/-- **Electric side, pointwise in the exterior.**  Outside the shell the continuous representative of the total
electric field of the actual shell solution (the incident field plus the literal dyadic integral of the induced
source) is the TE background electric field: both are continuous on the open exterior and agree almost
everywhere (`famBackground_ae`). -/
theorem bgFieldE_eq_exterior (A : Vec) (x : Sp) (hx : (SourcePairedInclusion.data q hq n r).X < ‖x‖)
    (i : Fin 3) :
    bgFieldE q hq n r A x i = ExteriorMaterial.total (SourcePairedInclusion.shell q hq n r) 1
      (SourcePairedInclusion.data q hq n r).X (shellSol q hq n r A) (RestrictedTEPlaneLocal.electric A) x i := by
  set X := (SourcePairedInclusion.data q hq n r).X with hX
  have hX0 : 0 < X := (SourcePairedInclusion.data q hq n r).hR.trans_le
    (OQ14.RadialStack.chain_ordered (SourcePairedInclusion.data q hq n r).chain)
  have hU : IsOpen {x : Sp | X < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hsub : {x : Sp | X < ‖x‖} ⊆ {x : Sp | x ≠ 0} := by
    intro y hy h0
    have : X < 0 := by simpa [h0] using hy
    linarith
  have hae : (fun x => bgFieldE q hq n r A x i) =ᵐ[volume] fun x => ExteriorMaterial.total
      (SourcePairedInclusion.shell q hq n r) 1 X (shellSol q hq n r A) (RestrictedTEPlaneLocal.electric A) x i := by
    have h := (famBackground_ae q hq n r A).symm.trans
      (ExteriorMaterial.total_ae (SourcePairedInclusion.shell q hq n r) 1 X (shellSol q hq n r A)
        (RestrictedTEPlaneLocal.electric A) (shell_vanish_outer q hq n r)).symm
    exact h.mono (fun y hy => congrFun hy i)
  have hcont : ContinuousOn (fun x => ExteriorMaterial.total (SourcePairedInclusion.shell q hq n r) 1 X
      (shellSol q hq n r A) (RestrictedTEPlaneLocal.electric A) x i) {x : Sp | X < ‖x‖} := by
    intro y hy
    have hs := ExteriorMaterial.scattered_continuousAt (SourcePairedInclusion.shell q hq n r) 1 X
      (shellSol q hq n r A) (shell_vanish_outer q hq n r) y hy
    have hinc : ContinuousAt (fun x : Sp => RestrictedTEPlaneLocal.electric A x i) y :=
      (RestrictedTEMaterial.electric_smooth A i).continuous.continuousAt
    exact (hinc.add (continuousAt_pi.mp hs i)).continuousWithinAt
  exact Measure.eqOn_open_of_ae_eq (μ := volume) (ae_restrict_of_ae hae) hU
    ((bgFieldE_continuousOn q hq n r A i).mono hsub) hcont hx

/-- The electric background of the shell (incident field plus the literal dyadic integral of the shell
polarization) is the TE background electric field outside the shell. -/
theorem backgroundElectric_eq_bgFieldE_exterior (A : Vec) (x : Sp)
    (hx : (SourcePairedInclusion.data q hq n r).X < ‖x‖) :
    SourcePairedPlaneIdentification.backgroundElectric (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.electric A) (fsLin q hq n r A) x =
      bgFieldE q hq n r A x := by
  funext i
  rw [bgFieldE_eq_exterior q hq n r A x hx i]
  have h2 := ExteriorMaterial.scattered_exterior (SourcePairedInclusion.shell q hq n r) 1
    (SourcePairedInclusion.data q hq n r).X (shellSol q hq n r A) x hx i
  change RestrictedTEPlaneLocal.electric A x i + ExteriorContinuity.electric 1
      (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) (shellSol q hq n r A)) x i =
    RestrictedTEPlaneLocal.electric A x i + ExteriorMaterial.scattered (SourcePairedInclusion.shell q hq n r) 1
      (SourcePairedInclusion.data q hq n r).X (shellSol q hq n r A) x i
  rw [h2]
  rfl

/-- The same on the plane: at the plane points outside the shell the literal electric background is the outside
background field `bgOutE`. -/
theorem backgroundElectric_eq_bgOutE (A : Vec) (ξ : PlaneInverseCube.Plane)
    (hξ : (SourcePairedInclusion.data q hq n r).X < ‖ξ‖) :
    SourcePairedPlaneIdentification.backgroundElectric (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.electric A) (fsLin q hq n r A)
      (MaxwellPlaneTail.planePoint ξ) = bgOutE q hq n r A ξ :=
  backgroundElectric_eq_bgFieldE_exterior q hq n r A _ (by rw [MaxwellPlaneTail.planePoint_norm]; exact hξ)

theorem backgroundMagnetic_eq_bgOutH (A : Vec) (ξ : PlaneInverseCube.Plane) (hξ : ξ ≠ 0) :
    SourcePairedPlaneIdentification.backgroundMagnetic (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.magnetic A) (fsLin q hq n r A)
      (MaxwellPlaneTail.planePoint ξ) = bgOutH q hq n r A ξ :=
  backgroundMagnetic_eq_bgFieldH q hq n r A _ (planePoint_ne_zero ξ hξ)

end Corollaries

end OQ14.RestrictedTEBackgroundOutside

#print axioms OQ14.RestrictedTEBackgroundOutside.weakFirst_of_testMaxwell
#print axioms OQ14.RestrictedTEBackgroundOutside.weakFirst_of_forced
#print axioms OQ14.RestrictedTEBackgroundOutside.magnetic_ae_unique
#print axioms OQ14.RestrictedTEBackgroundOutside.famBackgroundH_apply
#print axioms OQ14.RestrictedTEBackgroundOutside.famBackground_loc
#print axioms OQ14.RestrictedTEBackgroundOutside.famBackgroundH_loc
#print axioms OQ14.RestrictedTEBackgroundOutside.famForce_loc
#print axioms OQ14.RestrictedTEBackgroundOutside.famBackground_forced
#print axioms OQ14.RestrictedTEBackgroundOutside.famBackground_weakFirst
#print axioms OQ14.RestrictedTEBackgroundOutside.shellSol_equation
#print axioms OQ14.RestrictedTEBackgroundOutside.shell_testMaxwell
#print axioms OQ14.RestrictedTEBackgroundOutside.shell_totalMagnetic_loc
#print axioms OQ14.RestrictedTEBackgroundOutside.famBackground_ae
#print axioms OQ14.RestrictedTEBackgroundOutside.famBackgroundH_ae
#print axioms OQ14.RestrictedTEBackgroundOutside.clipped_inverseSigma_one
#print axioms OQ14.RestrictedTEBackgroundOutside.inverseSigma_one
#print axioms OQ14.RestrictedTEBackgroundOutside.bgHalf_continuousOn
#print axioms OQ14.RestrictedTEBackgroundOutside.hform_continuousOn
#print axioms OQ14.RestrictedTEBackgroundOutside.eform_continuousOn
#print axioms OQ14.RestrictedTEBackgroundOutside.backgroundMagnetic_continuousOn
#print axioms OQ14.RestrictedTEBackgroundOutside.backgroundElectric_continuousOn
#print axioms OQ14.RestrictedTEBackgroundOutside.famBackground_continuousOn
#print axioms OQ14.RestrictedTEBackgroundOutside.famBackgroundH_continuousOn
#print axioms OQ14.RestrictedTEBackgroundOutside.bgOutE_apply
#print axioms OQ14.RestrictedTEBackgroundOutside.bgOutH_apply
#print axioms OQ14.RestrictedTEBackgroundOutside.bgOutE_famBackground
#print axioms OQ14.RestrictedTEBackgroundOutside.bgOutH_famBackgroundH
#print axioms OQ14.RestrictedTEBackgroundOutside.planePoint_ne_zero
#print axioms OQ14.RestrictedTEBackgroundOutside.plane_aemeas
#print axioms OQ14.RestrictedTEBackgroundOutside.bgOutE_meas
#print axioms OQ14.RestrictedTEBackgroundOutside.bgOutH_meas
#print axioms OQ14.RestrictedTEBackgroundOutside.bgOutE_continuousOn
#print axioms OQ14.RestrictedTEBackgroundOutside.bgOutH_continuousOn
#print axioms OQ14.RestrictedTEBackgroundOutside.outFieldE_apply
#print axioms OQ14.RestrictedTEBackgroundOutside.outFieldH_apply
#print axioms OQ14.RestrictedTEBackgroundOutside.outsideDecomposition_of_radiated
#print axioms OQ14.RestrictedTEBackgroundOutside.outside_majorant_of_radiated
#print axioms OQ14.RestrictedTEBackgroundOutside.response_continuous_of_bounded
#print axioms OQ14.RestrictedTEBackgroundOutside.magnetic_continuous_of_bounded
#print axioms OQ14.RestrictedTEBackgroundOutside.polarization_bounded
#print axioms OQ14.RestrictedTEBackgroundOutside.teBackgroundPolarization_bounded
#print axioms OQ14.RestrictedTEBackgroundOutside.famForce_bounded
#print axioms OQ14.RestrictedTEBackgroundOutside.bgFieldE_continuousOn
#print axioms OQ14.RestrictedTEBackgroundOutside.bgFieldH_continuousOn
#print axioms OQ14.RestrictedTEBackgroundOutside.shell_source_ae
#print axioms OQ14.RestrictedTEBackgroundOutside.shell_totalMagnetic_continuous
#print axioms OQ14.RestrictedTEBackgroundOutside.famBackgroundH_eq
#print axioms OQ14.RestrictedTEBackgroundOutside.backgroundMagnetic_eq_bgFieldH
#print axioms OQ14.RestrictedTEBackgroundOutside.continuousTotalMagnetic_shell_eq_bgFieldH
#print axioms OQ14.RestrictedTEBackgroundOutside.bgFieldE_eq_exterior
#print axioms OQ14.RestrictedTEBackgroundOutside.backgroundElectric_eq_bgFieldE_exterior
#print axioms OQ14.RestrictedTEBackgroundOutside.backgroundElectric_eq_bgOutE
#print axioms OQ14.RestrictedTEBackgroundOutside.backgroundMagnetic_eq_bgOutH
