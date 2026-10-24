import RestrictedTEL1Assembly
import RestrictedTEActualSquare

/-! End-to-end composition of the counted-subspace theorem with abstract linear plane fields.

The plane flux of a pair of electric and magnetic fields `E, H`, linear in the coefficient vector with values in
functions on the plane, is `crossProduct (E x ξ) (conjugate (H x ξ)) 2` (`fieldFlux`).  This module proves

* `compact_flux_of_uniform_fields`: uniform convergence on a disk of the fields on the basis inputs of an
  orthonormal family, boundedness of the limit fields on the disk and measurability give `L1` convergence of the
  fluxes on the disk, uniformly on the unit-power sphere of the span (the product difference is bounded by the
  field differences times the field bounds, then integrated over the disk);
* `measurable_flux_of_fields` and `fieldFlux_homogeneous`: measurability of the flux and its quadratic
  homogeneity (through `homogeneous_of_linear`);
* the parity total fields `parityE`, `parityH` (`RestrictedTETotalLinear.totalE`/`totalH` with the device source of
  the doubled device at scale `a`), their linearity, continuity, measurability and boundedness on every disk;
* the structure `ActualFieldEstimates`, collecting the three field estimates on a family `E n r`, `H n r` of
  linear fields (measurability, uniform convergence on every disk to the parity total fields at scale
  `(q^n)⁻¹`, inverse-cube tail majorant of the flux on the unit-power sphere of the span of every orthonormal
  family), and `actual_counted_subspaces_of_fields`, the counted-subspace theorem through the fixed square for
  every family of linear fields with `ActualFieldEstimates`.

The tail estimate is also available in the sesquilinear form of fixed pairs of basis inputs
(`unit_tail_of_pair_tails`). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEActualFields
open MeasureTheory Filter Topology Metric Set
open scoped ComplexConjugate

/-- A field family linear in the coefficient vector, with values functions on the plane. -/
abbrev FieldMap := (SymmetricHarmonicJets.Index →₀ ℂ) →ₗ[ℂ] (PlaneInverseCube.Plane → Maxwell.Vector)

/-- The plane flux density `E × conj H` (normal component) of a pair of linear fields. -/
def fieldFlux (E H : FieldMap) (x : SymmetricHarmonicJets.Index →₀ ℂ) (ξ : PlaneInverseCube.Plane) : ℂ :=
  crossProduct (E x ξ) (Maxwell.conjugate (H x ξ)) 2

theorem fieldFlux_eq (E H : FieldMap) (x : SymmetricHarmonicJets.Index →₀ ℂ) (ξ : PlaneInverseCube.Plane) :
    fieldFlux E H x ξ = E x ξ 0 * conj (H x ξ 1) - E x ξ 1 * conj (H x ξ 0) := by
  unfold fieldFlux
  rw [RestrictedTETotalLinear.cross_two]
  rfl

theorem field_expand {κ : Type*} [Fintype κ] (F : FieldMap) (A : κ → SymmetricHarmonicJets.Index →₀ ℂ)
    (c : κ → ℂ) (ξ : PlaneInverseCube.Plane) (i : Fin 3) :
    F (∑ k, c k • A k) ξ i = ∑ k, c k * F (A k) ξ i := by
  rw [map_sum]
  simp [map_smul, Finset.sum_apply]

theorem unit_coeff_bound {κ : Type*} [Fintype κ] (A : κ → SymmetricHarmonicJets.Index →₀ ℂ)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k))) (cf : κ → ℂ)
    (hpow : RestrictedTEIncoming.physicalPower (∑ k, cf k • A k) = 1) : ∀ k, ‖cf k‖ ≤ 1 := by
  have hsum : (∑ k, ‖cf k‖ ^ 2) = 1 := by
    rw [← RestrictedTEPlaneJets.power_comb A horth cf]
    exact hpow
  intro k
  have h1 : ‖cf k‖ ^ 2 ≤ ∑ k, ‖cf k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖cf k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  by_contra hne
  push_neg at hne
  nlinarith [norm_nonneg (cf k)]

theorem basis_power {κ : Type*} [Fintype κ] (A : κ → SymmetricHarmonicJets.Index →₀ ℂ)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k))) (k : κ) :
    RestrictedTEIncoming.physicalPower (A k) = 1 := by
  rw [← RestrictedTEInput.input_norm_sq, horth.1 k]
  norm_num

/-- The product `e conj h` is stable under small perturbations of `e` and `h` of size `δ` around bounded values. -/
theorem prod_diff (e e' h h' : ℂ) (δ M : ℝ) (he : ‖e - e'‖ ≤ δ) (hh : ‖h - h'‖ ≤ δ) (he' : ‖e'‖ ≤ M)
    (hh' : ‖h'‖ ≤ M) : ‖e * conj h - e' * conj h'‖ ≤ δ * (M + δ) + M * δ := by
  have hid : e * conj h - e' * conj h' = (e - e') * conj h + e' * conj (h - h') := by
    rw [map_sub]
    ring
  have hδ : 0 ≤ δ := (norm_nonneg _).trans he
  have hM : 0 ≤ M := (norm_nonneg _).trans he'
  have hhb : ‖h‖ ≤ M + δ := by
    calc ‖h‖ = ‖h' + (h - h')‖ := by rw [add_sub_cancel]
      _ ≤ ‖h'‖ + ‖h - h'‖ := norm_add_le _ _
      _ ≤ M + δ := add_le_add hh' hh
  rw [hid]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul he hhb (norm_nonneg _) hδ
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul he' hh (norm_nonneg _) hM

theorem measurable_flux_of_fields (E H : FieldMap)
    (hE : ∀ x i, AEStronglyMeasurable (fun ξ => E x ξ i) volume)
    (hH : ∀ x i, AEStronglyMeasurable (fun ξ => H x ξ i) volume) (x : SymmetricHarmonicJets.Index →₀ ℂ) :
    AEStronglyMeasurable (fieldFlux E H x) volume := by
  have : fieldFlux E H x = fun ξ => E x ξ 0 * conj (H x ξ 1) - E x ξ 1 * conj (H x ξ 0) :=
    funext (fieldFlux_eq E H x)
  rw [this]
  exact ((hE x 0).mul (Complex.continuous_conj.comp_aestronglyMeasurable (hH x 1))).sub
    ((hE x 1).mul (Complex.continuous_conj.comp_aestronglyMeasurable (hH x 0)))

theorem fieldFlux_homogeneous (E H : ℕ → ℕ → FieldMap) :
    OQ14.RestrictedTEActualCounting.HomogeneousFlux (fun n r x => fieldFlux (E n r) (H n r) x) :=
  OQ14.RestrictedTEL1Assembly.homogeneous_of_linear (fun n r x ξ => E n r x ξ) (fun n r x ξ => H n r x ξ)
    (fun n r z x ξ => by beta_reduce; rw [map_smul]; rfl) (fun n r z x ξ => by beta_reduce; rw [map_smul]; rfl)

/-- Compact `L1` convergence of the plane fluxes from uniform convergence of the fields on the basis inputs. -/
theorem compact_flux_of_uniform_fields {κ : Type*} [Fintype κ] (A : κ → SymmetricHarmonicJets.Index →₀ ℂ)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)))
    (E H : ℕ → FieldMap) (E' H' : FieldMap)
    (hEa : ∀ (k : κ) (ρ0 : ℝ), 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop,
      ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i, ‖E r (A k) ξ i - E' (A k) ξ i‖ ≤ ε)
    (hHa : ∀ (k : κ) (ρ0 : ℝ), 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop,
      ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i, ‖H r (A k) ξ i - H' (A k) ξ i‖ ≤ ε)
    (hEb : ∀ (k : κ) (ρ0 : ℝ), 0 < ρ0 → ∃ B : ℝ, ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i,
      ‖E' (A k) ξ i‖ ≤ B)
    (hHb : ∀ (k : κ) (ρ0 : ℝ), 0 < ρ0 → ∃ B : ℝ, ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i,
      ‖H' (A k) ξ i‖ ≤ B)
    (hmE : ∀ r x i, AEStronglyMeasurable (fun ξ => E r x ξ i) volume)
    (hmH : ∀ r x i, AEStronglyMeasurable (fun ξ => H r x ξ i) volume)
    (hmE' : ∀ x i, AEStronglyMeasurable (fun ξ => E' x ξ i) volume)
    (hmH' : ∀ x i, AEStronglyMeasurable (fun ξ => H' x ξ i) volume) :
    ∀ ρ0 : ℝ, 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop,
      ∀ x ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower x = 1 →
        IntegrableOn (fun ξ => fieldFlux (E r) (H r) x ξ - fieldFlux E' H' x ξ) (closedBall 0 ρ0) volume ∧
        ∫ ξ in closedBall 0 ρ0, ‖fieldFlux (E r) (H r) x ξ - fieldFlux E' H' x ξ‖ ≤ ε := by
  intro ρ0 hρ0 ε hε
  choose BE hBE using fun k => hEb k ρ0 hρ0
  choose BH hBH using fun k => hHb k ρ0 hρ0
  set M : ℝ := (∑ k, |BE k|) + ∑ k, |BH k| with hM
  have hsE : 0 ≤ ∑ k, |BE k| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hsH : 0 ≤ ∑ k, |BH k| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hM0 : 0 ≤ M := add_nonneg hsE hsH
  set V0 : ℝ := volume.real (closedBall (0 : PlaneInverseCube.Plane) ρ0) with hV0
  have hV00 : 0 ≤ V0 := measureReal_nonneg
  have hVfin : volume (closedBall (0 : PlaneInverseCube.Plane) ρ0) ≠ ⊤ :=
    (isCompact_closedBall (0 : PlaneInverseCube.Plane) ρ0).measure_lt_top.ne
  set η : ℝ := ε / (V0 + 1) with hη
  have hη0 : 0 < η := by positivity
  set δ : ℝ := min 1 (η / (2 * (2 * M + 1))) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδη : 2 * δ * (2 * M + 1) ≤ η := by
    have h1 : δ ≤ η / (2 * (2 * M + 1)) := min_le_right _ _
    have hp : 0 < 2 * (2 * M + 1) := by positivity
    rw [le_div_iff₀ hp] at h1
    linarith
  set Nn : ℝ := (Fintype.card κ : ℝ) + 1 with hNn
  have hNn0 : 0 < Nn := by positivity
  set εb : ℝ := δ / Nn with hεb
  have hεb0 : 0 < εb := by positivity
  filter_upwards [Filter.eventually_all.2 (fun k => hEa k ρ0 hρ0 εb hεb0),
    Filter.eventually_all.2 (fun k => hHa k ρ0 hρ0 εb hεb0)] with r hE hH
  intro x hx hpow
  obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  have hcf := unit_coeff_bound A horth cf hpow
  have hpt : ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 →
      ‖fieldFlux (E r) (H r) (∑ k, cf k • A k) ξ - fieldFlux E' H' (∑ k, cf k • A k) ξ‖ ≤ η := by
    intro ξ hξ
    have hdiff : ∀ (F F' : FieldMap), (∀ k, ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i,
        ‖F (A k) ξ i - F' (A k) ξ i‖ ≤ εb) → ∀ i, ‖F (∑ k, cf k • A k) ξ i - F' (∑ k, cf k • A k) ξ i‖ ≤ δ := by
      intro F F' hF i
      rw [field_expand F A cf ξ i, field_expand F' A cf ξ i, ← Finset.sum_sub_distrib]
      calc ‖∑ k, (cf k * F (A k) ξ i - cf k * F' (A k) ξ i)‖
          ≤ ∑ k, ‖cf k * F (A k) ξ i - cf k * F' (A k) ξ i‖ := norm_sum_le _ _
        _ ≤ ∑ _k : κ, εb := Finset.sum_le_sum (fun k _ => by
            rw [← mul_sub, norm_mul]
            exact (mul_le_of_le_one_left (norm_nonneg _) (hcf k)).trans (hF k ξ hξ i))
        _ = (Fintype.card κ : ℝ) * εb := by simp
        _ ≤ Nn * εb := mul_le_mul_of_nonneg_right (by rw [hNn]; linarith) hεb0.le
        _ = δ := by rw [hεb]; field_simp
    have hbd : ∀ (F' : FieldMap) (B : κ → ℝ), (∀ k, ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i,
        ‖F' (A k) ξ i‖ ≤ B k) → (∑ k, |B k|) ≤ M → ∀ i, ‖F' (∑ k, cf k • A k) ξ i‖ ≤ M := by
      intro F' B hB hBM i
      rw [field_expand F' A cf ξ i]
      calc ‖∑ k, cf k * F' (A k) ξ i‖ ≤ ∑ k, ‖cf k * F' (A k) ξ i‖ := norm_sum_le _ _
        _ ≤ ∑ k, |B k| := Finset.sum_le_sum (fun k _ => by
            rw [norm_mul]
            exact (mul_le_of_le_one_left (norm_nonneg _) (hcf k)).trans ((hB k ξ hξ i).trans (le_abs_self _)))
        _ ≤ M := hBM
    have hdE := hdiff (E r) E' hE
    have hdH := hdiff (H r) H' hH
    have hbE := hbd E' BE hBE (by rw [hM]; linarith)
    have hbH := hbd H' BH hBH (by rw [hM]; linarith)
    rw [fieldFlux_eq, fieldFlux_eq]
    have h0 := prod_diff (E r (∑ k, cf k • A k) ξ 0) (E' (∑ k, cf k • A k) ξ 0) (H r (∑ k, cf k • A k) ξ 1)
      (H' (∑ k, cf k • A k) ξ 1) δ M (hdE 0) (hdH 1) (hbE 0) (hbH 1)
    have h1 := prod_diff (E r (∑ k, cf k • A k) ξ 1) (E' (∑ k, cf k • A k) ξ 1) (H r (∑ k, cf k • A k) ξ 0)
      (H' (∑ k, cf k • A k) ξ 0) δ M (hdE 1) (hdH 0) (hbE 1) (hbH 0)
    rw [show ∀ a0 a1 b0 b1 a0' a1' b0' b1' : ℂ,
        (a0 * conj b1 - a1 * conj b0) - (a0' * conj b1' - a1' * conj b0') =
          (a0 * conj b1 - a0' * conj b1') - (a1 * conj b0 - a1' * conj b0') from
        fun _ _ _ _ _ _ _ _ => by ring]
    refine (norm_sub_le _ _).trans ?_
    have : δ * (M + δ) + M * δ + (δ * (M + δ) + M * δ) ≤ 2 * δ * (2 * M + 1) := by
      nlinarith [hδ0, hδ1, hM0]
    linarith
  have hmeas : AEStronglyMeasurable
      (fun ξ => fieldFlux (E r) (H r) (∑ k, cf k • A k) ξ - fieldFlux E' H' (∑ k, cf k • A k) ξ) volume :=
    (measurable_flux_of_fields (E r) (H r) (hmE r) (hmH r) _).sub (measurable_flux_of_fields E' H' hmE' hmH' _)
  have hbound : ∀ᵐ ξ ∂(volume.restrict (closedBall (0 : PlaneInverseCube.Plane) ρ0)),
      ‖fieldFlux (E r) (H r) (∑ k, cf k • A k) ξ - fieldFlux E' H' (∑ k, cf k • A k) ξ‖ ≤ η := by
    rw [ae_restrict_iff' measurableSet_closedBall]
    exact Eventually.of_forall (fun ξ hξ => hpt ξ (by simpa using hξ))
  have hint := Measure.integrableOn_of_bounded hVfin hmeas hbound
  refine ⟨hint, ?_⟩
  calc ∫ ξ in closedBall (0 : PlaneInverseCube.Plane) ρ0,
        ‖fieldFlux (E r) (H r) (∑ k, cf k • A k) ξ - fieldFlux E' H' (∑ k, cf k • A k) ξ‖
      ≤ ∫ _ξ in closedBall (0 : PlaneInverseCube.Plane) ρ0, η :=
        setIntegral_mono_on hint.norm (integrableOn_const.mpr (Or.inr (lt_top_iff_ne_top.mpr hVfin)))
          measurableSet_closedBall (fun ξ hξ => hpt ξ (by simpa using hξ))
    _ = V0 * η := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ ε := by
        rw [hη, ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith

/-! ### The parity total fields of the doubled device -/

section Parity
open OQ14.RestrictedTEActualCounting OQ14.RestrictedTEPartnerSmallness OQ14.RestrictedTEDipoleProfile
  OQ14.RestrictedTEConcreteDevice

/-- The parity total electric field of the concrete doubled device at scale `a`, at a plane point: the field
`ParityPlaneFields.totalElectric 1 (1/a) (source x a) (electric (a⁻¹ x))` of `RestrictedTETotalLinear.totalE`
with the device source of the finite-ball inverse (gain constant `b = 1`, so `1/a = q^n` at `a = (q^n)⁻¹`). -/
def parityE {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ)
    (hχ : 0 < χ) (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (a : ℝ)
    (x : SymmetricHarmonicJets.Index →₀ ℂ) (ξ : PlaneInverseCube.Plane) : Maxwell.Vector :=
  RestrictedTETotalLinear.totalE (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
    (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 hρ hχ.le
    (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi) a x ξ

/-- The parity total magnetic field of the concrete doubled device at scale `a`, at a plane point. -/
def parityH {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ)
    (hχ : 0 < χ) (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (a : ℝ)
    (x : SymmetricHarmonicJets.Index →₀ ℂ) (ξ : PlaneInverseCube.Plane) : Maxwell.Vector :=
  RestrictedTETotalLinear.totalH (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
    (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 hρ hχ.le
    (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi) a x ξ

/-- The parity flux is the flux of the parity total fields. -/
theorem parityFlux_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ)
    (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (a : ℝ)
    (x : SymmetricHarmonicJets.Index →₀ ℂ) (ξ : PlaneInverseCube.Plane) :
    parityFlux r0 y ρ χ h R hρ hχ hi a x ξ =
      crossProduct (parityE r0 y ρ χ h R hρ hχ hi a x ξ)
        (Maxwell.conjugate (parityH r0 y ρ χ h R hρ hχ hi a x ξ)) 2 := rfl

/-- The parity total electric field as a linear map of the coefficient vector, at scales `a ∈ (0,1]` when
`ρ < h` (the gap of the device is `min((h-ρ)a, 1)`). -/
def parityEMap {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ)
    (hχ : 0 < χ) (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R)
    (hρh : ρ < h) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) : FieldMap where
  toFun x ξ := parityE r0 y ρ χ h R hρ hχ hi a x ξ
  map_add' x w := by
    funext ξ
    exact (RestrictedTETotalLinear.totalEMap (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
      (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 _ a hρ hχ.le
      (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
      (OQ14.RestrictedTEL1Assembly.parity_gap r0 y ρ h hρ hρh a ha ha1).1 ha ha1
      (OQ14.RestrictedTEL1Assembly.parity_gap r0 y ρ h hρ hρh a ha ha1).2 ξ).map_add x w
  map_smul' z x := by
    funext ξ
    exact (RestrictedTETotalLinear.totalEMap (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
      (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 _ a hρ hχ.le
      (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
      (OQ14.RestrictedTEL1Assembly.parity_gap r0 y ρ h hρ hρh a ha ha1).1 ha ha1
      (OQ14.RestrictedTEL1Assembly.parity_gap r0 y ρ h hρ hρh a ha ha1).2 ξ).map_smul z x

/-- The parity total magnetic field as a linear map of the coefficient vector. -/
def parityHMap {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ)
    (hχ : 0 < χ) (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R)
    (hρh : ρ < h) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) : FieldMap where
  toFun x ξ := parityH r0 y ρ χ h R hρ hχ hi a x ξ
  map_add' x w := by
    funext ξ
    exact (RestrictedTETotalLinear.totalHMap (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
      (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 _ a hρ hχ.le
      (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
      (OQ14.RestrictedTEL1Assembly.parity_gap r0 y ρ h hρ hρh a ha ha1).1 ha ha1
      (OQ14.RestrictedTEL1Assembly.parity_gap r0 y ρ h hρ hρh a ha ha1).2 ξ).map_add x w
  map_smul' z x := by
    funext ξ
    exact (RestrictedTETotalLinear.totalHMap (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
      (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 _ a hρ hχ.le
      (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
      (OQ14.RestrictedTEL1Assembly.parity_gap r0 y ρ h hρ hρh a ha ha1).1 ha ha1
      (OQ14.RestrictedTEL1Assembly.parity_gap r0 y ρ h hρ hρh a ha ha1).2 ξ).map_smul z x

/-- The parity flux is the flux of the linear parity fields. -/
theorem parityFlux_eq_fieldFlux {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hρh : ρ < h) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (x : SymmetricHarmonicJets.Index →₀ ℂ) (ξ : PlaneInverseCube.Plane) :
    parityFlux r0 y ρ χ h R hρ hχ hi a x ξ =
      fieldFlux (parityEMap r0 y ρ χ h R hρ hχ hi hρh a ha ha1) (parityHMap r0 y ρ χ h R hρ hχ hi hρh a ha ha1)
        x ξ := rfl

/-- The coordinates of the parity total electric field are continuous on the plane. -/
theorem parityE_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ)
    (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hρh : ρ < h) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (x : SymmetricHarmonicJets.Index →₀ ℂ) (i : Fin 3) :
    Continuous (fun ξ : PlaneInverseCube.Plane => parityE r0 y ρ χ h R hρ hχ hi a x ξ i) := by
  obtain ⟨hd, hh⟩ := OQ14.RestrictedTEL1Assembly.parity_gap r0 y ρ h hρ hρh a ha ha1
  have hS := RestrictedTEFiniteBalls.source_admissible
    (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre (fun l => abovePoint (hpoint r0 y l) (h * a)))
    ρ χ R 1 (min ((h - ρ) * a) 1) a hρ hχ.le
    (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
    (fun a => (a : ℂ)⁻¹ • x) ha ha1 hh
  have h1 := (RestrictedTEPlaneJets.electric_continuous ((a : ℂ)⁻¹ • x) i).comp
    MaxwellPlaneTail.planePoint_continuous
  have h2 := PlaneSourceKernel.electric_plane_continuous 1 R _ hd _ hS i
  have h3 := (ParityPlaneFields.electric_continuous true 1 _ hS.integrable i).comp
    MaxwellPlaneTail.planePoint_continuous
  have h4 := (ParityPlaneFields.electric_continuous false 1 _ hS.integrable i).comp
    MaxwellPlaneTail.planePoint_continuous
  exact ((h1.add h2).add (continuous_const.mul h3)).add (continuous_const.mul h4)

/-- The coordinates of the parity total magnetic field are continuous on the plane. -/
theorem parityH_continuous {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ)
    (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hρh : ρ < h) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (x : SymmetricHarmonicJets.Index →₀ ℂ) (i : Fin 3) :
    Continuous (fun ξ : PlaneInverseCube.Plane => parityH r0 y ρ χ h R hρ hχ hi a x ξ i) := by
  obtain ⟨hd, hh⟩ := OQ14.RestrictedTEL1Assembly.parity_gap r0 y ρ h hρ hρh a ha ha1
  have hS := RestrictedTEFiniteBalls.source_admissible
    (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre (fun l => abovePoint (hpoint r0 y l) (h * a)))
    ρ χ R 1 (min ((h - ρ) * a) 1) a hρ hχ.le
    (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
    (fun a => (a : ℂ)⁻¹ • x) ha ha1 hh
  have h1 := (RestrictedTEMagnetic.magnetic_continuous ((a : ℂ)⁻¹ • x) i).comp
    MaxwellPlaneTail.planePoint_continuous
  have h2 := PlaneSourceKernel.magnetic_plane_continuous 1 R _ hd _ hS i
  have h3 := (ParityPlaneFields.magnetic_continuous true 1 _ hS.integrable i).comp
    MaxwellPlaneTail.planePoint_continuous
  have h4 := (ParityPlaneFields.magnetic_continuous false 1 _ hS.integrable i).comp
    MaxwellPlaneTail.planePoint_continuous
  exact ((h1.add h2).add (continuous_const.mul h3)).add (continuous_const.mul h4)

/-- A continuous vector-valued plane function is bounded on every disk (uniformly in the coordinate). -/
theorem bounded_on_disk (f : PlaneInverseCube.Plane → Maxwell.Vector)
    (hf : ∀ i, Continuous (fun ξ => f ξ i)) (ρ0 : ℝ) :
    ∃ B : ℝ, ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i, ‖f ξ i‖ ≤ B := by
  have hb := fun i => (isCompact_closedBall (0 : PlaneInverseCube.Plane) ρ0).exists_bound_of_continuousOn
    (hf i).continuousOn
  choose C hC using hb
  refine ⟨∑ i, |C i|, fun ξ hξ i => ?_⟩
  have h1 : ‖f ξ i‖ ≤ C i := hC i ξ (by simpa using hξ)
  exact h1.trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))

end Parity

/-! ### The tail estimate in the sesquilinear form of fixed pairs of inputs -/

/-- Inverse-cube tails of the fluxes of fixed pairs of basis inputs (large shell index) give the tail majorant of
the flux uniformly on the unit-power sphere of the span of an orthonormal family. -/
theorem unit_tail_of_pair_tails {κ : Type*} [Fintype κ] (E H : ℕ → FieldMap)
    (A : κ → SymmetricHarmonicJets.Index →₀ ℂ)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)))
    (hpair : ∀ i j, ∃ (K T : ℝ) (r1 : ℕ), ∀ r ≥ r1, ∀ ξ : PlaneInverseCube.Plane, T < ‖ξ‖ →
      ‖crossProduct (E r (A i) ξ) (Maxwell.conjugate (H r (A j) ξ)) 2‖ ≤ K / ‖ξ‖ ^ 3) :
    ∃ (C T : ℝ) (r1 : ℕ), ∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range A),
      RestrictedTEIncoming.physicalPower x = 1 → ∀ ξ : PlaneInverseCube.Plane, T < ‖ξ‖ →
        ‖fieldFlux (E r) (H r) x ξ‖ ≤ C / ‖ξ‖ ^ 3 := by
  choose K T r1 hKT using hpair
  refine ⟨∑ i, ∑ j, K i j, ∑ i, ∑ j, |T i j|, ∑ i, ∑ j, r1 i j, ?_⟩
  intro r hr x hx hpow ξ hξ
  obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  have hcf := unit_coeff_bound A horth cf hpow
  have hr' (i j : κ) : r1 i j ≤ r := by
    refine le_trans ?_ hr
    exact (Finset.single_le_sum (f := fun j => r1 i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, r1 i j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hTle (i j : κ) : T i j < ‖ξ‖ := by
    refine lt_of_le_of_lt ((le_abs_self _).trans ?_) hξ
    exact (Finset.single_le_sum (f := fun j => |T i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |T i j|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i))
  have hexp : fieldFlux (E r) (H r) (∑ k, cf k • A k) ξ =
      ∑ i, ∑ j, (cf i * conj (cf j)) * crossProduct (E r (A i) ξ) (Maxwell.conjugate (H r (A j) ξ)) 2 := by
    rw [fieldFlux_eq, field_expand (E r) A cf ξ 0, field_expand (E r) A cf ξ 1, field_expand (H r) A cf ξ 0,
      field_expand (H r) A cf ξ 1]
    simp only [map_sum, map_mul, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [RestrictedTETotalLinear.cross_two]
    simp only [Maxwell.conjugate]
    ring
  rw [hexp]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖∑ j, (cf i * conj (cf j)) * crossProduct (E r (A i) ξ) (Maxwell.conjugate (H r (A j) ξ)) 2‖
      ≤ ∑ i, ∑ j, K i j / ‖ξ‖ ^ 3 := by
        refine Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_)))
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have hc : ‖cf i‖ * ‖cf j‖ ≤ 1 := by
          nlinarith [norm_nonneg (cf i), norm_nonneg (cf j), hcf i, hcf j]
        exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hKT i j r (hr' i j) ξ (hTle i j))
    _ = (∑ i, ∑ j, K i j) / ‖ξ‖ ^ 3 := by simp only [Finset.sum_div]

/-! ### The three field estimates and the interface -/

section Estimates
open OQ14.RestrictedTEActualCounting OQ14.RestrictedTEPartnerSmallness OQ14.RestrictedTEDipoleProfile
  OQ14.RestrictedTEConcreteDevice

/-- The three estimates on the actual plane fields `E n r`, `H n r` (gain index `n`, shell index `r`, linear in the
coefficient vector) that remain after this module, for the concrete doubled device `(r0, y, ρ, χ, h, R)` and the
shell ratio `q`:
* `meas`: every coordinate of the fields is a.e.-strongly measurable on the plane;
* `conv`: for every unit-power input `x`, on every disk, the coordinates of `E n r x`, `H n r x` converge
  uniformly, as `r → ∞`, to those of the parity total fields `parityE`, `parityH` (that is
  `RestrictedTETotalLinear.totalE`/`totalH` with the device source) at the matching scale `(q^n)⁻¹`;
* `tail`: for every orthonormal family and every `n`, an inverse-cube pointwise majorant of the flux
  `E × conj H` on the unit-power sphere of the span, for large `r` and `‖ξ‖` large. -/
structure ActualFieldEstimates {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ)
    (E H : ℕ → ℕ → FieldMap) : Prop where
  meas : ∀ (n r : ℕ) (x : SymmetricHarmonicJets.Index →₀ ℂ) (i : Fin 3),
    AEStronglyMeasurable (fun ξ => E n r x ξ i) volume ∧ AEStronglyMeasurable (fun ξ => H n r x ξ i) volume
  conv : ∀ (n : ℕ) (x : SymmetricHarmonicJets.Index →₀ ℂ), RestrictedTEIncoming.physicalPower x = 1 →
    ∀ ρ0 : ℝ, 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 →
      ∀ i, ‖E n r x ξ i - parityE r0 y ρ χ h R hρ hχ hi (scale q n) x ξ i‖ ≤ ε ∧
        ‖H n r x ξ i - parityH r0 y ρ χ h R hρ hχ hi (scale q n) x ξ i‖ ≤ ε
  tail : ∀ (N : ℕ) (B : Fin N → SymmetricHarmonicJets.Index →₀ ℂ),
    Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∀ n : ℕ, ∃ (C ρ1 : ℝ) (r1 : ℕ),
      ∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
        ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ → ‖fieldFlux (E n r) (H n r) x ξ‖ ≤ C / ‖ξ‖ ^ 3

/-- The tail estimate of `ActualFieldEstimates` from inverse-cube majorants of the fluxes of fixed pairs of
unit-power inputs. -/
theorem ActualFieldEstimates.of_pair_tails {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ)
    (E H : ℕ → ℕ → FieldMap)
    (hmeas : ∀ (n r : ℕ) (x : SymmetricHarmonicJets.Index →₀ ℂ) (i : Fin 3),
      AEStronglyMeasurable (fun ξ => E n r x ξ i) volume ∧ AEStronglyMeasurable (fun ξ => H n r x ξ i) volume)
    (hconv : ∀ (n : ℕ) (x : SymmetricHarmonicJets.Index →₀ ℂ), RestrictedTEIncoming.physicalPower x = 1 →
      ∀ ρ0 : ℝ, 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 →
        ∀ i, ‖E n r x ξ i - parityE r0 y ρ χ h R hρ hχ hi (scale q n) x ξ i‖ ≤ ε ∧
          ‖H n r x ξ i - parityH r0 y ρ χ h R hρ hχ hi (scale q n) x ξ i‖ ≤ ε)
    (hpair : ∀ (n : ℕ) (x w : SymmetricHarmonicJets.Index →₀ ℂ), RestrictedTEIncoming.physicalPower x = 1 →
      RestrictedTEIncoming.physicalPower w = 1 → ∃ (C ρ1 : ℝ) (r1 : ℕ), ∀ r ≥ r1,
        ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ →
          ‖crossProduct (E n r x ξ) (Maxwell.conjugate (H n r w ξ)) 2‖ ≤ C / ‖ξ‖ ^ 3) :
    ActualFieldEstimates r0 y ρ χ h R hρ hχ hi q E H where
  meas := hmeas
  conv := hconv
  tail := by
    intro N B horth n
    obtain ⟨C, T, r1, h1⟩ := unit_tail_of_pair_tails (E n) (H n) B horth (fun i j => by
      obtain ⟨C, ρ1, r1, h1⟩ := hpair n (B i) (B j) (basis_power B horth i) (basis_power B horth j)
      exact ⟨C, ρ1, r1, fun r hr ξ hξ => h1 r hr ξ hξ.le⟩)
    exact ⟨C, T + 1, r1, fun r hr x hx hp ξ hξ => h1 r hr x hx hp ξ (by linarith)⟩

/-- `L1Interface` of the concrete doubled device for the plane flux of the fields `E n r`, `H n r`, from
`ActualFieldEstimates`. -/
theorem L1Interface_of_field_estimates {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hR : 0 ≤ R)
    (hρh : ρ < h) (q : ℝ) (hq : 1 < q) (E H : ℕ → ℕ → FieldMap)
    (hest : ActualFieldEstimates r0 y ρ χ h R hρ hχ hi q E H) :
    L1Interface r0 y ρ χ h R hρ hχ hi q (fun n r x => fieldFlux (E n r) (H n r) x) := by
  refine OQ14.RestrictedTEL1Assembly.L1Interface_of_actual_estimates r0 y ρ χ h R hρ hχ hi hR hρh q hq _ ?_ ?_
    hest.tail
  · intro n r x
    exact measurable_flux_of_fields (E n r) (H n r) (fun x i => (hest.meas n r x i).1)
      (fun x i => (hest.meas n r x i).2) x
  · intro N B horth n ρ0 hρ0 ε hε
    have ha := scale_pos hq n
    have ha1 := scale_le_one hq.le n
    exact compact_flux_of_uniform_fields B horth (E n) (H n)
      (parityEMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) ha ha1)
      (parityHMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) ha ha1)
      (fun k ρ0 hρ0 ε hε => (hest.conv n (B k) (basis_power B horth k) ρ0 hρ0 ε hε).mono
        (fun r hr ξ hξ i => (hr ξ hξ i).1))
      (fun k ρ0 hρ0 ε hε => (hest.conv n (B k) (basis_power B horth k) ρ0 hρ0 ε hε).mono
        (fun r hr ξ hξ i => (hr ξ hξ i).2))
      (fun k ρ0 _ => bounded_on_disk (parityE r0 y ρ χ h R hρ hχ hi (scale q n) (B k))
        (fun i => parityE_continuous r0 y ρ χ h R hρ hχ hi hρh (scale q n) ha ha1 (B k) i) ρ0)
      (fun k ρ0 _ => bounded_on_disk (parityH r0 y ρ χ h R hρ hχ hi (scale q n) (B k))
        (fun i => parityH_continuous r0 y ρ χ h R hρ hχ hi hρh (scale q n) ha ha1 (B k) i) ρ0)
      (fun r x i => (hest.meas n r x i).1) (fun r x i => (hest.meas n r x i).2)
      (fun x i => (parityE_continuous r0 y ρ χ h R hρ hχ hi hρh (scale q n) ha ha1 x i).aestronglyMeasurable)
      (fun x i => (parityH_continuous r0 y ρ χ h R hρ hχ hi hρh (scale q n) ha ha1 x i).aestronglyMeasurable)
      ρ0 hρ0 ε hε

end Estimates

/-! ### The counted-subspace theorem in terms of plane fields -/

section Final
open OQ14.RestrictedTEPassageTransfer OQ14.RestrictedTEActualCounting OQ14.RestrictedTEActualWindow
  OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEConcreteDoubled OQ14.RestrictedTEPartnerBalls OQ14.RestrictedTEPlaneJets
  OQ14.RestrictedTEPartnerCount OQ14.RestrictedTEPartnerSmallness OQ14.ChannelMaterialThroughput
  OQ14.RestrictedTEActualSquare

/-- The counted-subspace theorem of the actual device through the fixed square `Dsq L`, in terms of abstract plane
fields.  For every `ε₊ > 1`, `N`, thresholds `0 < η < δ`, `τ ≤ 1` and half-side `L > 0` there are the device
parameters and an orthonormal family `A` of `N` inputs (as in `actual_counted_subspaces_square`, including the
permittivity bounds `1 ≤ ε ≤ ε₊` for large shell index) such that for every family of linear plane fields
`E n r`, `H n r` with `ActualFieldEstimates`, the span of `A` is counted through the square `Dsq L` for the flux
`E × conj H`, eventually in `n` and then in `r`. -/
theorem actual_counted_subspaces_of_fields (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) :
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (_ : ρ < h) (_ : 0 ≤ R)
      (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
        ‖abovePoint (hpoint (-L) (ysq N L) l) (h * a)‖ + ρ ≤ R)
      (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ),
      q ^ 2 ≤ εp ∧ 1 + χ ≤ εp ∧
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      (∀ n : ℕ, ∀ᶠ r : ℕ in atTop, ∃ _ : max R 1 ≤ (SourcePairedInclusion.data q hq.le n r).R,
        ∀ x : FourierL2.Space,
          1 ≤ MaterialMaxwell.dielectric (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ hχ.le q n)) x ∧
          MaterialMaxwell.dielectric (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ hχ.le q n)) x ≤ εp) ∧
      ∀ E H : ℕ → ℕ → FieldMap, ActualFieldEstimates (-L) (ysq N L) ρ χ h R hρ hχ hi q E H →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dsq L) (fieldFlux (E n r) (H n r) a))
            (fun a => bypass volume (Dsq L) (fieldFlux (E n r) (H n r) a)) τ η δ := by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, hq2, hχε, horth, hrank, hperm, hcount⟩ :=
    actual_counted_subspaces_square εp hεp N η δ hη hηδ τ hτ L hL
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, hq2, hχε, horth, hrank, hperm, ?_⟩
  intro E H hest
  exact hcount (fun n r x => fieldFlux (E n r) (H n r) x) (fieldFlux_homogeneous E H)
    (L1Interface_of_field_estimates (-L) (ysq N L) ρ χ h R hρ hχ hi hR hρh q hq E H hest)

end Final

section Consistency
open OQ14.RestrictedTEActualCounting OQ14.RestrictedTEPartnerSmallness OQ14.RestrictedTEDipoleProfile
  OQ14.RestrictedTEConcreteDevice

/-- Consistency check: the parity total fields themselves, as the "actual" fields, satisfy
`ActualFieldEstimates` (so the three estimates are not contradictory, and are met by the model case). -/
theorem ActualFieldEstimates.parity {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hR : 0 ≤ R)
    (hρh : ρ < h) (q : ℝ) (hq : 1 < q) :
    ActualFieldEstimates r0 y ρ χ h R hρ hχ hi q
      (fun n _ => parityEMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n))
      (fun n _ => parityHMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n)) where
  meas := fun n r x i =>
    ⟨(parityE_continuous r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n) x
      i).aestronglyMeasurable,
     (parityH_continuous r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n) x
      i).aestronglyMeasurable⟩
  conv := by
    intro n x _ ρ0 _ ε hε
    refine Eventually.of_forall (fun r ξ _ i => ⟨?_, ?_⟩)
    · change ‖parityE r0 y ρ χ h R hρ hχ hi (scale q n) x ξ i - parityE r0 y ρ χ h R hρ hχ hi (scale q n) x ξ i‖ ≤ ε
      rw [sub_self, norm_zero]
      exact hε.le
    · change ‖parityH r0 y ρ χ h R hρ hχ hi (scale q n) x ξ i - parityH r0 y ρ χ h R hρ hχ hi (scale q n) x ξ i‖ ≤ ε
      rw [sub_self, norm_zero]
      exact hε.le
  tail := by
    intro N B horth n
    obtain ⟨C, T, hT⟩ := OQ14.RestrictedTEL1Assembly.parityFlux_tail r0 y ρ χ h R hρ hχ hi hR hρh (scale q n)
      (scale_pos hq n) (scale_le_one hq.le n) B horth
    exact ⟨C, T + 1, 0, fun r _ x hx hp ξ hξ => hT x hx hp ξ (by linarith)⟩

end Consistency

end OQ14.RestrictedTEActualFields
#print axioms OQ14.RestrictedTEActualFields.fieldFlux_eq
#print axioms OQ14.RestrictedTEActualFields.field_expand
#print axioms OQ14.RestrictedTEActualFields.unit_coeff_bound
#print axioms OQ14.RestrictedTEActualFields.basis_power
#print axioms OQ14.RestrictedTEActualFields.prod_diff
#print axioms OQ14.RestrictedTEActualFields.measurable_flux_of_fields
#print axioms OQ14.RestrictedTEActualFields.fieldFlux_homogeneous
#print axioms OQ14.RestrictedTEActualFields.compact_flux_of_uniform_fields
#print axioms OQ14.RestrictedTEActualFields.parityFlux_eq
#print axioms OQ14.RestrictedTEActualFields.parityFlux_eq_fieldFlux
#print axioms OQ14.RestrictedTEActualFields.parityE_continuous
#print axioms OQ14.RestrictedTEActualFields.parityH_continuous
#print axioms OQ14.RestrictedTEActualFields.bounded_on_disk
#print axioms OQ14.RestrictedTEActualFields.unit_tail_of_pair_tails
#print axioms OQ14.RestrictedTEActualFields.ActualFieldEstimates.of_pair_tails
#print axioms OQ14.RestrictedTEActualFields.L1Interface_of_field_estimates
#print axioms OQ14.RestrictedTEActualFields.actual_counted_subspaces_of_fields
#print axioms OQ14.RestrictedTEActualFields.ActualFieldEstimates.parity
