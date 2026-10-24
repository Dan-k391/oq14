import RestrictedTEActualPiecewise
import RestrictedTEFieldLinear
import RestrictedTEScale

/-! The counted-subspace theorems with a gain-index dependent global phase of the twist.

The limiting transmissions of the paired stacks rescale the input degreewise by `q^n` on the even active degrees
times one global unimodular constant `c q n` that depends on `n` and `q` but not on the degree; for the odd and the
degree-zero entries the gain is different, but those entries carry zero physical input.  Hence the rescaled vector
`scaledCoeff x (transInf q n)` is `q^n c q n` times `x` only at the level of the physical input
(`RestrictedTEInput.input`), not as a vector, and a fixed twist of the input space cannot satisfy the twist identity.
This module makes the two necessary changes.

* The incident TE fields, the weighted data, the device source and the parity total fields depend on the coefficient
  vector only through its physical input (`electric_eq_of_input_eq`, `magnetic_eq_of_input_eq` from
  `input_zero_fields` and linearity; `datum_eq_of_electric_eq`, `source_eq_of_input_eq`, `totalE_eq_of_input_eq`,
  `totalH_eq_of_input_eq`).  So the raw limit of the assembled fields is the parity total field at the phase-rotated
  input `c • A` as soon as the physical input of `scaledCoeff A (transInf)` is `q^n c` times that of `A`
  (`rescaled_input_witness`, `rawLimitE_eq_parity_phase`, `rawLimitH_eq_parity_phase`, `core_agree_conv_phase`).
* The phase is a global scalar, so no twist of the physical family is needed: the fields are rephased by the phase
  (`rephaseFields`: divided by `c n` from some gain index on, the parity model below), the rephased fields satisfy
  the untwisted `ActualFieldEstimates` (`ActualFieldEstimatesPhase.rephase`) and have the same plane flux as the
  actual fields (`fieldFlux_rephase`, a unimodular phase cancels in `E conj H`), so the span of the family `A` of the
  square theorem itself is counted for the flux of the actual fields
  (`actual_counted_subspaces_of_fields_phase`; `span_phase_invariant`).

`ActualFieldEstimatesPhase` collects the estimates with a phase function `c q n`; `ActualFieldEstimatesPhase.of_core`
derives it from `CoreAgreement`; `actual_counted_subspaces_of_core_phase` and `actual_counted_subspaces_of_pieces_phase`
restate the composite theorems of `RestrictedTEActualCore` and `RestrictedTEActualPiecewise` with the phase hypotheses
`hc` (modulus one for large `n`) and `hin` (the input-level twist identity), and `ActualFieldEstimatesPhase.parity_phase`
is the consistency check (the parity fields times the phase satisfy the estimates). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEActualPhase
open MeasureTheory Filter Topology Metric Set
open scoped ComplexConjugate

abbrev FieldMap := OQ14.RestrictedTEActualFields.FieldMap
abbrev Vec := OQ14.RestrictedTEActualCore.Vec
abbrev Sp := FourierL2.Space

/-! ### The incident TE fields and the parity total fields depend on the input vector only through its physical input -/

section InputDependence

/-- Two coefficient vectors with the same physical input have the same incident electric field. -/
theorem electric_eq_of_input_eq {A B : Vec} (h : RestrictedTEInput.input A = RestrictedTEInput.input B) :
    RestrictedTEPlaneLocal.electric A = RestrictedTEPlaneLocal.electric B := by
  have h0 : RestrictedTEInput.input (A - B) = 0 := by rw [map_sub, h, sub_self]
  have e : RestrictedTEPlaneLocal.electric (A - B) = 0 := (RestrictedTEInput.input_zero_fields (A - B) h0).1
  have hsum : RestrictedTEPlaneLocal.electric A =
      RestrictedTEPlaneLocal.electric (A - B) + RestrictedTEPlaneLocal.electric B := by
    rw [← RestrictedTEFieldLinear.electric_add, sub_add_cancel]
  rw [hsum, e, zero_add]

/-- Two coefficient vectors with the same physical input have the same incident magnetic field. -/
theorem magnetic_eq_of_input_eq {A B : Vec} (h : RestrictedTEInput.input A = RestrictedTEInput.input B) :
    RestrictedTEPlaneLocal.magnetic A = RestrictedTEPlaneLocal.magnetic B := by
  have h0 : RestrictedTEInput.input (A - B) = 0 := by rw [map_sub, h, sub_self]
  have e : RestrictedTEPlaneLocal.magnetic (A - B) = 0 := (RestrictedTEInput.input_zero_fields (A - B) h0).2
  have hsum : RestrictedTEPlaneLocal.magnetic A =
      RestrictedTEPlaneLocal.magnetic (A - B) + RestrictedTEPlaneLocal.magnetic B := by
    rw [← RestrictedTEFieldLinear.magnetic_add, sub_add_cancel]
  rw [hsum, e, zero_add]

/-- The weighted datum of a restricted-TE vector depends on the vector only through its incident electric field. -/
theorem datum_eq_of_electric_eq (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    {A B : Vec} (h : RestrictedTEPlaneLocal.electric A = RestrictedTEPlaneLocal.electric B) :
    RestrictedTEMaterial.datum c d A = RestrictedTEMaterial.datum c d B := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  filter_upwards [RestrictedTEMaterial.datum_actual c d A i, RestrictedTEMaterial.datum_actual c d B i] with x h1 h2
  rw [h1, h2, h]

section Totals
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The device source of the finite-ball inverse at scale `a` depends on the input only through its physical
input. -/
theorem source_eq_of_input_eq (p : ℝ → ι → Sp) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (a : ℝ) {A B : Vec}
    (h : RestrictedTEInput.input A = RestrictedTEInput.input B) :
    RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a = RestrictedTESourceMass.source p ρ χ R b hρ hχ hi B a := by
  have hE : RestrictedTEPlaneLocal.electric ((a : ℂ)⁻¹ • A) = RestrictedTEPlaneLocal.electric ((a : ℂ)⁻¹ • B) := by
    rw [RestrictedTEScale.electric_smul, RestrictedTEScale.electric_smul, electric_eq_of_input_eq h]
  unfold RestrictedTESourceMass.source RestrictedTEFiniteBalls.solution
  by_cases ha : 0 < a ∧ a ≤ 1
  · simp only [dif_pos ha]
    rw [datum_eq_of_electric_eq _ _ hE]
  · simp only [dif_neg ha]

/-- The parity total electric field at scale `a` depends on the input only through its physical input. -/
theorem totalE_eq_of_input_eq (p : ℝ → ι → Sp) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (a : ℝ) {A B : Vec}
    (h : RestrictedTEInput.input A = RestrictedTEInput.input B) (ξ : PlaneInverseCube.Plane) :
    RestrictedTETotalLinear.totalE p ρ χ R b hρ hχ hi a A ξ = RestrictedTETotalLinear.totalE p ρ χ R b hρ hχ hi a B ξ := by
  unfold RestrictedTETotalLinear.totalE
  rw [source_eq_of_input_eq p ρ χ R b hρ hχ hi a h, RestrictedTEScale.electric_smul, RestrictedTEScale.electric_smul,
    electric_eq_of_input_eq h]

/-- The parity total magnetic field at scale `a` depends on the input only through its physical input. -/
theorem totalH_eq_of_input_eq (p : ℝ → ι → Sp) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (a : ℝ) {A B : Vec}
    (h : RestrictedTEInput.input A = RestrictedTEInput.input B) (ξ : PlaneInverseCube.Plane) :
    RestrictedTETotalLinear.totalH p ρ χ R b hρ hχ hi a A ξ = RestrictedTETotalLinear.totalH p ρ χ R b hρ hχ hi a B ξ := by
  unfold RestrictedTETotalLinear.totalH
  rw [source_eq_of_input_eq p ρ χ R b hρ hχ hi a h, RestrictedTEScale.magnetic_smul, RestrictedTEScale.magnetic_smul,
    magnetic_eq_of_input_eq h]

end Totals

end InputDependence

/-! ### Convergence to the parity fields at the phase-rotated input -/

section PhaseConv
open OQ14.RestrictedTEActualCore OQ14.RestrictedTEPartnerSmallness OQ14.RestrictedTEPartnerBalls

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ → ι → Sp} {ρ χ R γ : ℝ}
  (hd : Device p ρ χ R γ) {q : ℝ} (hq : 1 < q)

/-- If the physical input of the rescaled vector `scaledCoeff A (transInf)` is `q^n c` times the input of `A`, the
rescaled vector is `q^n` times a vector `w` with the same physical input as `c • A`. -/
theorem rescaled_input_witness (n : ℕ) (A : Vec) (c : ℂ)
    (hin : RestrictedTEInput.input (BackgroundCoreTransmission.scaledCoeff A (transInf q hq.le n)) =
      (((q ^ n : ℝ) : ℂ) * c) • RestrictedTEInput.input A) :
    ∃ w : Vec, BackgroundCoreTransmission.scaledCoeff A (transInf q hq.le n) = ((q ^ n : ℝ) : ℂ) • w ∧
      RestrictedTEInput.input w = RestrictedTEInput.input (c • A) := by
  have hqn : ((q ^ n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_pos (zero_lt_one.trans hq) n).ne'
  refine ⟨((q ^ n : ℝ) : ℂ)⁻¹ • BackgroundCoreTransmission.scaledCoeff A (transInf q hq.le n), ?_, ?_⟩
  · rw [smul_inv_smul₀ hqn]
  · rw [map_smul, hin, map_smul, smul_smul, inv_mul_cancel_left₀ hqn]

/-- **Phase-rotated twist identification (electric).**  If the physical input of the vector rescaled degreewise by
the limiting transmissions is `q^n c` times its input, the raw limit of the assembled electric field is the parity
total electric field at scale `(q^n)⁻¹` and the input `c • A` (the parity field depends on the input vector only
through its physical input). -/
theorem rawLimitE_eq_parity_phase (n : ℕ) (A : Vec) (c : ℂ)
    (hin : RestrictedTEInput.input (BackgroundCoreTransmission.scaledCoeff A (transInf q hq.le n)) =
      (((q ^ n : ℝ) : ℂ) * c) • RestrictedTEInput.input A) (ξ : PlaneInverseCube.Plane) :
    rawLimitE q hq.le n (deviceCoeff p ρ χ hd.hχ q n) (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A ξ =
      parityEg p ρ χ R hd.hρ hd.hχ hd.hi (scale q n) (c • A) ξ := by
  obtain ⟨w, hw, hwi⟩ := rescaled_input_witness hq n A c hin
  rw [rawLimitE_eq_parity hd hq n A w hw ξ]
  unfold parityEg
  exact totalE_eq_of_input_eq _ _ _ _ _ _ _ _ _ hwi ξ

/-- **Phase-rotated twist identification (magnetic).** -/
theorem rawLimitH_eq_parity_phase (n : ℕ) (A : Vec) (c : ℂ)
    (hin : RestrictedTEInput.input (BackgroundCoreTransmission.scaledCoeff A (transInf q hq.le n)) =
      (((q ^ n : ℝ) : ℂ) * c) • RestrictedTEInput.input A) (ξ : PlaneInverseCube.Plane) :
    rawLimitH q hq.le n (deviceCoeff p ρ χ hd.hχ q n) (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A ξ =
      parityHg p ρ χ R hd.hρ hd.hχ hd.hi (scale q n) (c • A) ξ := by
  obtain ⟨w, hw, hwi⟩ := rescaled_input_witness hq n A c hin
  rw [rawLimitH_eq_parity hd hq n A w hw ξ]
  unfold parityHg
  exact totalH_eq_of_input_eq _ _ _ _ _ _ _ _ _ hwi ξ

variable {b : ℝ} (hRb : R ≤ b)
include hRb

/-- **Convergence of any fields agreeing with the core fields on the core, to the phase-rotated parity fields.**
If the fields `E n r`, `H n r` coincide on the open core with the assembled fields of the combined device (for large
`r`) and the physical input of the vector rescaled degreewise by the limiting transmissions is `q^n c n` times its
input (for large `n`), the fields converge uniformly on every disk to the parity total fields at the input `c n • x`. -/
theorem core_agree_conv_phase (hb0 : 0 < b) (c : ℕ → ℂ)
    (hin : ∀ᶠ n : ℕ in atTop, ∀ x : Vec,
      RestrictedTEInput.input (BackgroundCoreTransmission.scaledCoeff x (transInf q hq.le n)) =
        (((q ^ n : ℝ) : ℂ) * c n) • RestrictedTEInput.input x)
    (E H : ℕ → ℕ → FieldMap)
    (hE : ∀ n : ℕ, ∀ᶠ r : ℕ in atTop, ∀ (x : Vec) (ξ : PlaneInverseCube.Plane),
      ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R →
        E n r x ξ = coreE q hq.le n r (deviceCoeff p ρ χ hd.hχ q n)
          (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) x ξ)
    (hH : ∀ n : ℕ, ∀ᶠ r : ℕ in atTop, ∀ (x : Vec) (ξ : PlaneInverseCube.Plane),
      ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R →
        H n r x ξ = coreH q hq.le n r (deviceCoeff p ρ χ hd.hχ q n)
          (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) x ξ) :
    ∀ᶠ n : ℕ in atTop, ∀ (x : Vec) (ρ0 : ℝ), 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop,
      ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i,
        ‖E n r x ξ i - parityEg p ρ χ R hd.hρ hd.hχ hd.hi (scale q n) (c n • x) ξ i‖ ≤ ε ∧
        ‖H n r x ξ i - parityHg p ρ χ R hd.hρ hd.hχ hd.hi (scale q n) (c n • x) ξ i‖ ≤ ε := by
  filter_upwards [core_conv_raw_eventually hd hq hRb hb0, hin] with n h hin'
  intro x ρ0 hρ0 ε hε
  filter_upwards [h x ρ0 hρ0 ε hε, hE n, hH n,
    RadialPhaseLimit.radius_tendsto.eventually (eventually_gt_atTop ρ0)] with r hr hEr hHr hρ ξ hξ i
  have hξR : ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R := lt_of_le_of_lt hξ hρ
  obtain ⟨h1, h2⟩ := hr ξ hξ i
  rw [rawLimitE_eq_parity_phase hd hq n x (c n) (hin' x) ξ] at h1
  rw [rawLimitH_eq_parity_phase hd hq n x (c n) (hin' x) ξ] at h2
  rw [hEr x ξ hξR, hHr x ξ hξR]
  exact ⟨h1, h2⟩

end PhaseConv

/-! ### The phase-rotated field estimates and the rephased fields -/

section Estimates
open OQ14.RestrictedTEPartnerSmallness OQ14.RestrictedTEPartnerBalls OQ14.RestrictedTEActualCore
  OQ14.RestrictedTEActualFields

/-- The span of a family is invariant under a global scalar (a global phase). -/
theorem span_phase_invariant {κ : Type*} (B : κ → Vec) (z : ℂ) (x : Vec)
    (hx : x ∈ Submodule.span ℂ (Set.range B)) : z • x ∈ Submodule.span ℂ (Set.range B) :=
  Submodule.smul_mem _ z hx

/-- The three estimates on the actual plane fields, up to a global phase `c n` of the input that depends on the gain
index: the fields converge, for large gain index, to the parity total fields at the phase-rotated input `c n • x`
(`‖c n‖ = 1` for large `n`), with measurability and the inverse-cube tail of the flux. -/
structure ActualFieldEstimatesPhase {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ)
    (c : ℕ → ℂ) (E H : ℕ → ℕ → FieldMap) : Prop where
  meas : ∀ (n r : ℕ) (x : Vec) (i : Fin 3),
    AEStronglyMeasurable (fun ξ => E n r x ξ i) volume ∧ AEStronglyMeasurable (fun ξ => H n r x ξ i) volume
  unit : ∀ᶠ n : ℕ in atTop, ‖c n‖ = 1
  conv : ∀ᶠ n : ℕ in atTop, ∀ x : Vec, RestrictedTEIncoming.physicalPower x = 1 →
    ∀ ρ0 : ℝ, 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 →
      ∀ i, ‖E n r x ξ i - parityE r0 y ρ χ h R hρ hχ hi (scale q n) (c n • x) ξ i‖ ≤ ε ∧
        ‖H n r x ξ i - parityH r0 y ρ χ h R hρ hχ hi (scale q n) (c n • x) ξ i‖ ≤ ε
  tail : ∀ᶠ n : ℕ in atTop, ∀ (N : Nat) (B : Fin N → Vec),
    Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (C ρ1 : ℝ) (r1 : ℕ),
      ∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
        ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ →
          ‖fieldFlux (E n r) (H n r) x ξ‖ ≤ C / ‖ξ‖ ^ 3

/-- **The phase-rotated estimates from the core.**  For the concrete doubled device, fields agreeing with the
assembled core fields on the open core (for large `r`), with measurable coordinates and the inverse-cube tail
majorant of the flux (`CoreAgreement`), satisfy `ActualFieldEstimatesPhase` as soon as the physical input of the
vector rescaled degreewise by the limiting transmissions is `q^n c n` times its input for large `n` and `‖c n‖ = 1`
for large `n`. -/
theorem ActualFieldEstimatesPhase.of_core {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hρh : ρ < h) {q : ℝ} (hq : 1 < q)
    {b : ℝ} (hb0 : 0 < b) (hRb : R ≤ b) (c : ℕ → ℂ) (hc : ∀ᶠ n : ℕ in atTop, ‖c n‖ = 1)
    (hin : ∀ᶠ n : ℕ in atTop, ∀ x : Vec,
      RestrictedTEInput.input (BackgroundCoreTransmission.scaledCoeff x (transInf q hq.le n)) =
        (((q ^ n : ℝ) : ℂ) * c n) • RestrictedTEInput.input x)
    (E H : ℕ → ℕ → FieldMap) (hca : CoreAgreement r0 y ρ χ h R hρ hχ hi q hq E H) :
    ActualFieldEstimatesPhase r0 y ρ χ h R hρ hχ hi q c E H where
  meas := hca.meas
  unit := hc
  conv := by
    have hd := concrete_device r0 y ρ χ h R hρ hχ.le hρh hi
    filter_upwards [core_agree_conv_phase hd hq hRb hb0 c hin E H hca.agreeE hca.agreeH] with n hn x _ ρ0 hρ0 ε hε
    filter_upwards [hn x ρ0 hρ0 ε hε] with r hr ξ hξ i
    exact hr ξ hξ i
  tail := hca.tail

/-- Rephased fields: the fields divided by the phase for gain indices `≥ n0`, a model below `n0`. -/
def rephaseFields (n0 : ℕ) (c : ℕ → ℂ) (E : ℕ → ℕ → FieldMap) (model : ℕ → FieldMap) : ℕ → ℕ → FieldMap :=
  fun n r => if n0 ≤ n then (c n)⁻¹ • E n r else model n

theorem rephaseFields_ge (n0 : ℕ) (c : ℕ → ℂ) (E : ℕ → ℕ → FieldMap) (model : ℕ → FieldMap) (n r : ℕ)
    (hn : n0 ≤ n) : rephaseFields n0 c E model n r = (c n)⁻¹ • E n r := by
  unfold rephaseFields
  rw [if_pos hn]

theorem rephaseFields_lt (n0 : ℕ) (c : ℕ → ℂ) (E : ℕ → ℕ → FieldMap) (model : ℕ → FieldMap) (n r : ℕ)
    (hn : ¬ n0 ≤ n) : rephaseFields n0 c E model n r = model n := by
  unfold rephaseFields
  rw [if_neg hn]

/-- Dividing both fields by a phase leaves the plane flux unchanged. -/
theorem fieldFlux_rephase (z : ℂ) (hz : ‖z‖ = 1) (E H : FieldMap) (x : Vec) :
    fieldFlux (z⁻¹ • E) (z⁻¹ • H) x = fieldFlux E H x := by
  funext ξ
  rw [fieldFlux_eq, fieldFlux_eq]
  have h1 : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hzz : z⁻¹ * conj (z⁻¹) = 1 := by
    rw [map_inv₀, ← mul_inv, h1, inv_one]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  linear_combination (E x ξ 0 * conj (H x ξ 1) - E x ξ 1 * conj (H x ξ 0)) * hzz

/-- The parity total electric field is complex linear in the input. -/
theorem parityE_smul_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ)
    (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hρh : ρ < h) (a : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) (z : ℂ) (x : Vec) (ξ : PlaneInverseCube.Plane) (i : Fin 3) :
    parityE r0 y ρ χ h R hρ hχ hi a (z • x) ξ i = z * parityE r0 y ρ χ h R hρ hχ hi a x ξ i :=
  congrFun (congrFun (map_smul (parityEMap r0 y ρ χ h R hρ hχ hi hρh a ha ha1) z x) ξ) i

theorem parityH_smul_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ)
    (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hρh : ρ < h) (a : ℝ) (ha : 0 < a)
    (ha1 : a ≤ 1) (z : ℂ) (x : Vec) (ξ : PlaneInverseCube.Plane) (i : Fin 3) :
    parityH r0 y ρ χ h R hρ hχ hi a (z • x) ξ i = z * parityH r0 y ρ χ h R hρ hχ hi a x ξ i :=
  congrFun (congrFun (map_smul (parityHMap r0 y ρ χ h R hρ hχ hi hρh a ha ha1) z x) ξ) i

/-- A coordinate estimate against the phase-rotated model gives the rephased estimate. -/
theorem rephase_norm (z e P : ℂ) (ε : ℝ) (hz : ‖z‖ = 1) (h : ‖e - z * P‖ ≤ ε) : ‖z⁻¹ * e - P‖ ≤ ε := by
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz
    exact zero_ne_one hz
  have e1 : z⁻¹ * e - P = z⁻¹ * (e - z * P) := by
    rw [mul_sub, inv_mul_cancel_left₀ hz0]
  rw [e1, norm_mul, norm_inv, hz, inv_one, one_mul]
  exact h

/-- **From the phase-rotated estimates to the untwisted ones.**  The phase-rotated estimates give the untwisted
estimates `ActualFieldEstimates` for the rephased fields (the fields divided by the phase from some gain index on, the
parity model below), and the rephased fields have the same plane flux as the fields for the large gain indices. -/
theorem ActualFieldEstimatesPhase.rephase {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hR : 0 ≤ R) (hρh : ρ < h)
    (q : ℝ) (hq : 1 < q) (c : ℕ → ℂ) (E H : ℕ → ℕ → FieldMap)
    (hest : ActualFieldEstimatesPhase r0 y ρ χ h R hρ hχ hi q c E H) :
    ∃ n0 : ℕ, (∀ n, n0 ≤ n → ‖c n‖ = 1) ∧
      ActualFieldEstimates r0 y ρ χ h R hρ hχ hi q
        (rephaseFields n0 c E (fun n => parityEMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n)
          (scale_le_one hq.le n)))
        (rephaseFields n0 c H (fun n => parityHMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n)
          (scale_le_one hq.le n))) := by
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp (hest.unit.and (hest.conv.and hest.tail))
  have hpar := ActualFieldEstimates.parity r0 y ρ χ h R hρ hχ hi hR hρh q hq
  refine ⟨n0, fun n hn => (hn0 n hn).1, ?_, ?_, ?_⟩
  · intro n r x i
    by_cases hn : n0 ≤ n
    · rw [rephaseFields_ge n0 c E _ n r hn, rephaseFields_ge n0 c H _ n r hn]
      have m1 : AEStronglyMeasurable (fun ξ => (c n)⁻¹ * E n r x ξ i) volume :=
        (hest.meas n r x i).1.const_mul ((c n)⁻¹)
      have m2 : AEStronglyMeasurable (fun ξ => (c n)⁻¹ * H n r x ξ i) volume :=
        (hest.meas n r x i).2.const_mul ((c n)⁻¹)
      exact ⟨m1, m2⟩
    · rw [rephaseFields_lt n0 c E _ n r hn, rephaseFields_lt n0 c H _ n r hn]
      exact hpar.meas n r x i
  · intro n x hx ρ0 hρ0 ε hε
    by_cases hn : n0 ≤ n
    · obtain ⟨hu, hcv, _⟩ := hn0 n hn
      filter_upwards [hcv x hx ρ0 hρ0 ε hε] with r hr ξ hξ i
      rw [rephaseFields_ge n0 c E _ n r hn, rephaseFields_ge n0 c H _ n r hn]
      obtain ⟨h1, h2⟩ := hr ξ hξ i
      rw [parityE_smul_apply r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n)] at h1
      rw [parityH_smul_apply r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n)] at h2
      exact ⟨rephase_norm (c n) _ _ ε hu h1, rephase_norm (c n) _ _ ε hu h2⟩
    · filter_upwards [hpar.conv n x hx ρ0 hρ0 ε hε] with r hr ξ hξ i
      rw [rephaseFields_lt n0 c E _ n r hn, rephaseFields_lt n0 c H _ n r hn]
      exact hr ξ hξ i
  · intro N B horth n
    by_cases hn : n0 ≤ n
    · obtain ⟨C, ρ1, r1, h1⟩ := (hn0 n hn).2.2 N B horth
      refine ⟨C, ρ1, r1, fun r hr x hx hp ξ hξ => ?_⟩
      rw [rephaseFields_ge n0 c E _ n r hn, rephaseFields_ge n0 c H _ n r hn,
        fieldFlux_rephase (c n) (hn0 n hn).1]
      exact h1 r hr x hx hp ξ hξ
    · obtain ⟨C, ρ1, r1, h1⟩ := hpar.tail N B horth n
      refine ⟨C, ρ1, r1, fun r hr x hx hp ξ hξ => ?_⟩
      rw [rephaseFields_lt n0 c E _ n r hn, rephaseFields_lt n0 c H _ n r hn]
      exact h1 r hr x hx hp ξ hξ

end Estimates

/-! ### The consistency check -/

section Consistency
open OQ14.RestrictedTEPartnerSmallness OQ14.RestrictedTEActualFields

/-- Consistency check: the parity total fields multiplied by the global phase `c n` satisfy the phase-rotated
estimates (so the estimates are not contradictory and are met by the model case). -/
theorem ActualFieldEstimatesPhase.parity_phase {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hR : 0 ≤ R) (hρh : ρ < h)
    (q : ℝ) (hq : 1 < q) (c : ℕ → ℂ) (hc : ∀ᶠ n : ℕ in atTop, ‖c n‖ = 1) :
    ActualFieldEstimatesPhase r0 y ρ χ h R hρ hχ hi q c
      (fun n _ => c n • parityEMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n))
      (fun n _ => c n • parityHMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n)) where
  meas := fun n r x i =>
    ⟨(Continuous.const_smul (parityE_continuous r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n)
      (scale_le_one hq.le n) x i) (c n)).aestronglyMeasurable,
     (Continuous.const_smul (parityH_continuous r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n)
      (scale_le_one hq.le n) x i) (c n)).aestronglyMeasurable⟩
  unit := hc
  conv := by
    refine Eventually.of_forall (fun n x _ ρ0 _ ε hε => Eventually.of_forall (fun r ξ _ i => ⟨?_, ?_⟩))
    · change ‖c n * parityE r0 y ρ χ h R hρ hχ hi (scale q n) x ξ i -
        parityE r0 y ρ χ h R hρ hχ hi (scale q n) (c n • x) ξ i‖ ≤ ε
      rw [parityE_smul_apply r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n),
        sub_self, norm_zero]
      exact hε.le
    · change ‖c n * parityH r0 y ρ χ h R hρ hχ hi (scale q n) x ξ i -
        parityH r0 y ρ χ h R hρ hχ hi (scale q n) (c n • x) ξ i‖ ≤ ε
      rw [parityH_smul_apply r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n),
        sub_self, norm_zero]
      exact hε.le
  tail := by
    filter_upwards [hc] with n hn N B horth
    obtain ⟨C, ρ1, r1, h1⟩ := (ActualFieldEstimates.parity r0 y ρ χ h R hρ hχ hi hR hρh q hq).tail N B horth n
    refine ⟨C, ρ1, r1, fun r hr x hx hp ξ hξ => ?_⟩
    have hf := fieldFlux_rephase (c n)⁻¹ (by rw [norm_inv, hn, inv_one])
      (parityEMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n))
      (parityHMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n)) x
    rw [inv_inv] at hf
    rw [hf]
    exact h1 r hr x hx hp ξ hξ

end Consistency

/-! ### The counted-subspace theorems with a global phase -/

section Final
open OQ14.RestrictedTEPassageTransfer OQ14.RestrictedTEActualCounting OQ14.RestrictedTEActualWindow
  OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEConcreteDoubled OQ14.RestrictedTEPartnerBalls OQ14.RestrictedTEPlaneJets
  OQ14.RestrictedTEPartnerCount OQ14.RestrictedTEPartnerSmallness OQ14.ChannelMaterialThroughput
  OQ14.RestrictedTEActualSquare OQ14.RestrictedTEActualCore OQ14.RestrictedTEActualFields

/-- **Counted subspaces for plane fields converging to the phase-rotated parity fields.**  Let `c q n` be a global
phase (a complex number of modulus one for large `n`) for every `q > 1`.  For every `ε₊ > 1`, `N`, thresholds
`0 < η < δ`, `τ ≤ 1` and half-side `L > 0` there are the device parameters of `actual_counted_subspaces_square` and
the physical family `A` of the square theorem itself (no twist of the family: the span of `A` is invariant under the
phases), such that for every family of linear plane fields `E n r`, `H n r` with `ActualFieldEstimatesPhase`
(measurability, convergence to the parity total fields at the phase-rotated input `c q n • x`, and the inverse-cube
tail majorant of the flux) the span of `A` is counted through the square `Dsq L` for the flux of the fields,
eventually in `n` and then in `r`. -/
theorem actual_counted_subspaces_of_fields_phase (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) (c : ℝ → ℕ → ℂ) :
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
      ∀ E H : ℕ → ℕ → FieldMap,
        ActualFieldEstimatesPhase (-L) (ysq N L) ρ χ h R hρ hχ hi q (c q) E H →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dsq L) (fieldFlux (E n r) (H n r) a))
            (fun a => bypass volume (Dsq L) (fieldFlux (E n r) (H n r) a)) τ η δ := by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, hq2, hχε, horth, hrank, hperm, hcount⟩ :=
    actual_counted_subspaces_of_fields εp hεp N η δ hη hηδ τ hτ L hL
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, hq2, hχε, horth, hrank, hperm, ?_⟩
  intro E H hest
  obtain ⟨n0, hu, hAFE⟩ := hest.rephase (-L) (ysq N L) ρ χ h R hρ hχ hi hR hρh q hq (c q) E H
  have h1 := hcount _ _ hAFE
  filter_upwards [h1, eventually_ge_atTop n0] with n hn1 hn
  filter_upwards [hn1] with r hr
  rw [rephaseFields_ge n0 (c q) E _ n r hn, rephaseFields_ge n0 (c q) H _ n r hn] at hr
  simp only [fieldFlux_rephase (c q n) (hu n hn)] at hr
  exact hr

/-- **Counted subspaces from the core identification, with a global phase.**  Suppose that for every `q > 1` and all
large `n` the phase `c q n` has modulus one and the physical input of the vector rescaled degreewise by the limiting
transmissions over two is `q^n c q n` times its physical input.  Then, with the device parameters and the physical
family `A` of the square theorem, for every family of linear plane fields `E n r`, `H n r` that agrees with the
assembled fields of the combined device on the open core and is measurable with an inverse-cube tail majorant of its
flux (`CoreAgreement`), the span of `A` is counted through the square `Dsq L`, eventually in `n` and then in `r`. -/
theorem actual_counted_subspaces_of_core_phase (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) (c : ℝ → ℕ → ℂ)
    (hc : ∀ (q : ℝ) (_ : 1 < q), ∀ᶠ n : ℕ in atTop, ‖c q n‖ = 1)
    (hin : ∀ (q : ℝ) (hq : 1 < q), ∀ᶠ n : ℕ in atTop, ∀ x : Vec,
      RestrictedTEInput.input (BackgroundCoreTransmission.scaledCoeff x (transInf q hq.le n)) =
        (((q ^ n : ℝ) : ℂ) * c q n) • RestrictedTEInput.input x) :
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
      ∀ E H : ℕ → ℕ → FieldMap,
        CoreAgreement (-L) (ysq N L) ρ χ h R hρ hχ hi q hq E H →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dsq L) (fieldFlux (E n r) (H n r) a))
            (fun a => bypass volume (Dsq L) (fieldFlux (E n r) (H n r) a)) τ η δ := by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6⟩ :=
    actual_counted_subspaces_of_fields_phase εp hεp N η δ hη hηδ τ hτ L hL c
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, ?_⟩
  intro E H hca
  have hb0 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  exact h6 E H (ActualFieldEstimatesPhase.of_core (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq hb0
    (le_max_left R 1) (c q) (hc q hq) (hin q hq) E H hca)

end Final

/-! ### The counted-subspace theorem from the pieces, with a global phase -/

section Pieces
open OQ14.RestrictedTEPassageTransfer OQ14.RestrictedTEActualCounting OQ14.RestrictedTEActualWindow
  OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEConcreteDoubled OQ14.RestrictedTEPartnerBalls OQ14.RestrictedTEPlaneJets
  OQ14.RestrictedTEPartnerCount OQ14.RestrictedTEPartnerSmallness OQ14.ChannelMaterialThroughput
  OQ14.RestrictedTEActualSquare OQ14.RestrictedTEActualPiecewise

/-- **Counted subspaces from the pieces, with a global phase.**  The phase version of
`actual_counted_subspaces_of_pieces`: the twist identity is replaced by the input-level identity with a global phase
`c q n` of modulus one, and the physical family is the family `A` of the square theorem. -/
theorem actual_counted_subspaces_of_pieces_phase (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) (c : ℝ → ℕ → ℂ)
    (hc : ∀ (q : ℝ) (_ : 1 < q), ∀ᶠ n : ℕ in atTop, ‖c q n‖ = 1)
    (hin : ∀ (q : ℝ) (hq : 1 < q), ∀ᶠ n : ℕ in atTop, ∀ x : Vec,
      RestrictedTEInput.input (BackgroundCoreTransmission.scaledCoeff x
        (OQ14.RestrictedTEActualCore.transInf q hq.le n)) =
        (((q ^ n : ℝ) : ℂ) * c q n) • RestrictedTEInput.input x) :
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (hρh : ρ < h) (_ : 0 ≤ R)
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
      ∀ (outE outH : ℕ → ℕ → FieldMap) (radE radH : ℕ → ℕ → Vec → PlaneInverseCube.Plane → Maxwell.Vector),
        (∀ (n r : ℕ) (x : Vec) (i : Fin 3), AEStronglyMeasurable (fun ξ => outE n r x ξ i) volume ∧
          AEStronglyMeasurable (fun ξ => outH n r x ξ i) volume) →
        OutsideDecomposition q hq.le outE outH radE radH →
        CoreMajorant (-L) (ysq N L) ρ χ h R hρ hχ hi q hq →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
              (deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outE n r)
              (deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outH n r) a))
            (fun a => bypass volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
              (deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outE n r)
              (deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outH n r) a)) τ η δ := by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6⟩ :=
    actual_counted_subspaces_of_core_phase εp hεp N η δ hη hηδ τ hτ L hL c hc hin
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, ?_⟩
  intro outE outH radE radH hmeas hOD hCM
  have hd := OQ14.RestrictedTEActualCore.concrete_device (-L) (ysq N L) ρ χ h R hρ hχ.le hρh hi
  refine h6 _ _ (coreAgreement_of_out (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outE outH hmeas ?_)
  filter_upwards [hCM.maj, hOD.rad] with n hn1 hn2
  intro N' B horth
  obtain ⟨C1, ρ1, r1, hc'⟩ := hn1 N' B horth
  obtain ⟨K1, K2, L1, L2, r2, hrad⟩ := hn2 N' B horth
  obtain ⟨C2, r2', hT2⟩ := outside_majorant_of_pieces q hq.le outE outH radE radH hOD n N' B horth
    ⟨K1, K2, L1, L2, r2, hrad⟩
  obtain ⟨rb, hrb⟩ := Filter.eventually_atTop.mp
    (SourcePairedReduction.eventually_inner_radius q hq.le n (max R 1))
  have hT1 : ∃ (C1' ρ1' : ℝ) (r1' : ℕ), ∀ r ≥ r1',
      ∀ x ∈ {x | x ∈ Submodule.span ℂ (Set.range B) ∧ RestrictedTEIncoming.physicalPower x = 1},
      ∀ ξ : PlaneInverseCube.Plane, ρ1' ≤ ‖ξ‖ → ‖ξ‖ < RadialPhaseLimit.radius r →
        ‖OQ14.RestrictedTEActualFields.fieldFlux
          (OQ14.RestrictedTEActualCore.deviceFieldE hd hq (le_max_left R 1) n r)
          (OQ14.RestrictedTEActualCore.deviceFieldH hd hq (le_max_left R 1) n r) x ξ‖ ≤ C1' / ‖ξ‖ ^ 3 := by
    refine ⟨C1, ρ1, max r1 rb, fun r hr x hx ξ hξ hlt => ?_⟩
    have hbr := hrb r ((le_max_right _ _).trans hr)
    unfold OQ14.RestrictedTEActualFields.fieldFlux
    rw [OQ14.RestrictedTEActualCore.deviceFieldE_apply hd hq (le_max_left R 1) n r hbr x ξ hlt,
      OQ14.RestrictedTEActualCore.deviceFieldH_apply hd hq (le_max_left R 1) n r hbr x ξ hlt]
    exact hc' r ((le_max_left _ _).trans hr) x hx.1 hx.2 ξ hξ hlt
  have hT2' : ∃ (C2' : ℝ) (r2'' : ℕ), ∀ r ≥ r2'',
      ∀ x ∈ {x | x ∈ Submodule.span ℂ (Set.range B) ∧ RestrictedTEIncoming.physicalPower x = 1},
      ∀ ξ : PlaneInverseCube.Plane, RadialPhaseLimit.radius r ≤ ‖ξ‖ →
        ‖OQ14.RestrictedTEActualFields.fieldFlux (outE n r) (outH n r) x ξ‖ ≤ C2' / ‖ξ‖ ^ 3 :=
    ⟨C2, r2', fun r hr x hx ξ hξ => hT2 r hr x hx.1 hx.2 ξ hξ⟩
  obtain ⟨C, ρ1', r1', ht⟩ := tail_of_two_majorants (fun r => RadialPhaseLimit.radius r)
    (fun n r => OQ14.RestrictedTEActualCore.deviceFieldE hd hq (le_max_left R 1) n r)
    (fun n r => OQ14.RestrictedTEActualCore.deviceFieldH hd hq (le_max_left R 1) n r) outE outH n
    {x | x ∈ Submodule.span ℂ (Set.range B) ∧ RestrictedTEIncoming.physicalPower x = 1} hT1 hT2'
  exact ⟨C, ρ1', r1', fun r hr x hx hp ξ hξ => ht r hr x ⟨hx, hp⟩ ξ hξ⟩

end Pieces

end OQ14.RestrictedTEActualPhase

#print axioms OQ14.RestrictedTEActualPhase.electric_eq_of_input_eq
#print axioms OQ14.RestrictedTEActualPhase.magnetic_eq_of_input_eq
#print axioms OQ14.RestrictedTEActualPhase.datum_eq_of_electric_eq
#print axioms OQ14.RestrictedTEActualPhase.source_eq_of_input_eq
#print axioms OQ14.RestrictedTEActualPhase.totalE_eq_of_input_eq
#print axioms OQ14.RestrictedTEActualPhase.totalH_eq_of_input_eq
#print axioms OQ14.RestrictedTEActualPhase.rescaled_input_witness
#print axioms OQ14.RestrictedTEActualPhase.rawLimitE_eq_parity_phase
#print axioms OQ14.RestrictedTEActualPhase.rawLimitH_eq_parity_phase
#print axioms OQ14.RestrictedTEActualPhase.core_agree_conv_phase
#print axioms OQ14.RestrictedTEActualPhase.span_phase_invariant
#print axioms OQ14.RestrictedTEActualPhase.ActualFieldEstimatesPhase.of_core
#print axioms OQ14.RestrictedTEActualPhase.rephaseFields_ge
#print axioms OQ14.RestrictedTEActualPhase.rephaseFields_lt
#print axioms OQ14.RestrictedTEActualPhase.fieldFlux_rephase
#print axioms OQ14.RestrictedTEActualPhase.parityE_smul_apply
#print axioms OQ14.RestrictedTEActualPhase.parityH_smul_apply
#print axioms OQ14.RestrictedTEActualPhase.rephase_norm
#print axioms OQ14.RestrictedTEActualPhase.ActualFieldEstimatesPhase.rephase
#print axioms OQ14.RestrictedTEActualPhase.ActualFieldEstimatesPhase.parity_phase
#print axioms OQ14.RestrictedTEActualPhase.actual_counted_subspaces_of_fields_phase
#print axioms OQ14.RestrictedTEActualPhase.actual_counted_subspaces_of_core_phase
#print axioms OQ14.RestrictedTEActualPhase.actual_counted_subspaces_of_pieces_phase
