import RestrictedTEConcreteDoubled
import RestrictedTEHomogeneousCount
import RestrictedTEPartnerSmallness
import ChannelScatteringMap
import OQ14

/-! Diagonal assembly of the counted channels of the actual device.

Interface.  `Fpar a x` is the plane flux density of the parity device at scale `a` for the input `x`, and
`Fact n r x` is the plane flux density of the actual paired-shell device with gain index `n` (scale
`sc n = (q^n)⁻¹`) and shell index `r`.  The two hypotheses of the diagonal argument are
* (H1) the audited counting inequality of the parity device with intermediate thresholds
  `η' ∈ (ηt, p0)`, `δ' ∈ (p0, δt)`, for all small scales `a`;
* (H2) the whole-plane L1 interface: for every fixed `n` and every `ε > 0`, for all large shell indices `r`, the
  actual flux is integrable and within `ε` of the parity flux at the matching scale, on the unit-power sphere of
  the span.
The conclusion is the counting inequality for the actual device, first for large `n` and then for large `r`
(`diagonal_transfer`), then for all powers by quadratic homogeneity, and finally the manuscript's counted-subspace
statement (`IsCounted`) with unit throughput. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEActualCounting
open MeasureTheory Filter Topology OQ14.RestrictedTEPassageTransfer
abbrev Idx := SymmetricHarmonicJets.Index

section Abstract
variable {P V : Type*} [MeasurableSpace P]

/-- Abstract diagonal transfer: parity-device counting for small scales plus whole-plane L1 convergence of the
actual flux to the parity flux at the matching scale give the counting inequality for the actual device, for all
large `n` and then all large `r`. -/
theorem diagonal_transfer (μ : Measure P) (D : Set P) (S : Set V) (Fpar : ℝ → V → P → ℂ)
    (Fact : ℕ → ℕ → V → P → ℂ) (sc : ℕ → ℝ) (hsc : Tendsto sc atTop (𝓝[>] 0)) (ηt δt η' δ' : ℝ)
    (hη : ηt < η') (hδ : δ' < δt) (hFpar : ∀ n, ∀ x ∈ S, Integrable (Fpar (sc n) x) μ)
    (H1 : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ x ∈ S, η' ≤ passage μ D (Fpar a x) ∧ bypass μ D (Fpar a x) ≤ δ')
    (H2 : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ x ∈ S,
      Integrable (Fact n r x) μ ∧ ∫ q, ‖Fact n r x q - Fpar (sc n) x q‖ ∂μ ≤ ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop, ∀ x ∈ S,
      ηt ≤ passage μ D (Fact n r x) ∧ bypass μ D (Fact n r x) ≤ δt := by
  filter_upwards [hsc.eventually H1] with n hn
  have hε : 0 < min (η' - ηt) (δt - δ') := lt_min (by linarith) (by linarith)
  filter_upwards [H2 n _ hε] with r hr x hx
  obtain ⟨hf, hd⟩ := hr x hx
  have h1 := abs_passage_sub_le D (Fact n r x) (Fpar (sc n) x) hf (hFpar n x hx)
  have h2 := abs_bypass_sub_le D (Fact n r x) (Fpar (sc n) x) hf (hFpar n x hx)
  have hm1 : min (η' - ηt) (δt - δ') ≤ η' - ηt := min_le_left _ _
  have hm2 : min (η' - ηt) (δt - δ') ≤ δt - δ' := min_le_right _ _
  obtain ⟨hp, hb⟩ := hn x hx
  constructor
  · have := (abs_le.mp (h1.trans hd)).1
    linarith
  · have := (abs_le.mp (h2.trans hd)).2
    linarith

/-- The same, when the interface also records the integrability of the difference (then the integrability of the
parity flux is a consequence). -/
theorem diagonal_transfer_of_diff (μ : Measure P) (D : Set P) (S : Set V) (Fpar : ℝ → V → P → ℂ)
    (Fact : ℕ → ℕ → V → P → ℂ) (sc : ℕ → ℝ) (hsc : Tendsto sc atTop (𝓝[>] 0)) (ηt δt η' δ' : ℝ)
    (hη : ηt < η') (hδ : δ' < δt)
    (H1 : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ x ∈ S, η' ≤ passage μ D (Fpar a x) ∧ bypass μ D (Fpar a x) ≤ δ')
    (H2 : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ x ∈ S,
      Integrable (Fact n r x) μ ∧ Integrable (fun q => Fact n r x q - Fpar (sc n) x q) μ ∧
        ∫ q, ‖Fact n r x q - Fpar (sc n) x q‖ ∂μ ≤ ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop, ∀ x ∈ S,
      ηt ≤ passage μ D (Fact n r x) ∧ bypass μ D (Fact n r x) ≤ δt := by
  refine diagonal_transfer μ D S Fpar Fact sc hsc ηt δt η' δ' hη hδ ?_ H1
    (fun n ε hε => (H2 n ε hε).mono (fun r hr x hx => ⟨(hr x hx).1, (hr x hx).2.2⟩))
  intro n x hx
  obtain ⟨r, hr⟩ := (H2 n 1 one_pos).exists
  obtain ⟨hf, hd, _⟩ := hr x hx
  have : Fpar (sc n) x = fun q => Fact n r x q - (Fact n r x q - Fpar (sc n) x q) :=
    funext fun q => (sub_sub_cancel _ _).symm
  rw [this]
  exact hf.sub hd

/-- Quadratic homogeneity extends the unit-power counting inequalities to every positive power. -/
theorem homogeneous_extension [AddCommGroup V] [Module ℂ V] (μ : Measure P) (D : Set P) (W : Submodule ℂ V)
    (pow : V → ℝ) (hpow : ∀ (z : ℂ) x, pow (z • x) = ‖z‖ ^ 2 * pow x) (F : V → P → ℂ)
    (hhom : ∀ (z : ℂ) x, F (z • x) = fun q => ((‖z‖ ^ 2 : ℝ) : ℂ) * F x q) (ηt δt : ℝ)
    (h : ∀ x ∈ W, pow x = 1 → ηt ≤ passage μ D (F x) ∧ bypass μ D (F x) ≤ δt) :
    ∀ x ∈ W, 0 < pow x →
      ηt * pow x ≤ passage μ D (F x) ∧ bypass μ D (F x) ≤ δt * pow x := by
  intro x hx hP
  set Px := pow x with hPx
  let z : ℂ := ((Real.sqrt Px)⁻¹ : ℝ)
  have hz : ‖z‖ ^ 2 = Px⁻¹ := by
    simp only [z, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg Px))]
    rw [inv_pow, Real.sq_sqrt hP.le]
  have hmem : z • x ∈ W := W.smul_mem z hx
  have hpow1 : pow (z • x) = 1 := by
    rw [hpow, hz, ← hPx, inv_mul_cancel₀ hP.ne']
  obtain ⟨hpass, hbyp⟩ := h (z • x) hmem hpow1
  have hF : F (z • x) = fun q => ((Px⁻¹ : ℝ) : ℂ) * F x q := by
    rw [hhom, hz]
  rw [hF, RestrictedTEHomogeneousCount.passage_const_mul] at hpass
  rw [hF, RestrictedTEHomogeneousCount.bypass_const_mul _ _ _ (inv_nonneg.mpr hP.le)] at hbyp
  constructor
  · have := mul_le_mul_of_nonneg_left hpass hP.le
    rw [← mul_assoc, mul_inv_cancel₀ hP.ne', one_mul] at this
    rw [mul_comm ηt Px]
    exact this
  · have := mul_le_mul_of_nonneg_left hbyp hP.le
    rw [← mul_assoc, mul_inv_cancel₀ hP.ne', one_mul] at this
    rw [mul_comm δt Px]
    exact this

/-- Diagonal transfer for all powers: unit-power parity counting and the unit-power L1 interface give the
homogeneous counting inequalities of the actual device. -/
theorem diagonal_transfer_homogeneous [AddCommGroup V] [Module ℂ V] (μ : Measure P) (D : Set P)
    (W : Submodule ℂ V) (pow : V → ℝ) (hpow : ∀ (z : ℂ) x, pow (z • x) = ‖z‖ ^ 2 * pow x)
    (Fpar : ℝ → V → P → ℂ) (Fact : ℕ → ℕ → V → P → ℂ)
    (hhom : ∀ n r (z : ℂ) x, Fact n r (z • x) = fun q => ((‖z‖ ^ 2 : ℝ) : ℂ) * Fact n r x q)
    (sc : ℕ → ℝ) (hsc : Tendsto sc atTop (𝓝[>] 0)) (ηt δt η' δ' : ℝ) (hη : ηt < η') (hδ : δ' < δt)
    (H1 : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ x ∈ W, pow x = 1 →
      η' ≤ passage μ D (Fpar a x) ∧ bypass μ D (Fpar a x) ≤ δ')
    (H2 : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ x ∈ W, pow x = 1 →
      Integrable (Fact n r x) μ ∧ Integrable (fun q => Fact n r x q - Fpar (sc n) x q) μ ∧
        ∫ q, ‖Fact n r x q - Fpar (sc n) x q‖ ∂μ ≤ ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop, ∀ x ∈ W, 0 < pow x →
      ηt * pow x ≤ passage μ D (Fact n r x) ∧ bypass μ D (Fact n r x) ≤ δt * pow x := by
  have h := diagonal_transfer_of_diff μ D {x | x ∈ W ∧ pow x = 1} Fpar Fact sc hsc ηt δt η' δ' hη hδ
    (H1.mono (fun a ha x hx => ha x hx.1 hx.2))
    (fun n ε hε => (H2 n ε hε).mono (fun r hr x hx => hr x hx.1 hx.2))
  filter_upwards [h] with n hn
  filter_upwards [hn] with r hr
  exact homogeneous_extension μ D W pow hpow (Fact n r) (hhom n r) ηt δt (fun x hx hp => hr x ⟨hx, hp⟩)

end Abstract


/-! ### Counted subspaces (manuscript Definition `pr:count`) -/

section Counted
open OQ14.ChannelScatteringMap
/-- The counted-subspace conditions of Definition `pr:count` for the finite input space: for every vector `a` of
the subspace `W`, the transmission `τ ‖a‖² ≤ ‖T a‖²`, the passage `η ‖T a‖² ≤ Pass a` and the absolute bypass
`Byp a ≤ δ ‖a‖²`, where `‖a‖² = physicalPower a`. -/
def IsCounted (W : Submodule ℂ (Idx →₀ ℂ)) (T : (Idx →₀ ℂ) →ₗ[ℂ] Ambient) (Pass Byp : (Idx →₀ ℂ) → ℝ)
    (τ η δ : ℝ) : Prop :=
  ∀ a ∈ W, τ * RestrictedTEIncoming.physicalPower a ≤ ‖T a‖ ^ 2 ∧ η * ‖T a‖ ^ 2 ≤ Pass a ∧
    Byp a ≤ δ * RestrictedTEIncoming.physicalPower a

theorem physicalPower_zero : RestrictedTEIncoming.physicalPower (0 : Idx →₀ ℂ) = 0 := by
  have h := RestrictedTEHomogeneousCount.physicalPower_smul (0 : ℂ) (0 : Idx →₀ ℂ)
  rw [smul_zero] at h
  simpa using h

/-- In the span of an orthonormal family of inputs, zero physical power forces the zero vector. -/
theorem span_power_zero {κ : Type*} [Fintype κ] (A : κ → Idx →₀ ℂ)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k))) (a : Idx →₀ ℂ)
    (ha : a ∈ Submodule.span ℂ (Set.range A)) (h0 : RestrictedTEIncoming.physicalPower a = 0) : a = 0 := by
  obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp ha
  rw [RestrictedTEPlaneJets.power_comb A horth cf] at h0
  have hz : ∀ k, ‖cf k‖ ^ 2 = 0 :=
    fun k => (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg ‖cf k‖)).mp h0 k (Finset.mem_univ k)
  have hc : ∀ k, cf k = 0 := fun k => norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero)|>.mp (hz k))
  simp [hc]

/-- From the counting inequalities of the actual device (all powers) and unit throughput on the span, the span of
the orthonormal inputs is a counted subspace for the actual scattering map. -/
theorem counted_of_counting {P : Type*} [MeasurableSpace P] (μ : Measure P) (D : Set P)
    {κ : Type*} [Fintype κ] (A : κ → Idx →₀ ℂ)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)))
    (Fpar : ℝ → (Idx →₀ ℂ) → P → ℂ) (Fact : ℕ → ℕ → (Idx →₀ ℂ) → P → ℂ)
    (hhom : ∀ n r (z : ℂ) x, Fact n r (z • x) = fun q => ((‖z‖ ^ 2 : ℝ) : ℂ) * Fact n r x q)
    (sc : ℕ → ℝ) (hsc : Tendsto sc atTop (𝓝[>] 0)) (ηt δt η' δ' : ℝ) (hη : ηt < η') (hδ : δ' < δt)
    (H1 : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ x ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower x = 1 →
      η' ≤ passage μ D (Fpar a x) ∧ bypass μ D (Fpar a x) ≤ δ')
    (H2 : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ x ∈ Submodule.span ℂ (Set.range A),
      RestrictedTEIncoming.physicalPower x = 1 →
      Integrable (Fact n r x) μ ∧ Integrable (fun q => Fact n r x q - Fpar (sc n) x q) μ ∧
        ∫ q, ‖Fact n r x q - Fpar (sc n) x q‖ ∂μ ≤ ε)
    (T : ℕ → ℕ → (Idx →₀ ℂ) →ₗ[ℂ] Ambient)
    (hiso : ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop, ∀ x ∈ Submodule.span ℂ (Set.range A),
      ‖T n r x‖ ^ 2 = RestrictedTEIncoming.physicalPower x)
    (τ : ℝ) (hτ : τ ≤ 1) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
      IsCounted (Submodule.span ℂ (Set.range A)) (T n r)
        (fun a => passage μ D (Fact n r a)) (fun a => bypass μ D (Fact n r a)) τ ηt δt := by
  have h := diagonal_transfer_homogeneous μ D (Submodule.span ℂ (Set.range A))
    RestrictedTEIncoming.physicalPower RestrictedTEHomogeneousCount.physicalPower_smul Fpar Fact hhom sc hsc
    ηt δt η' δ' hη hδ H1 H2
  filter_upwards [h, hiso] with n hn hn'
  filter_upwards [hn, hn'] with r hr hr' a ha
  have hP0 : 0 ≤ RestrictedTEIncoming.physicalPower a := RestrictedTEIncoming.physical_power_nonnegative a
  rw [hr' a ha]
  by_cases h0 : RestrictedTEIncoming.physicalPower a = 0
  · have ha0 : a = 0 := span_power_zero A horth a ha h0
    subst ha0
    have hF : Fact n r 0 = fun _ => 0 := by
      have := hhom n r 0 0
      rw [smul_zero] at this
      rw [this]
      funext q
      simp
    have hp : passage μ D (Fact n r 0) = 0 := by simp [passage, hF]
    have hb : bypass μ D (Fact n r 0) = 0 := by simp [bypass, hF]
    beta_reduce
    rw [hp, hb, h0]
    simp
  · have hpos : 0 < RestrictedTEIncoming.physicalPower a := lt_of_le_of_ne hP0 (Ne.symm h0)
    obtain ⟨hpass, hbyp⟩ := hr a ha hpos
    refine ⟨?_, hpass, hbyp⟩
    nlinarith

/-- The scattering map `T` read on the coefficient space `C^N` of the `N` inputs `A`:
`c ↦ T (∑ c_k A_k)`, as a continuous linear map on the Euclidean space `C^N`. -/
def coeffOperator {N : ℕ} (T : (Idx →₀ ℂ) →ₗ[ℂ] Ambient) (A : Fin N → Idx →₀ ℂ) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] Ambient :=
  LinearMap.toContinuousLinearMap
    (T ∘ₗ ((Fintype.linearCombination ℂ A).comp (WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).toLinearMap))

/-- Unit-throughput form of the finite-rank channel bound: if `T` is an isometry on the span of `N` orthonormal
inputs, no operator of rank below `N` approximates it on those inputs within `sqrt τ` (`τ ≤ 1`). -/
theorem no_low_rank_approximation {N : ℕ} (T : (Idx →₀ ℂ) →ₗ[ℂ] Ambient) (A : Fin N → Idx →₀ ℂ)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)))
    (hT : ∀ x ∈ Submodule.span ℂ (Set.range A), ‖T x‖ ^ 2 = RestrictedTEIncoming.physicalPower x)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1) (M : ℕ) (hM : M < N)
    (R : EuclideanSpace ℂ (Fin N) →L[ℂ] Ambient)
    (hrank : Module.finrank ℂ (LinearMap.range R.toLinearMap) ≤ M) :
    Real.sqrt τ ≤ ‖coeffOperator T A - R‖ := by
  by_contra hlt
  push_neg at hlt
  let U : EuclideanSpace ℂ (Fin N) →L[ℂ] Ambient := coeffOperator T A
  have hUx : ∀ x : EuclideanSpace ℂ (Fin N), ‖U x‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    have hmem : (∑ k, x k • A k) ∈ Submodule.span ℂ (Set.range A) :=
      (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨x, rfl⟩
    have h1 : U x = T (∑ k, x k • A k) := by
      simp [U, coeffOperator, Fintype.linearCombination_apply]
    rw [h1, hT _ hmem, RestrictedTEPlaneJets.power_comb A horth x, EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
  have hpower : ∀ x : EuclideanSpace ℂ (Fin N), τ * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2 := by
    intro x
    rw [hUx x]
    nlinarith [sq_nonneg ‖x‖]
  have hfin := OQ14.finite_rank_power_channel_bound U R τ M hτ0 hpower hlt hrank
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = N := by simp
  have := hfin.2
  omega

end Counted


/-! ### The concrete doubled device with the paired-shell actual device -/

section Concrete
open OQ14.ChannelScatteringMap OQ14.ChannelMaterialThroughput OQ14.RestrictedTEPartnerSmallness
  OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEConcreteDoubled OQ14.RestrictedTEPartnerBalls OQ14.RestrictedTEPlaneJets
  OQ14.RestrictedTEPartnerCount SymmetricHarmonicJets RestrictedTEPlaneLocal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positions of the original balls of the concrete device at scale `a`. -/
abbrev devicePos (r0 : ℝ) (y : ι → ℝ) (h : ℝ) : ℝ → ι → FourierL2.Space :=
  fun a l => abovePoint (hpoint r0 y l) (h * a)

/-- The parity plane flux density of the concrete doubled device (gain constant `b = 1`, so the gain at scale `a`
is `1 / a`, which is `q ^ n` at the scale `a = (q ^ n)⁻¹`). -/
abbrev parityFlux (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (a : ℝ)
    (x : Idx →₀ ℂ) : PlaneInverseCube.Plane → ℂ :=
  Fflux (fun a => partnerCentre (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 hρ
    hχ.le (partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi) a x

/-- Quadratic homogeneity of a plane flux family in the input. -/
def HomogeneousFlux (Fact : ℕ → ℕ → (Idx →₀ ℂ) → PlaneInverseCube.Plane → ℂ) : Prop :=
  ∀ n r (z : ℂ) (x : Idx →₀ ℂ), Fact n r (z • x) = fun ξ => ((‖z‖ ^ 2 : ℝ) : ℂ) * Fact n r x ξ

/-- The whole-plane L1 interface between the actual device flux `Fact n r` and the parity flux at the matching
scale `(q^n)⁻¹`: for every orthonormal family of finite inputs, every fixed gain index `n` and every `ε > 0`, for
all large shell indices `r` the actual flux is integrable and within `ε` in `L1(R²)` of the parity flux, uniformly
on the unit-power sphere of the span. -/
def L1Interface (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ)
    (Fact : ℕ → ℕ → (Idx →₀ ℂ) → PlaneInverseCube.Plane → ℂ) : Prop :=
  ∀ (N : ℕ) (A : Fin N → Idx →₀ ℂ), Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) →
    ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ x ∈ Submodule.span ℂ (Set.range A),
      RestrictedTEIncoming.physicalPower x = 1 →
        MeasureTheory.Integrable (Fact n r x) volume ∧
        MeasureTheory.Integrable (fun ξ => Fact n r x ξ - parityFlux r0 y ρ χ h R hρ hχ hi (scale q n) x ξ) volume ∧
        ∫ ξ, ‖Fact n r x ξ - parityFlux r0 y ρ χ h R hρ hχ hi (scale q n) x ξ‖ ≤ ε

theorem scale_tendsto_nhdsGT {q : ℝ} (hq : 1 < q) : Tendsto (fun n : ℕ => scale q n) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨scale_tendsto hq, Eventually.of_forall (fun n => scale_pos hq n)⟩

theorem device_carrier_le (p : ℝ → ι → FourierL2.Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hRb : R ≤ b)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) (n : ℕ) :
    ∀ x ∈ (deviceData p ρ χ R hρ hχ hi q hq n).carrier, ‖x‖ ≤ b := by
  intro x hx
  have hin : ∀ l, ‖p (scale q n) l‖ + ρ * scale q n ≤ R := fun l =>
    (add_le_add_left (mul_le_of_le_one_right hρ.le (scale_le_one hq.le n)) _).trans
      (hi (scale q n) (scale_pos hq n) (scale_le_one hq.le n) l)
  exact (partner_carrier_norm (p (scale q n)) (fun _ : ι => ρ * scale q n) χ hχ R hin x hx).trans hRb

/-- The scattering map of the actual paired-shell device with gain index `n` and shell index `r`, defined when the
inclusion radius `b` lies inside the inner shell radius (and zero otherwise). -/
def actualScatter (p : ℝ → ι → FourierL2.Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hRb : R ≤ b)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) (n r : ℕ) :
    (Idx →₀ ℂ) →ₗ[ℂ] Ambient :=
  if hbR : b ≤ (SourcePairedInclusion.data q hq.le n r).R then
    scatterMap (pairedCoeff q hq.le n r (deviceCoeff p ρ χ hχ q n))
      (pairedSupport q hq.le n r (deviceCoeff p ρ χ hχ q n) b hbR
        (SourcePairedReduction.inclusion_vanish (deviceCoeff p ρ χ hχ q n)
          (deviceData p ρ χ R hρ hχ hi q hq n) b (device_carrier_le p ρ χ R b hρ hχ hRb hi q hq n)))
  else 0

/-- Unit throughput of the actual device along the diagonal: for all large `n` and then all large `r`,
`‖actualScatter x‖² = physicalPower x` for every finite TE input `x`. -/
theorem actualScatter_norm_eventually (p : ℝ → ι → FourierL2.Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hb : 0 < b) (hRb : R ≤ b) (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop, ∀ x : Idx →₀ ℂ,
      ‖actualScatter p ρ χ R b hρ hχ hRb hi q hq n r x‖ ^ 2 = RestrictedTEIncoming.physicalPower x := by
  filter_upwards [partner_limitEffective_isUnit p ρ χ R b hρ hχ hb hRb hi q hq] with n hL
  filter_upwards [SourcePairedReduction.eventually_effective_isUnit q hq.le n (deviceCoeff p ρ χ hχ q n)
      (deviceData p ρ χ R hρ hχ hi q hq n) b hb (device_carrier_le p ρ χ R b hρ hχ hRb hi q hq n) hL,
    SourcePairedReduction.eventually_inner_radius q hq.le n b] with r hE hbR x
  unfold actualScatter
  rw [dif_pos hbR.le, paired_scatterMap_norm q hq.le n r (deviceCoeff p ρ χ hχ q n) b hbR.le
    (SourcePairedReduction.inclusion_vanish (deviceCoeff p ρ χ hχ q n) (deviceData p ρ χ R hρ hχ hi q hq n) b
      (device_carrier_le p ρ χ R b hρ hχ hRb hi q hq n)) hE x, RestrictedTEInput.input_norm_sq]

/-- The concrete doubled counting statement for an arbitrary half-turn symmetric section `D` with the local
half-plane structure at the dipole points (the proof of `RestrictedTEConcreteDoubled.concrete_doubled_counting`,
with the section as a parameter). -/
theorem concrete_doubled_counting_section (r : ℝ) (hr : 0 < r) (y : ι → ℝ) (hy : Function.Injective y)
    (ρ χ h δ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ) (hh : ρ < h) (hδ : 0 < δ) (hR : 0 ≤ R) (hb : b ≠ 0)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ i j, i ≠ j →
      δ ≤ dist (abovePoint (hpoint r y i) (h * a)) (abovePoint (hpoint r y j) (h * a)))
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r y l) (h * a)‖ + ρ ≤ R)
    (D : Set PlaneInverseCube.Plane) (hDsym : ∀ q : PlaneInverseCube.Plane, -q ∈ D ↔ q ∈ D)
    (hDloc : ∀ l, ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ s0 →
      D ∩ Metric.closedBall (hpoint r y l) s = (fun q => q - hpoint r y l) ⁻¹' (U nvec ∩ Metric.closedBall 0 s)) :
    ∃ (scale : ℝ) (N : ℕ) (A : Fin N → Index →₀ ℂ), 0 < scale ∧
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) ∧
      ∀ ηt δt : ℝ, ηt < 2 * (Vb ρ * halfPlane nvec h / scale) → 2 * (Vb ρ * halfPlane nvec h / scale) < δt →
        ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ A' ∈ Submodule.span ℂ (Set.range A),
          RestrictedTEIncoming.physicalPower A' = 1 →
          ηt ≤ passage volume D
              (Fflux (fun a => partnerCentre (fun l => abovePoint (hpoint r y l) (h * a))) ρ χ R b hρ hχ.le
                (partner_hi_aux (fun a l => abovePoint (hpoint r y l) (h * a)) ρ R hi) a A') ∧
          bypass volume D
              (Fflux (fun a => partnerCentre (fun l => abovePoint (hpoint r y l) (h * a))) ρ χ R b hρ hχ.le
                (partner_hi_aux (fun a l => abovePoint (hpoint r y l) (h * a)) ρ R hi) a A') ≤ δt := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hr0 : r ≠ 0 := hr.ne'
  have h0 : ∀ l, pts r y l 0 = r := fun l => by simp [pts, abovePoint, hpoint]
  have h1 : ∀ l, pts r y l 1 = y l := fun l => by simp [pts, abovePoint, hpoint]
  have h2 : ∀ l, pts r y l 2 = 0 := fun l => by simp [pts, abovePoint]
  obtain ⟨scale, hs, L, A, _, hjet, horth⟩ := PhysicalTEBandInterpolation.interpolate r hr0 y hy (pts r y)
    h0 h1 h2 (Fintype.card ι) (target χ e)
  refine ⟨scale, Fintype.card ι, A, hs, horth, ?_⟩
  intro ηt δt hlo hhi
  have hhpos : ∀ _ : ι, 0 < h := fun _ => by linarith
  have hγ : 0 < h - ρ := by linarith
  have hh1 : ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ l : ι, ((h - ρ) + ρ) * a ≤
      |(abovePoint (hpoint r y l) (h * a)) 2| := by
    intro a ha _ l
    rw [above_normal, abs_of_pos (mul_pos (by linarith) ha)]
    linarith
  have hspan : ∀ A' ∈ Submodule.span ℂ (Set.range A), ∃ cf : Fin (Fintype.card ι) → ℂ, ∑ k, cf k • A k = A' :=
    fun A' hA' => (Submodule.mem_span_range_iff_exists_fun ℂ).mp hA'
  have hT : ∀ A' ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A' = 1 → ∀ l,
      magnetic A' (MaxwellPlaneTail.planePoint (hpoint r y l)) 0 =
        -(mj A' (hpoint r y) (fun _ => nvec) l) * ((nvec 1 : ℝ) : ℂ) ∧
      magnetic A' (MaxwellPlaneTail.planePoint (hpoint r y l)) 1 =
        mj A' (hpoint r y) (fun _ => nvec) l * ((nvec 0 : ℝ) : ℂ) := by
    intro A' hA' _ l
    obtain ⟨cf, rfl⟩ := hspan A' hA'
    obtain ⟨_, h2', h3'⟩ := jets_of_interp r y scale χ e A hjet cf l
    unfold mj
    rw [h2', h3']
    simp [nvec_zero, nvec_one]
  have hK : ∀ A' ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A' = 1 → ∀ l,
      0 ≤ (kap ρ χ A' (hpoint r y) (fun _ => nvec) l).re ∧
        (kap ρ χ A' (hpoint r y) (fun _ => nvec) l).im = 0 := by
    intro A' hA' _ l
    obtain ⟨cf, rfl⟩ := hspan A' hA'
    rw [kap_value r y ρ scale χ hs hχ e A hjet cf l, Complex.ofReal_re, Complex.ofReal_im]
    refine ⟨?_, rfl⟩
    have : 0 ≤ Vb ρ := by unfold Vb; positivity
    positivity
  have hB : ∀ A' ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A' = 1 →
      ∑ l, (kap ρ χ A' (hpoint r y) (fun _ => nvec) l).re * halfPlane nvec h =
        Vb ρ * halfPlane nvec h / scale := by
    intro A' hA' hpow
    obtain ⟨cf, rfl⟩ := hspan A' hA'
    have hsum : (∑ k, ‖cf k‖ ^ 2) = 1 := by rw [← power_comb A horth cf]; exact hpow
    simp_rw [kap_value r y ρ scale χ hs hχ e A hjet cf, Complex.ofReal_re]
    have : (∑ l : ι, Vb ρ * ‖cf (e l)‖ ^ 2 / scale * halfPlane nvec h) =
        Vb ρ * halfPlane nvec h / scale * ∑ l : ι, ‖cf (e l)‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [this, Equiv.sum_comp e (fun k => ‖cf k‖ ^ 2), hsum, mul_one]
  have hsepD : ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ i j : ι ⊕ ι, i ≠ j → min δ (2 * |r|) ≤
      dist (partnerCentre (fun l => abovePoint (hpoint r y l) (h * a)) i)
        (partnerCentre (fun l => abovePoint (hpoint r y l) (h * a)) j) :=
    fun a _ _ => partner_separation r δ (h * a) (hpoint r y) (fun l => hpoint_zero r y l) (hsep a ‹_› ‹_›)
  have hδ' : 0 < min δ (2 * |r|) := lt_min hδ (by positivity)
  have hcdD : ∀ i j : ι ⊕ ι, i ≠ j → cD (hpoint r y) i ≠ cD (hpoint r y) j := by
    intro i j hij heq
    simp only [cD] at heq
    rcases i with l | l <;> rcases j with k | k
    · exact hpoint_inj r y hy l k (fun hlk => hij (by rw [hlk])) heq
    · have := congrArg (fun q : PlaneInverseCube.Plane => q 0) heq
      simp [hpoint_zero] at this
      linarith
    · have := congrArg (fun q : PlaneInverseCube.Plane => q 0) heq
      simp [hpoint_zero] at this
      linarith
    · exact hpoint_inj r y hy l k (fun hlk => hij (by rw [hlk])) (neg_inj.mp heq)
  exact doubled_device_counting (fun a l => abovePoint (hpoint r y l) (h * a)) ρ χ (min δ (2 * |r|)) R b (h - ρ)
    hρ hχ.le hδ' hR hb hγ hsepD (partner_hi_aux _ ρ R hi) (partner_hh_aux _ (h - ρ) ρ hh1)
    (hpoint r y) (fun _ => h) hhpos (fun a l => rfl) hcdD (fun _ => nvec) (fun _ => norm_nvec) D
    hDsym hDloc A horth hT hK (Vb ρ * halfPlane nvec h / scale) ηt δt hB hlo hhi

/-- Counted channels of the actual device for an arbitrary symmetric section.  For the concrete doubled device
(`2 card ι` balls of radius `ρ a` at height `h a` above the points `(r0, y_l)` and their half-turn images, the
symmetric section `D`, orthonormal interpolated inputs `A`), and a family `Fact` of plane flux densities of the
actual paired-shell device that is quadratically homogeneous (`hhom`) and satisfies the whole-plane L1 interface
(`H2`), the span of `A` is a counted subspace of the actual device (manuscript Definition `pr:count`) for all large
gain indices `n` and then all large shell indices `r`: transmission is exact (unit throughput, by the audited
isometry of the scattering map), the passage is at least `ηt` times the power and the absolute bypass at most `δt`
times the power, for every `ηt < p0 < δt` where `p0 = 2 Vb(ρ) halfPlane(nvec, h) / jetScale` is the passage constant
of the doubled device, and the dimension of the span is `card ι`. -/
theorem actual_counted_subspaces_section (r0 : ℝ) (hr0 : 0 < r0) (y : ι → ℝ) (hy : Function.Injective y)
    (ρ χ h δ R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ) (hh : ρ < h) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ i j, i ≠ j →
      δ ≤ dist (abovePoint (hpoint r0 y i) (h * a)) (abovePoint (hpoint r0 y j) (h * a)))
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R)
    (D : Set PlaneInverseCube.Plane) (hDsym : ∀ q : PlaneInverseCube.Plane, -q ∈ D ↔ q ∈ D)
    (hDloc : ∀ l, ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ s0 →
      D ∩ Metric.closedBall (hpoint r0 y l) s = (fun q => q - hpoint r0 y l) ⁻¹' (U nvec ∩ Metric.closedBall 0 s))
    (q : ℝ) (hq : 1 < q) (Fact : ℕ → ℕ → (Idx →₀ ℂ) → PlaneInverseCube.Plane → ℂ)
    (hhom : HomogeneousFlux Fact) (H2 : L1Interface r0 y ρ χ h R hρ hχ hi q Fact) :
    ∃ (jetScale : ℝ) (N : ℕ) (A : Fin N → Idx →₀ ℂ), 0 < jetScale ∧
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      ∀ ηt δt : ℝ, ηt < 2 * (Vb ρ * halfPlane nvec h / jetScale) →
        2 * (Vb ρ * halfPlane nvec h / jetScale) < δt → ∀ τ : ℝ, τ ≤ 1 →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume D (Fact n r a))
            (fun a => bypass volume D (Fact n r a)) τ ηt δt := by
  obtain ⟨jetScale, N, A, hs, horth, hcount⟩ :=
    concrete_doubled_counting_section r0 hr0 y hy ρ χ h δ R 1 hρ hχ hh hδ hR one_ne_zero hsep hi D hDsym hDloc
  refine ⟨jetScale, N, A, hs, horth, ?_, ?_⟩
  · have hli : LinearIndependent ℂ A :=
      LinearIndependent.of_comp (RestrictedTEInput.input : (Idx →₀ ℂ) →ₗ[ℂ] Ambient) horth.linearIndependent
    rw [finrank_span_eq_card hli]
    simp
  · intro ηt δt hlo hhi τ hτ
    have hb : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
    have H1 := hcount ((ηt + 2 * (Vb ρ * halfPlane nvec h / jetScale)) / 2)
      ((2 * (Vb ρ * halfPlane nvec h / jetScale) + δt) / 2) (by linarith) (by linarith)
    exact counted_of_counting volume D A horth (parityFlux r0 y ρ χ h R hρ hχ hi) Fact hhom
      (fun n => scale q n) (scale_tendsto_nhdsGT hq) ηt δt ((ηt + 2 * (Vb ρ * halfPlane nvec h / jetScale)) / 2)
      ((2 * (Vb ρ * halfPlane nvec h / jetScale) + δt) / 2) (by linarith) (by linarith) H1 (H2 N A horth)
      (fun n r => actualScatter (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le
        (le_max_left R 1) hi q hq n r)
      ((actualScatter_norm_eventually (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le
        hb (le_max_left R 1) hi q hq).mono (fun n hn => hn.mono (fun r hr x _ => hr x))) τ hτ

/-- No finite-rank channel model of the actual device: for all large `n` and then all large `r`, for every
`N` orthonormal finite inputs, every `τ ∈ [0, 1]` and every operator `R` of rank `M < N` on the coefficient space
of the inputs, the scattering map of the actual device is at distance at least `sqrt τ` from `R` on those inputs
(`OQ14.finite_rank_power_channel_bound` with unit throughput). -/
theorem actual_device_no_low_rank (p : ℝ → ι → FourierL2.Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hb : 0 < b) (hRb : R ≤ b) (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop, ∀ (N : ℕ) (A : Fin N → Idx →₀ ℂ),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) → ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → ∀ M : ℕ, M < N →
      ∀ R' : EuclideanSpace ℂ (Fin N) →L[ℂ] Ambient,
        Module.finrank ℂ (LinearMap.range R'.toLinearMap) ≤ M →
        Real.sqrt τ ≤ ‖coeffOperator (actualScatter p ρ χ R b hρ hχ hRb hi q hq n r) A - R'‖ :=
  (actualScatter_norm_eventually p ρ χ R b hρ hχ hb hRb hi q hq).mono fun n hn =>
    hn.mono fun r hr _ A horth τ h0 h1 M hM R' hrank =>
      no_low_rank_approximation (actualScatter p ρ χ R b hρ hχ hRb hi q hq n r) A horth (fun x _ => hr x) τ h0 h1
        M hM R' hrank

/-- The same for the unbounded symmetric section `{|x| > r0}` of the concrete doubled device. -/
theorem actual_counted_subspaces (r0 : ℝ) (hr0 : 0 < r0) (y : ι → ℝ) (hy : Function.Injective y)
    (ρ χ h δ R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ) (hh : ρ < h) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ i j, i ≠ j →
      δ ≤ dist (abovePoint (hpoint r0 y i) (h * a)) (abovePoint (hpoint r0 y j) (h * a)))
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R)
    (q : ℝ) (hq : 1 < q) (Fact : ℕ → ℕ → (Idx →₀ ℂ) → PlaneInverseCube.Plane → ℂ)
    (hhom : HomogeneousFlux Fact) (H2 : L1Interface r0 y ρ χ h R hρ hχ hi q Fact) :
    ∃ (jetScale : ℝ) (N : ℕ) (A : Fin N → Idx →₀ ℂ), 0 < jetScale ∧
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      ∀ ηt δt : ℝ, ηt < 2 * (Vb ρ * halfPlane nvec h / jetScale) →
        2 * (Vb ρ * halfPlane nvec h / jetScale) < δt → ∀ τ : ℝ, τ ≤ 1 →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dsym r0) (Fact n r a))
            (fun a => bypass volume (Dsym r0) (Fact n r a)) τ ηt δt :=
  actual_counted_subspaces_section r0 hr0 y hy ρ χ h δ R hρ hχ hh hδ hR hsep hi (Dsym r0) (Dsym_neg r0)
    (fun l => ⟨r0, hr0, fun s _ hs => hD_sym r0 y l s hs⟩) q hq Fact hhom H2

/-! ### A bounded symmetric section -/

/-- The bounded half-turn symmetric section: `{|x| > r0}` intersected with the open disk of radius `T`. -/
def Dbdd (r0 T : ℝ) : Set PlaneInverseCube.Plane := Dsym r0 ∩ Metric.ball 0 T

theorem Dbdd_neg (r0 T : ℝ) (q : PlaneInverseCube.Plane) : -q ∈ Dbdd r0 T ↔ q ∈ Dbdd r0 T := by
  simp [Dbdd, Dsym, abs_neg]

theorem Dbdd_bounded (r0 T : ℝ) : Bornology.IsBounded (Dbdd r0 T) :=
  Metric.isBounded_ball.subset Set.inter_subset_right

theorem Dbdd_local (r0 : ℝ) (hr0 : 0 < r0) (y : ι → ℝ) (T : ℝ) (hT : ∀ l, ‖hpoint r0 y l‖ < T) (l : ι) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ s0 →
      Dbdd r0 T ∩ Metric.closedBall (hpoint r0 y l) s =
        (fun q => q - hpoint r0 y l) ⁻¹' (U nvec ∩ Metric.closedBall 0 s) := by
  refine ⟨min r0 ((T - ‖hpoint r0 y l‖) / 2), lt_min hr0 (by linarith [hT l]), ?_⟩
  intro s hs hs0
  have hsr : s ≤ r0 := hs0.trans (min_le_left _ _)
  have hsT : s ≤ (T - ‖hpoint r0 y l‖) / 2 := hs0.trans (min_le_right _ _)
  rw [← hD_sym r0 y l s hsr]
  ext z
  simp only [Dbdd, Set.mem_inter_iff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    have hz : ‖z‖ ≤ ‖z - hpoint r0 y l‖ + ‖hpoint r0 y l‖ := by
      have := norm_add_le (z - hpoint r0 y l) (hpoint r0 y l)
      rwa [sub_add_cancel] at this
    rw [dist_eq_norm] at h3
    linarith [hT l]

/-- Counted channels of the actual device through a bounded symmetric section (the open disk of radius `T`
intersected with `{|x| > r0}`, `T` larger than the norms of all dipole points). -/
theorem actual_counted_subspaces_bounded (r0 : ℝ) (hr0 : 0 < r0) (y : ι → ℝ) (hy : Function.Injective y)
    (ρ χ h δ R T : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ) (hh : ρ < h) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ i j, i ≠ j →
      δ ≤ dist (abovePoint (hpoint r0 y i) (h * a)) (abovePoint (hpoint r0 y j) (h * a)))
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R)
    (hT : ∀ l, ‖hpoint r0 y l‖ < T)
    (q : ℝ) (hq : 1 < q) (Fact : ℕ → ℕ → (Idx →₀ ℂ) → PlaneInverseCube.Plane → ℂ)
    (hhom : HomogeneousFlux Fact) (H2 : L1Interface r0 y ρ χ h R hρ hχ hi q Fact) :
    ∃ (jetScale : ℝ) (N : ℕ) (A : Fin N → Idx →₀ ℂ), 0 < jetScale ∧
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      ∀ ηt δt : ℝ, ηt < 2 * (Vb ρ * halfPlane nvec h / jetScale) →
        2 * (Vb ρ * halfPlane nvec h / jetScale) < δt → ∀ τ : ℝ, τ ≤ 1 →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dbdd r0 T) (Fact n r a))
            (fun a => bypass volume (Dbdd r0 T) (Fact n r a)) τ ηt δt :=
  actual_counted_subspaces_section r0 hr0 y hy ρ χ h δ R hρ hχ hh hδ hR hsep hi (Dbdd r0 T) (Dbdd_neg r0 T)
    (Dbdd_local r0 hr0 y T hT) q hq Fact hhom H2

end Concrete

end OQ14.RestrictedTEActualCounting
#print axioms OQ14.RestrictedTEActualCounting.diagonal_transfer
#print axioms OQ14.RestrictedTEActualCounting.diagonal_transfer_of_diff
#print axioms OQ14.RestrictedTEActualCounting.homogeneous_extension
#print axioms OQ14.RestrictedTEActualCounting.diagonal_transfer_homogeneous
#print axioms OQ14.RestrictedTEActualCounting.physicalPower_zero
#print axioms OQ14.RestrictedTEActualCounting.span_power_zero
#print axioms OQ14.RestrictedTEActualCounting.counted_of_counting
#print axioms OQ14.RestrictedTEActualCounting.no_low_rank_approximation
#print axioms OQ14.RestrictedTEActualCounting.scale_tendsto_nhdsGT
#print axioms OQ14.RestrictedTEActualCounting.device_carrier_le
#print axioms OQ14.RestrictedTEActualCounting.actualScatter_norm_eventually
#print axioms OQ14.RestrictedTEActualCounting.concrete_doubled_counting_section
#print axioms OQ14.RestrictedTEActualCounting.actual_counted_subspaces_section
#print axioms OQ14.RestrictedTEActualCounting.actual_counted_subspaces
#print axioms OQ14.RestrictedTEActualCounting.Dbdd_neg
#print axioms OQ14.RestrictedTEActualCounting.Dbdd_bounded
#print axioms OQ14.RestrictedTEActualCounting.Dbdd_local
#print axioms OQ14.RestrictedTEActualCounting.actual_counted_subspaces_bounded
#print axioms OQ14.RestrictedTEActualCounting.actual_device_no_low_rank
