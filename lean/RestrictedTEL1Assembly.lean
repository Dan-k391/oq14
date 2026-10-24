import RestrictedTEActualCounting
import RestrictedTEConcreteDoubled
import RestrictedTETotalFlux
import RestrictedTEPointTail
import RestrictedTECoherentTail
import HerglotzParityPlane
import SourceParityFlux
import ParityPlaneBounds
import PlaneInverseCube

/-! Abstract reduction of the whole-plane `L1` interface to compact convergence plus inverse-cube tails, the
parity tail majorant uniform on the unit-power sphere of a finite orthonormal span, and generic quadratic
homogeneity.

Part A.  If the actual flux converges to the parity flux in `L1` on every disk, uniformly on a set `S` of inputs, and
both fluxes have the pointwise majorant `C / ‖ξ‖³` beyond a fixed radius (for large shell index), then the
whole-plane `L1` distance tends to zero uniformly on `S`: the tails beyond `T` contribute at most
`2 C diskConstant / T`.  `L1Interface_of_compact_and_tails` puts this in the exact shape of `L1Interface`.
Part B.  The parity total flux of the concrete doubled device at a fixed scale has, for every pair of basis inputs,
the pointwise majorant `C / ‖q‖³` beyond a radius.  On the plane the mixed total flux splits exactly into six
pieces (`mixed_identity`): exterior electric field against the incident magnetic field, exterior against exterior,
exterior electric against the parity-true magnetic field, parity-false electric against the incident magnetic
field, against the exterior magnetic field, and against the parity-true magnetic field.  Each piece has an audited
pointwise inverse-cube tail.  The sesquilinear expansion over an orthonormal family gives a bound uniform on the
unit-power sphere (`parityFlux_tail`).  Integrability of the parity flux comes from `whole_bounds`.
`L1Interface_of_actual_estimates` leaves exactly three estimates on the actual flux.
Part C.  Linear fields give a quadratically homogeneous flux (`homogeneous_of_linear`), applied to the parity
flux in `parityFlux_homogeneous`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEL1Assembly
open MeasureTheory Filter Topology Metric Set

/-! ### Part A: compact convergence plus tails -/

theorem tail_set_eq (T : ℝ) : {ξ : PlaneInverseCube.Plane | T < ‖ξ‖} = (closedBall (0 : PlaneInverseCube.Plane) T)ᶜ := by
  ext ξ
  simp [mem_closedBall, dist_zero_right]

theorem integrable_of_ball_and_tail (f : PlaneInverseCube.Plane → ℂ) (T K : ℝ) (hT : 0 < T)
    (hball : IntegrableOn f (closedBall (0 : PlaneInverseCube.Plane) T) volume)
    (hmeas : AEStronglyMeasurable f volume) (hb : ∀ ξ, T < ‖ξ‖ → ‖f ξ‖ ≤ K / ‖ξ‖ ^ 3) :
    Integrable f volume := by
  have ht := PlaneInverseCube.tail_integrable T K hT hmeas.restrict hb
  rw [tail_set_eq] at ht
  simpa only [union_compl_self, integrableOn_univ] using hball.union ht

theorem integral_norm_le_ball_add_tail (f : PlaneInverseCube.Plane → ℂ) (T K : ℝ) (hT : 0 < T)
    (hint : Integrable f volume) (hb : ∀ ξ, T < ‖ξ‖ → ‖f ξ‖ ≤ K / ‖ξ‖ ^ 3) :
    ∫ ξ, ‖f ξ‖ ≤ (∫ ξ in closedBall (0 : PlaneInverseCube.Plane) T, ‖f ξ‖) + K * PlaneInverseCube.diskConstant / T := by
  have h1 := integral_add_compl (measurableSet_closedBall (x := (0 : PlaneInverseCube.Plane)) (ε := T)) hint.norm
  have h2 := PlaneInverseCube.tail_integral_bound T K hT hint.aestronglyMeasurable.restrict hb
  rw [tail_set_eq] at h2
  linarith

/-- Abstract reduction: compact `L1` convergence uniform on `S` plus pointwise inverse-cube tail majorants of both
fluxes give whole-plane `L1` convergence uniform on `S`. -/
theorem l1_of_compact_and_tails {V : Type*} (S : Set V) (F : ℕ → V → PlaneInverseCube.Plane → ℂ)
    (G : V → PlaneInverseCube.Plane → ℂ)
    (hFm : ∀ r, ∀ x ∈ S, AEStronglyMeasurable (F r x) volume)
    (hG : ∀ x ∈ S, Integrable (G x) volume)
    (hcompact : ∀ ρ0 : ℝ, 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ x ∈ S,
      IntegrableOn (fun ξ => F r x ξ - G x ξ) (closedBall 0 ρ0) volume ∧
        ∫ ξ in closedBall 0 ρ0, ‖F r x ξ - G x ξ‖ ≤ ε)
    (C ρ1 : ℝ) (r1 : ℕ)
    (htailF : ∀ r ≥ r1, ∀ x ∈ S, ∀ ξ, ρ1 ≤ ‖ξ‖ → ‖F r x ξ‖ ≤ C / ‖ξ‖ ^ 3)
    (htailG : ∀ x ∈ S, ∀ ξ, ρ1 ≤ ‖ξ‖ → ‖G x ξ‖ ≤ C / ‖ξ‖ ^ 3) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ x ∈ S,
      Integrable (F r x) volume ∧ Integrable (fun ξ => F r x ξ - G x ξ) volume ∧
        ∫ ξ, ‖F r x ξ - G x ξ‖ ≤ ε := by
  intro ε hε
  have hdC0 : 0 ≤ PlaneInverseCube.diskConstant := by
    unfold PlaneInverseCube.diskConstant
    exact mul_nonneg zero_le_two measureReal_nonneg
  set K : ℝ := max C 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hCK : C ≤ K := le_max_left _ _
  set T : ℝ := max ρ1 (max 1 (4 * K * PlaneInverseCube.diskConstant / ε + 1)) with hT
  have hT1 : 1 ≤ T := (le_max_left 1 _).trans (le_max_right _ _)
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  have hTρ : ρ1 ≤ T := le_max_left _ _
  have hTε : 4 * K * PlaneInverseCube.diskConstant / ε + 1 ≤ T := (le_max_right 1 _).trans (le_max_right _ _)
  filter_upwards [hcompact T hT0 (ε / 2) (half_pos hε), eventually_ge_atTop r1] with r hc hr x hx
  obtain ⟨hint, hle⟩ := hc x hx
  have hbF : ∀ ξ : PlaneInverseCube.Plane, T < ‖ξ‖ → ‖F r x ξ‖ ≤ K / ‖ξ‖ ^ 3 := by
    intro ξ hξ
    have hpos : 0 < ‖ξ‖ ^ 3 := by have : 0 < ‖ξ‖ := lt_trans hT0 hξ; positivity
    exact (htailF r hr x hx ξ (hTρ.trans hξ.le)).trans (div_le_div_of_nonneg_right hCK hpos.le)
  have hbG : ∀ ξ : PlaneInverseCube.Plane, T < ‖ξ‖ → ‖G x ξ‖ ≤ K / ‖ξ‖ ^ 3 := by
    intro ξ hξ
    have hpos : 0 < ‖ξ‖ ^ 3 := by have : 0 < ‖ξ‖ := lt_trans hT0 hξ; positivity
    exact (htailG x hx ξ (hTρ.trans hξ.le)).trans (div_le_div_of_nonneg_right hCK hpos.le)
  have hFint : Integrable (F r x) volume := by
    refine integrable_of_ball_and_tail (F r x) T K hT0 ?_ (hFm r x hx) hbF
    have : F r x = fun ξ => (F r x ξ - G x ξ) + G x ξ := funext fun ξ => (sub_add_cancel _ _).symm
    rw [this]
    exact hint.add (hG x hx).integrableOn
  have hDint : Integrable (fun ξ => F r x ξ - G x ξ) volume := hFint.sub (hG x hx)
  refine ⟨hFint, hDint, ?_⟩
  have hbD : ∀ ξ : PlaneInverseCube.Plane, T < ‖ξ‖ → ‖F r x ξ - G x ξ‖ ≤ (2 * K) / ‖ξ‖ ^ 3 := by
    intro ξ hξ
    have h := (norm_sub_le (F r x ξ) (G x ξ)).trans (add_le_add (hbF ξ hξ) (hbG ξ hξ))
    calc _ ≤ K / ‖ξ‖ ^ 3 + K / ‖ξ‖ ^ 3 := h
      _ = (2 * K) / ‖ξ‖ ^ 3 := by ring
  have h1 := integral_norm_le_ball_add_tail (fun ξ => F r x ξ - G x ξ) T (2 * K) hT0 hDint hbD
  have h2 : 2 * K * PlaneInverseCube.diskConstant / T ≤ ε / 2 := by
    rw [div_le_iff₀ hT0]
    have h3 : 4 * K * PlaneInverseCube.diskConstant / ε ≤ T - 1 := by linarith
    have h4 : 4 * K * PlaneInverseCube.diskConstant ≤ (T - 1) * ε := by
      rwa [div_le_iff₀ hε] at h3
    nlinarith
  linarith

/-! ### The shape of `L1Interface` -/

open OQ14.RestrictedTEActualCounting OQ14.RestrictedTEPartnerSmallness OQ14.RestrictedTEDipoleProfile
  OQ14.RestrictedTEConcreteDevice

/-- `L1Interface` follows from compact convergence on every disk, measurability, and pointwise inverse-cube tail
majorants (for large shell index) of the actual flux and of the parity flux at the matching scale, uniformly on the
unit-power sphere of the span of every orthonormal family. -/
theorem L1Interface_of_compact_and_tails {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ)
    (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ)
    (Fact : ℕ → ℕ → (SymmetricHarmonicJets.Index →₀ ℂ) → PlaneInverseCube.Plane → ℂ)
    (hmeas : ∀ n r x, AEStronglyMeasurable (Fact n r x) volume)
    (hG : ∀ n x, Integrable (parityFlux r0 y ρ χ h R hρ hχ hi (scale q n) x) volume)
    (hcompact : ∀ (N : ℕ) (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) → ∀ n : ℕ, ∀ ρ0 : ℝ, 0 < ρ0 → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ r : ℕ in atTop, ∀ x ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower x = 1 →
          IntegrableOn (fun ξ => Fact n r x ξ - parityFlux r0 y ρ χ h R hρ hχ hi (scale q n) x ξ)
            (closedBall 0 ρ0) volume ∧
          ∫ ξ in closedBall 0 ρ0, ‖Fact n r x ξ - parityFlux r0 y ρ χ h R hρ hχ hi (scale q n) x ξ‖ ≤ ε)
    (htail : ∀ (N : ℕ) (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) → ∀ n : ℕ, ∃ (C ρ1 : ℝ) (r1 : ℕ),
        (∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower x = 1 →
          ∀ ξ, ρ1 ≤ ‖ξ‖ → ‖Fact n r x ξ‖ ≤ C / ‖ξ‖ ^ 3) ∧
        (∀ x ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower x = 1 →
          ∀ ξ, ρ1 ≤ ‖ξ‖ → ‖parityFlux r0 y ρ χ h R hρ hχ hi (scale q n) x ξ‖ ≤ C / ‖ξ‖ ^ 3)) :
    L1Interface r0 y ρ χ h R hρ hχ hi q Fact := by
  intro N A horth n ε hε
  obtain ⟨C, ρ1, r1, hF, hGt⟩ := htail N A horth n
  have h := l1_of_compact_and_tails
    {x | x ∈ Submodule.span ℂ (Set.range A) ∧ RestrictedTEIncoming.physicalPower x = 1}
    (Fact n) (parityFlux r0 y ρ χ h R hρ hχ hi (scale q n))
    (fun r x _ => hmeas n r x) (fun x _ => hG n x)
    (fun ρ0 hρ0 ε' hε' => (hcompact N A horth n ρ0 hρ0 ε' hε').mono
      (fun r hr x hx => hr x hx.1 hx.2))
    C ρ1 r1 (fun r hr x hx ξ hξ => hF r hr x hx.1 hx.2 ξ hξ) (fun x hx ξ hξ => hGt x hx.1 hx.2 ξ hξ) ε hε
  filter_upwards [h] with r hr x hx hp
  exact hr x ⟨hx, hp⟩

/-! ### Part C: generic homogeneity -/

/-- Fields linear in the input give a quadratically homogeneous flux. -/
theorem homogeneous_of_linear
    (E H : ℕ → ℕ → (SymmetricHarmonicJets.Index →₀ ℂ) → PlaneInverseCube.Plane → Maxwell.Vector)
    (hE : ∀ n r (z : ℂ) x ξ, E n r (z • x) ξ = z • E n r x ξ)
    (hH : ∀ n r (z : ℂ) x ξ, H n r (z • x) ξ = z • H n r x ξ) :
    HomogeneousFlux (fun n r x ξ => crossProduct (E n r x ξ) (Maxwell.conjugate (H n r x ξ)) 2) := by
  intro n r z x
  funext ξ
  simp only [hE, hH, RestrictedTETotalLinear.cross_two, Maxwell.conjugate, Pi.smul_apply, smul_eq_mul, map_mul]
  have := Complex.mul_conj' z
  push_cast
  linear_combination (E n r x ξ 0 * (starRingEnd ℂ) (H n r x ξ 1) - E n r x ξ 1 * (starRingEnd ℂ) (H n r x ξ 0)) * this


/-! ### Part B: pointwise inverse-cube tails of the parity total flux -/

section ParityTail
open Complex Maxwell PlaneSourceKernel MaxwellRadiation SymmetricHarmonicJets
open scoped ComplexConjugate

/-- The mixed total flux (electric field of one source against the magnetic field of another) splits on the plane
into the dynamic mixed flux, the exterior bilinear flux, and the four parity pieces. -/
theorem mixed_identity (B : ℝ) (S S' : Source) (A A' : Index →₀ ℂ) (q : PlaneInverseCube.Plane) :
    crossProduct (ParityPlaneFields.totalElectric 1 B S (RestrictedTEPlaneLocal.electric A)
        (MaxwellPlaneTail.planePoint q))
      (conjugate (ParityPlaneFields.totalMagnetic 1 B S' (RestrictedTEPlaneLocal.magnetic A')
        (MaxwellPlaneTail.planePoint q))) 2 =
    RestrictedTEPlaneLocal.dynamicMixed S A' q + MaxwellPlaneL1.flux 1 S S' q +
      (conj (((B ^ 2 - 1 : ℝ) : ℂ)) * SourceParityFlux.electric true 1 S S' q +
      (((B⁻¹ ^ 2 - 1 : ℝ) : ℂ) * RestrictedTEReactionFlux.flux false S A' q +
      (((B⁻¹ ^ 2 - 1 : ℝ) : ℂ) * SourceParityFlux.magnetic false 1 S S' q +
      (((B⁻¹ ^ 2 - 1 : ℝ) : ℂ) * conj (((B ^ 2 - 1 : ℝ) : ℂ)) * ParityPlaneBounds.flux false true 1 S S' q)))) := by
  have hi (i : Fin 3) (h : i ≠ 2) :
      RestrictedTEPlaneLocal.electric A (MaxwellPlaneTail.planePoint q) i = 0 :=
    RestrictedTEPlaneLocal.electric_tangent_zero A q i h
  have he (i : Fin 3) (h : i ≠ 2) :
      ParityPlaneFields.electric true 1 S (MaxwellPlaneTail.planePoint q) i = 0 :=
    ParityPlaneFields.electric_true_zero 1 S _ (by rfl) i h
  have hh (i : Fin 3) (h : i ≠ 2) :
      ParityPlaneFields.magnetic false 1 S' (MaxwellPlaneTail.planePoint q) i = 0 :=
    ParityPlaneFields.magnetic_false_zero 1 S' _ (by rfl) i h
  unfold ParityPlaneFields.totalElectric ParityPlaneFields.totalMagnetic RestrictedTEPlaneLocal.dynamicMixed
    MaxwellPlaneL1.flux MaxwellPlaneTail.bilinearFlux SourceParityFlux.electric SourceParityFlux.magnetic
    ParityPlaneBounds.flux RestrictedTEReactionFlux.flux
  simp [cross_apply, conjugate]
  rw [hi 0 (by decide), hi 1 (by decide), he 0 (by decide), he 1 (by decide), hh 0 (by decide), hh 1 (by decide)]
  simp only [mul_zero, zero_add, add_zero, map_add, map_mul, map_zero, Complex.star_def]
  ring

/-- Pointwise inverse-cube tail of the parity-electric flux against a fixed finite harmonic TE magnetic field,
proportional to the source mass and uniform over admissible sources. -/
theorem reaction_flux_tail (A : Index →₀ ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ T : ℝ, 2 ≤ T ∧ 2 * R ≤ T ∧ ∀ (e : Bool) (d : ℝ) (S : Source), Admissible R d S →
      ∀ q : PlaneInverseCube.Plane, T < ‖q‖ →
        ‖RestrictedTEReactionFlux.flux e S A q‖ ≤ K * sourceMass S / ‖q‖ ^ 3 := by
  obtain ⟨K, hK, T, hT, hTR, hb⟩ := RestrictedTEPointTail.reaction_tail A R hR
  refine ⟨K, hK, T, hT, hTR, ?_⟩
  intro e d S hS q hq
  unfold RestrictedTEReactionFlux.flux
  rw [ParityPlaneColumns.electric_cross e 1 S hS.integrable]
  refine (ParityPlaneColumns.sum_integral_bound S hS.integrable _
    (fun j => ParityPlaneColumns.electric_cross_integrable e 1 S hS.integrable _ _ j) (K / ‖q‖ ^ 3) ?_).trans_eq
    (by ring)
  intro j
  filter_upwards with y
  by_cases hy : S j y = 0
  · simp [hy]
  · have hs : y ∈ closedBall (0 : FourierL2.Space) R := by
      by_contra hn
      exact hy (hS.support j y hn)
    rw [norm_mul]
    have := hb e (MaxwellPlaneTail.planePoint q) y j (by rwa [MaxwellPlaneTail.planePoint_norm]) (by rfl) hs
    rw [MaxwellPlaneTail.planePoint_norm] at this
    exact (mul_le_mul_of_nonneg_left this (norm_nonneg (S j y))).trans_eq (by ring)

theorem scaled_tail (z X : ℂ) (c t : ℝ) (h : ‖X‖ ≤ c / t) : ‖z * X‖ ≤ (‖z‖ * c) / t := by
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg z)


/-- Pointwise inverse-cube tail of every entry `fluxForm q A A'` of the sesquilinear form of the finite-ball
parity total flux, at a fixed scale `a` with admissible gap `d`. -/
theorem pair_tail {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ → ι → FourierL2.Space) (ρ χ R b : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (hR : 0 ≤ R)
    (a d : ℝ) (hd : 0 < d) (ha : 0 < a) (ha1 : a ≤ 1) (hh : ∀ l, d + ρ * a ≤ |p a l 2|)
    (A A' : Index →₀ ℂ) :
    ∃ K T : ℝ, ∀ q : PlaneInverseCube.Plane, T < ‖q‖ →
      ‖RestrictedTETotalLinear.fluxForm p ρ χ R b a hρ hχ hi q A A'‖ ≤ K / ‖q‖ ^ 3 := by
  have hS : Admissible R d (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a) :=
    RestrictedTEFiniteBalls.source_admissible p ρ χ R b d a hρ hχ hi (fun a => (a : ℂ)⁻¹ • A) ha ha1 hh
  have hS' : Admissible R d (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A' a) :=
    RestrictedTEFiniteBalls.source_admissible p ρ χ R b d a hρ hχ hi (fun a => (a : ℂ)⁻¹ • A') ha ha1 hh
  set S := RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a with hSdef
  set S' := RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A' a with hSdef'
  obtain ⟨K1, hK1, T1, hT1, hT1R, h1⟩ := RestrictedTECoherentTail.dynamic_tail ((a : ℂ)⁻¹ • A') R hR
  obtain ⟨K4, hK4, T4, hT4, hT4R, h4⟩ := reaction_flux_tail ((a : ℂ)⁻¹ • A') R hR
  set m : ℝ := sourceMass S with hm
  set m' : ℝ := sourceMass S' with hm'
  set Tc2 : ℝ := MaxwellPlaneTail.tailConstant 1 R with hTc2
  set Tc3 : ℝ := PointMaxwellTail.tailConstant 1 1 R with hTc3
  set ze : ℂ := (((b / a) ^ 2 - 1 : ℝ) : ℂ) with hze
  set zm : ℂ := ((((b / a)⁻¹) ^ 2 - 1 : ℝ) : ℂ) with hzm
  refine ⟨K1 * m + Tc2 * m * m' + ‖conj ze‖ * (Tc3 * m * m') + ‖zm‖ * (K4 * m) + ‖zm‖ * (Tc3 * m * m') +
    ‖zm * conj ze‖ * (Tc3 * m * m'), max (max T1 T4) (max 2 (2 * R)), ?_⟩
  intro q hq
  have hqT1 : T1 < ‖q‖ := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hq
  have hqT4 : T4 < ‖q‖ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hq
  have hqR : 2 * R < ‖q‖ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hq
  have hq2 : 2 < ‖q‖ := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hq
  have hxn : ‖MaxwellPlaneTail.planePoint q‖ = ‖q‖ := MaxwellPlaneTail.planePoint_norm q
  have hid : RestrictedTETotalLinear.fluxForm p ρ χ R b a hρ hχ hi q A A' = _ :=
    mixed_identity (b / a) S S' ((a : ℂ)⁻¹ • A) ((a : ℂ)⁻¹ • A') q
  rw [hid]
  have e1 : ‖RestrictedTEPlaneLocal.dynamicMixed S ((a : ℂ)⁻¹ • A') q‖ ≤ (K1 * m) / ‖q‖ ^ 3 :=
    h1 d S hS q hqT1
  have e2 : ‖MaxwellPlaneL1.flux 1 S S' q‖ ≤ (Tc2 * m * m') / ‖q‖ ^ 3 := by
    have := MaxwellPlaneTail.bilinear_flux_tail 1 R hR S S' hS.integrable hS'.integrable hS.support hS'.support
      (MaxwellPlaneTail.planePoint q) (by rw [hxn]; exact hqR) (by rw [hxn]; exact hq2.le) (by rfl)
    rw [hxn] at this
    exact this
  have e3 : ‖SourceParityFlux.electric true 1 S S' q‖ ≤ (Tc3 * m * m') / ‖q‖ ^ 3 := by
    have := SourceParityFlux.electric_tail true 1 R d hR hd one_ne_zero S S' hS hS' q hqR hq2.le
    refine this.trans_eq ?_
    ring
  have e4 : ‖RestrictedTEReactionFlux.flux false S ((a : ℂ)⁻¹ • A') q‖ ≤ (K4 * m) / ‖q‖ ^ 3 :=
    h4 false d S hS q hqT4
  have e5 : ‖SourceParityFlux.magnetic false 1 S S' q‖ ≤ (Tc3 * m * m') / ‖q‖ ^ 3 := by
    have := SourceParityFlux.magnetic_tail false 1 R d hR hd one_ne_zero S S' hS hS' q hqR hq2.le
    refine this.trans_eq ?_
    ring
  have e6 : ‖ParityPlaneBounds.flux false true 1 S S' q‖ ≤ (Tc3 * m * m') / ‖q‖ ^ 3 := by
    have := ParityPlaneBounds.density_bound false true 1 R d S S' hS hS' q (Tc3 / ‖q‖ ^ 3) (fun y z hy hz j m'' => by
      have hf := HerglotzParityPlane.flux_tail false true 1 R hR one_ne_zero (MaxwellPlaneTail.planePoint q) y z
        (by rw [hxn]; exact hqR) (by rw [hxn]; exact hq2.le) (by rfl) hy hz j m''
      rw [hxn] at hf
      exact hf)
    refine this.trans_eq ?_
    ring
  have f3 := scaled_tail (conj ze) _ _ _ e3
  have f4 := scaled_tail zm _ _ _ e4
  have f5 := scaled_tail zm _ _ _ e5
  have f6 := scaled_tail (zm * conj ze) _ _ _ e6
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) ((norm_add_le _ _).trans (add_le_add f3 ((norm_add_le _ _).trans
    (add_le_add f4 ((norm_add_le _ _).trans (add_le_add f5 f6))))))).trans ?_
  refine (add_le_add (add_le_add e1 e2) le_rfl).trans_eq ?_
  ring


/-- The form tail summed over an orthonormal family: uniform on the unit-power sphere of its span. -/
theorem fluxForm_unit_tail {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (p : ℝ → ι → FourierL2.Space) (ρ χ R b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (hR : 0 ≤ R)
    (a d : ℝ) (hd : 0 < d) (ha : 0 < a) (ha1 : a ≤ 1) (hh : ∀ l, d + ρ * a ≤ |p a l 2|)
    (A : κ → Index →₀ ℂ) (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k))) :
    ∃ C T : ℝ, ∀ x ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower x = 1 →
      ∀ q : PlaneInverseCube.Plane, T < ‖q‖ →
        ‖RestrictedTETotalLinear.fluxForm p ρ χ R b a hρ hχ hi q x x‖ ≤ C / ‖q‖ ^ 3 := by
  choose K T hKT using fun i j => pair_tail p ρ χ R b hρ hχ hi hR a d hd ha ha1 hh (A i) (A j)
  refine ⟨∑ i, ∑ j, K i j, ∑ i, ∑ j, |T i j|, ?_⟩
  intro x hx hpow q hq
  obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  have hsum : (∑ k, ‖cf k‖ ^ 2) = 1 := by
    rw [← RestrictedTEPlaneJets.power_comb A horth cf]
    exact hpow
  have hcf : ∀ k, ‖cf k‖ ≤ 1 := by
    intro k
    have h1 : ‖cf k‖ ^ 2 ≤ ∑ k, ‖cf k‖ ^ 2 :=
      Finset.single_le_sum (f := fun k => ‖cf k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    by_contra hne
    push_neg at hne
    nlinarith [norm_nonneg (cf k)]
  have hsq := RestrictedTETotalLinear.fluxForm_sesq p ρ χ R b d a hρ hχ hi hd ha ha1 hh q
  have hexp := RestrictedTETotalLinear.sesq_expand hsq Finset.univ A cf cf
  rw [hexp]
  have hTle (i j : κ) : T i j < ‖q‖ := by
    refine lt_of_le_of_lt ((le_abs_self _).trans ?_) hq
    exact (Finset.single_le_sum (f := fun j => |T i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |T i j|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i))
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖∑ j, (cf i * conj (cf j)) • RestrictedTETotalLinear.fluxForm p ρ χ R b a hρ hχ hi q (A i) (A j)‖
      ≤ ∑ i, ∑ j, K i j / ‖q‖ ^ 3 := by
        refine Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_)))
        rw [norm_smul, norm_mul, Complex.norm_conj]
        have hc : ‖cf i‖ * ‖cf j‖ ≤ 1 := by
          nlinarith [norm_nonneg (cf i), norm_nonneg (cf j), hcf i, hcf j]
        exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (hKT i j q (hTle i j))
    _ = (∑ i, ∑ j, K i j) / ‖q‖ ^ 3 := by simp only [Finset.sum_div]

end ParityTail

/-! ### The concrete parity flux -/

section Concrete

theorem parity_heights {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ h : ℝ)
    (hρ : 0 < ρ) (hρh : ρ < h) :
    ∀ a, 0 < a → a ≤ 1 → ∀ j : ι ⊕ ι, ((h - ρ) + ρ) * a ≤
      |OQ14.RestrictedTEPartnerBalls.partnerCentre (fun l => abovePoint (hpoint r0 y l) (h * a)) j 2| := by
  refine OQ14.RestrictedTEConcreteDoubled.partner_hh_aux (fun a l => abovePoint (hpoint r0 y l) (h * a))
    (h - ρ) ρ ?_
  intro a ha _ l
  beta_reduce
  rw [OQ14.RestrictedTEDipoleConcentration.above_normal, abs_of_pos (mul_pos (by linarith) ha)]
  linarith

theorem parity_gap {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ h : ℝ)
    (hρ : 0 < ρ) (hρh : ρ < h) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    0 < min ((h - ρ) * a) 1 ∧ ∀ j : ι ⊕ ι, min ((h - ρ) * a) 1 + ρ * a ≤
      |OQ14.RestrictedTEPartnerBalls.partnerCentre (fun l => abovePoint (hpoint r0 y l) (h * a)) j 2| := by
  refine ⟨lt_min (mul_pos (by linarith) ha) one_pos, fun j => ?_⟩
  have h1 := parity_heights r0 y ρ h hρ hρh a ha ha1 j
  have h2 := min_le_left ((h - ρ) * a) 1
  nlinarith

/-- Pointwise inverse-cube tail of the parity flux of the concrete doubled device at a fixed scale `a`,
uniform on the unit-power sphere of the span of any orthonormal family of inputs. -/
theorem parityFlux_tail {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hR : 0 ≤ R)
    (hρh : ρ < h) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (A : κ → SymmetricHarmonicJets.Index →₀ ℂ)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k))) :
    ∃ C T : ℝ, ∀ x ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower x = 1 →
      ∀ ξ : PlaneInverseCube.Plane, T < ‖ξ‖ →
        ‖parityFlux r0 y ρ χ h R hρ hχ hi a x ξ‖ ≤ C / ‖ξ‖ ^ 3 := by
  obtain ⟨hd, hh⟩ := parity_gap r0 y ρ h hρ hρh a ha ha1
  exact fluxForm_unit_tail (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
    (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 hρ hχ.le
    (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
    hR a _ hd ha ha1 hh A horth

/-- The parity flux of the concrete doubled device is integrable on the plane at every scale `a ∈ (0,1]`. -/
theorem parityFlux_integrable {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hR : 0 ≤ R)
    (hρh : ρ < h) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (x : SymmetricHarmonicJets.Index →₀ ℂ) :
    Integrable (parityFlux r0 y ρ χ h R hρ hχ hi a x) volume := by
  obtain ⟨hd, hh⟩ := parity_gap r0 y ρ h hρ hρh a ha ha1
  obtain ⟨Ci, Cp, _, _, hwhole⟩ := RestrictedTETotalFlux.whole_bounds x R hR
  have hS := RestrictedTEFiniteBalls.source_admissible
    (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre (fun l => abovePoint (hpoint r0 y l) (h * a)))
    ρ χ R 1 (min ((h - ρ) * a) 1) a hρ hχ.le
    (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
    (fun a => (a : ℂ)⁻¹ • x) ha ha1 hh
  have hdM : min ((h - ρ) * a) 1 ≤ max 2 (2 * R) + R :=
    (min_le_right _ _).trans (by
      have := le_max_left (2 : ℝ) (2 * R)
      linarith)
  exact (hwhole (1 / a) (max 2 (2 * R)) (min ((h - ρ) * a) 1) hd (le_max_left _ _) (le_max_right _ _) hdM _ hS
    ((a : ℂ)⁻¹)).2.1

end Concrete

/-- The parity flux of the concrete doubled device is quadratically homogeneous in the input at the scales
`(q ^ n)⁻¹`, because the total electric and magnetic fields are linear in the input. -/
theorem parityFlux_homogeneous {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R)
    (hρh : ρ < h) (q : ℝ) (hq : 1 < q) :
    HomogeneousFlux (fun n (_ : ℕ) x => parityFlux r0 y ρ χ h R hρ hχ hi (scale q n) x) := by
  have hE : ∀ (n r : ℕ) (z : ℂ) (x : SymmetricHarmonicJets.Index →₀ ℂ) (ξ : PlaneInverseCube.Plane),
      RestrictedTETotalLinear.totalE (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
        (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 hρ hχ.le
        (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
        (scale q n) (z • x) ξ =
      z • RestrictedTETotalLinear.totalE (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
        (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 hρ hχ.le
        (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
        (scale q n) x ξ := by
    intro n r z x ξ
    obtain ⟨hd, hh⟩ := parity_gap r0 y ρ h hρ hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n)
    exact (RestrictedTETotalLinear.totalEMap (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
      (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 _ (scale q n) hρ hχ.le
      (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
      hd (scale_pos hq n) (scale_le_one hq.le n) hh ξ).map_smul z x
  have hH : ∀ (n r : ℕ) (z : ℂ) (x : SymmetricHarmonicJets.Index →₀ ℂ) (ξ : PlaneInverseCube.Plane),
      RestrictedTETotalLinear.totalH (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
        (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 hρ hχ.le
        (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
        (scale q n) (z • x) ξ =
      z • RestrictedTETotalLinear.totalH (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
        (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 hρ hχ.le
        (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
        (scale q n) x ξ := by
    intro n r z x ξ
    obtain ⟨hd, hh⟩ := parity_gap r0 y ρ h hρ hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n)
    exact (RestrictedTETotalLinear.totalHMap (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
      (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 _ (scale q n) hρ hχ.le
      (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
      hd (scale_pos hq n) (scale_le_one hq.le n) hh ξ).map_smul z x
  exact homogeneous_of_linear
    (fun n _ x ξ => RestrictedTETotalLinear.totalE (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
        (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 hρ hχ.le
        (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
        (scale q n) x ξ)
    (fun n _ x ξ => RestrictedTETotalLinear.totalH (fun a => OQ14.RestrictedTEPartnerBalls.partnerCentre
        (fun l => abovePoint (hpoint r0 y l) (h * a))) ρ χ R 1 hρ hχ.le
        (OQ14.RestrictedTEConcreteDoubled.partner_hi_aux (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ R hi)
        (scale q n) x ξ)
    hE hH

/-- `L1Interface` for the concrete doubled device, reduced to the three estimates the field work must deliver for
the actual flux `Fact`: a.e. measurability; `L1` convergence to the parity flux on every disk, uniformly on the
unit-power sphere of every orthonormal span; and an inverse-cube pointwise majorant for large shell index.  The
parity-side integrability and tail majorant are proved here. -/
theorem L1Interface_of_actual_estimates {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hR : 0 ≤ R)
    (hρh : ρ < h) (q : ℝ) (hq : 1 < q)
    (Fact : ℕ → ℕ → (SymmetricHarmonicJets.Index →₀ ℂ) → PlaneInverseCube.Plane → ℂ)
    (hmeas : ∀ n r x, AEStronglyMeasurable (Fact n r x) volume)
    (hcompact : ∀ (N : ℕ) (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) → ∀ n : ℕ, ∀ ρ0 : ℝ, 0 < ρ0 → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ r : ℕ in atTop, ∀ x ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower x = 1 →
          IntegrableOn (fun ξ => Fact n r x ξ - parityFlux r0 y ρ χ h R hρ hχ hi (scale q n) x ξ)
            (closedBall 0 ρ0) volume ∧
          ∫ ξ in closedBall 0 ρ0, ‖Fact n r x ξ - parityFlux r0 y ρ χ h R hρ hχ hi (scale q n) x ξ‖ ≤ ε)
    (htail : ∀ (N : ℕ) (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) → ∀ n : ℕ, ∃ (C ρ1 : ℝ) (r1 : ℕ),
        ∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower x = 1 →
          ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ → ‖Fact n r x ξ‖ ≤ C / ‖ξ‖ ^ 3) :
    L1Interface r0 y ρ χ h R hρ hχ hi q Fact := by
  refine L1Interface_of_compact_and_tails r0 y ρ χ h R hρ hχ hi q Fact hmeas
    (fun n x => parityFlux_integrable r0 y ρ χ h R hρ hχ hi hR hρh (scale q n) (scale_pos hq n)
      (scale_le_one hq.le n) x) hcompact ?_
  intro N A horth n
  obtain ⟨CF, ρF, r1, hF⟩ := htail N A horth n
  obtain ⟨CG, TG, hG⟩ := parityFlux_tail r0 y ρ χ h R hρ hχ hi hR hρh (scale q n) (scale_pos hq n)
    (scale_le_one hq.le n) A horth
  refine ⟨max CF CG, max ρF (TG + 1), r1, ?_, ?_⟩
  · intro r hr x hx hp ξ hξ
    exact (hF r hr x hx hp ξ ((le_max_left _ _).trans hξ)).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  · intro x hx hp ξ hξ
    have hTG : TG + 1 ≤ ‖ξ‖ := (le_max_right _ _).trans hξ
    exact (hG x hx hp ξ (by linarith)).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))

/-- Consistency check of the three field estimates: the parity flux itself, used as the "actual" flux, satisfies
all three hypotheses of `L1Interface_of_actual_estimates` (so they are not contradictory), and hence the interface. -/
theorem L1Interface_parity_self {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hR : 0 ≤ R)
    (hρh : ρ < h) (q : ℝ) (hq : 1 < q) :
    L1Interface r0 y ρ χ h R hρ hχ hi q (fun n (_ : ℕ) x => parityFlux r0 y ρ χ h R hρ hχ hi (scale q n) x) := by
  refine L1Interface_of_actual_estimates r0 y ρ χ h R hρ hχ hi hR hρh q hq _ ?_ ?_ ?_
  · intro n r x
    exact (parityFlux_integrable r0 y ρ χ h R hρ hχ hi hR hρh (scale q n) (scale_pos hq n)
      (scale_le_one hq.le n) x).aestronglyMeasurable
  · intro N A horth n ρ0 hρ0 ε hε
    refine Eventually.of_forall (fun r x _ _ => ?_)
    simp only [sub_self, norm_zero]
    refine ⟨integrableOn_zero, ?_⟩
    simp only [integral_zero]
    exact hε.le
  · intro N A horth n
    obtain ⟨C, T, hT⟩ := parityFlux_tail r0 y ρ χ h R hρ hχ hi hR hρh (scale q n) (scale_pos hq n)
      (scale_le_one hq.le n) A horth
    exact ⟨C, T + 1, 0, fun r _ x hx hp ξ hξ => hT x hx hp ξ (by linarith)⟩

end OQ14.RestrictedTEL1Assembly
#print axioms OQ14.RestrictedTEL1Assembly.tail_set_eq
#print axioms OQ14.RestrictedTEL1Assembly.integrable_of_ball_and_tail
#print axioms OQ14.RestrictedTEL1Assembly.integral_norm_le_ball_add_tail
#print axioms OQ14.RestrictedTEL1Assembly.l1_of_compact_and_tails
#print axioms OQ14.RestrictedTEL1Assembly.L1Interface_of_compact_and_tails
#print axioms OQ14.RestrictedTEL1Assembly.homogeneous_of_linear
#print axioms OQ14.RestrictedTEL1Assembly.mixed_identity
#print axioms OQ14.RestrictedTEL1Assembly.reaction_flux_tail
#print axioms OQ14.RestrictedTEL1Assembly.scaled_tail
#print axioms OQ14.RestrictedTEL1Assembly.pair_tail
#print axioms OQ14.RestrictedTEL1Assembly.fluxForm_unit_tail
#print axioms OQ14.RestrictedTEL1Assembly.parity_heights
#print axioms OQ14.RestrictedTEL1Assembly.parity_gap
#print axioms OQ14.RestrictedTEL1Assembly.parityFlux_tail
#print axioms OQ14.RestrictedTEL1Assembly.parityFlux_integrable
#print axioms OQ14.RestrictedTEL1Assembly.parityFlux_homogeneous
#print axioms OQ14.RestrictedTEL1Assembly.L1Interface_of_actual_estimates
#print axioms OQ14.RestrictedTEL1Assembly.L1Interface_parity_self
