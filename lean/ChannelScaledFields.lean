import AngularPower
import RestrictedTEAmplitude
import SphereTangentialPower
import RegularTEIncoming
import MaxwellFarField

/-! Scaled far fields of the complete field: pairing limits on the sphere.

For the complete field `E = E_in + E_out + E_sc` outside the support radius the far expansion of the sphere
flux uses six scaled families on the unit sphere: the electric parts and the tangential magnetic traces
`n x H` of the incoming Hankel part (scale `exp (i r) r`), of the outgoing Hankel part of the incident finite TE
field and of the scattered field (scale `factor 1 r = r exp (- i r)`).  Each family is `Good`: eventually
continuous in the direction, uniformly bounded, and pointwise convergent.  For `Good` families the sphere
pairing integrals converge by dominated convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ChannelScaledFields
open Filter MeasureTheory Metric Topology OQ14.Maxwell OQ14.DebyeRadialTrace
abbrev Sphere := OQ14.AngularPower.Sphere
abbrev Idx := SymmetricHarmonicJets.Index

/-- A scaled family on the unit sphere converging to a limit field. -/
structure Good (U : ℝ → Sphere → Vector) (U0 : Sphere → Vector) : Prop where
  cont : ∀ᶠ r : ℝ in atTop, Continuous (U r)
  bound : ∃ B : ℝ, ∀ᶠ r : ℝ in atTop, ∀ (n : Sphere) (i : Fin 3), ‖U r n i‖ ≤ B
  lim : ∀ n : Sphere, Tendsto (fun r => U r n) atTop (𝓝 (U0 n))

theorem Good.add {U V : ℝ → Sphere → Vector} {U0 V0 : Sphere → Vector} (hU : Good U U0) (hV : Good V V0) :
    Good (fun r n => U r n + V r n) (fun n => U0 n + V0 n) where
  cont := by
    filter_upwards [hU.cont, hV.cont] with r h1 h2
    exact h1.add h2
  bound := by
    obtain ⟨B1, h1⟩ := hU.bound
    obtain ⟨B2, h2⟩ := hV.bound
    refine ⟨B1 + B2, ?_⟩
    filter_upwards [h1, h2] with r a b n i
    exact (norm_add_le _ _).trans (add_le_add (a n i) (b n i))
  lim := fun n => (hU.lim n).add (hV.lim n)

theorem Good.congr {U U' : ℝ → Sphere → Vector} {U0 : Sphere → Vector} (hU : Good U U0)
    (h : ∀ᶠ r : ℝ in atTop, ∀ n, U' r n = U r n) : Good U' U0 where
  cont := by
    filter_upwards [hU.cont, h] with r h1 h2
    have : U' r = U r := funext (h2)
    rw [this]
    exact h1
  bound := by
    obtain ⟨B, hB⟩ := hU.bound
    refine ⟨B, ?_⟩
    filter_upwards [hB, h] with r a b n i
    rw [b n]
    exact a n i
  lim := fun n => (hU.lim n).congr' (by
    filter_upwards [h] with r hr
    exact (hr n).symm)

theorem Good.congr_lim {U : ℝ → Sphere → Vector} {U0 U1 : Sphere → Vector} (hU : Good U U0) (h : U0 = U1) :
    Good U U1 := h ▸ hU

/-- The sesquilinear pairing used for the radial flux in tangential form. -/
def pair (u t : Vector) : ℂ := dot u (conjugate t)

theorem pair_continuous : Continuous (fun p : Vector × Vector => pair p.1 p.2) := by
  have hc (i : Fin 3) : Continuous (fun p : Vector × Vector => (starRingEnd ℂ) (p.2 i)) :=
    Complex.continuous_conj.comp ((continuous_apply i).comp continuous_snd)
  have hu (i : Fin 3) : Continuous (fun p : Vector × Vector => p.1 i) :=
    (continuous_apply i).comp continuous_fst
  unfold pair dot conjugate
  fun_prop

theorem pair_norm_le (u t : Vector) (B : ℝ) (hu : ∀ i, ‖u i‖ ≤ B) (ht : ∀ i, ‖t i‖ ≤ B) :
    ‖pair u t‖ ≤ 3 * B ^ 2 := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hu 0)
  have h (i : Fin 3) : ‖u i * (starRingEnd ℂ) (t i)‖ ≤ B ^ 2 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖u i‖ * ‖t i‖ ≤ B * B := mul_le_mul (hu i) (ht i) (norm_nonneg _) hB
      _ = B ^ 2 := by ring
  unfold pair dot conjugate
  calc _ ≤ ‖u 0 * (starRingEnd ℂ) (t 0)‖ + ‖u 1 * (starRingEnd ℂ) (t 1)‖ + ‖u 2 * (starRingEnd ℂ) (t 2)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ B ^ 2 + B ^ 2 + B ^ 2 := add_le_add (add_le_add (h 0) (h 1)) (h 2)
    _ = 3 * B ^ 2 := by ring

theorem pairing_integrable {U T : ℝ → Sphere → Vector} {U0 T0 : Sphere → Vector} (hU : Good U U0)
    (hT : Good T T0) :
    ∀ᶠ r : ℝ in atTop, Integrable (fun n => pair (U r n) (T r n)) OQ14.AngularPower.angularMeasure := by
  filter_upwards [hU.cont, hT.cont] with r a b
  exact (pair_continuous.comp (a.prodMk b)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Dominated convergence of the sphere pairing integrals of `Good` families. -/
theorem pairing_limit {U T : ℝ → Sphere → Vector} {U0 T0 : Sphere → Vector} (hU : Good U U0)
    (hT : Good T T0) :
    Tendsto (fun r => ∫ n, pair (U r n) (T r n) ∂OQ14.AngularPower.angularMeasure) atTop
      (𝓝 (∫ n, pair (U0 n) (T0 n) ∂OQ14.AngularPower.angularMeasure)) := by
  obtain ⟨B1, h1⟩ := hU.bound
  obtain ⟨B2, h2⟩ := hT.bound
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => 3 * (max B1 B2) ^ 2)
  · filter_upwards [hU.cont, hT.cont] with r a b
    exact (pair_continuous.comp (a.prodMk b)).aestronglyMeasurable
  · filter_upwards [h1, h2] with r a b
    exact Eventually.of_forall (fun n => pair_norm_le _ _ (max B1 B2)
      (fun i => (a n i).trans (le_max_left _ _)) (fun i => (b n i).trans (le_max_right _ _)))
  · exact integrable_const _
  · exact Eventually.of_forall (fun n =>
      (pair_continuous.tendsto (U0 n, T0 n)).comp ((hU.lim n).prodMk_nhds (hT.lim n)))

/-- A finite combination of continuous angular fields with convergent coefficients is `Good`. -/
theorem good_sum {κ : Type*} (s : Finset κ) (α : κ → ℝ → ℂ) (α0 : κ → ℂ)
    (hα : ∀ i, Tendsto (α i) atTop (𝓝 (α0 i))) (τ : κ → Sphere → Vector) (hτ : ∀ i, Continuous (τ i)) :
    Good (fun r n => ∑ i ∈ s, α i r • τ i n) (fun n => ∑ i ∈ s, α0 i • τ i n) where
  cont := Eventually.of_forall (fun r => continuous_finset_sum _ (fun i _ => continuous_const.smul (hτ i)))
  bound := by
    have hB : ∀ i, ∃ B : ℝ, ∀ (n : Sphere) (j : Fin 3), ‖τ i n j‖ ≤ B := by
      intro i
      obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (f := τ i) (hτ i).continuousOn
      exact ⟨B, fun n j => (norm_le_pi_norm (τ i n) j).trans (hB n (Set.mem_univ n))⟩
    choose B hB using hB
    refine ⟨∑ i ∈ s, (‖α0 i‖ + 1) * B i, ?_⟩
    have hev : ∀ᶠ r : ℝ in atTop, ∀ i ∈ s, ‖α i r‖ ≤ ‖α0 i‖ + 1 := by
      rw [Filter.eventually_all_finset]
      intro i _
      filter_upwards [(hα i).eventually (Metric.closedBall_mem_nhds (α0 i) one_pos)] with r hr
      rw [dist_eq_norm] at hr
      calc ‖α i r‖ = ‖(α i r - α0 i) + α0 i‖ := by rw [sub_add_cancel]
        _ ≤ ‖α i r - α0 i‖ + ‖α0 i‖ := norm_add_le _ _
        _ ≤ ‖α0 i‖ + 1 := by linarith
    filter_upwards [hev] with r hr n j
    have hs : (∑ i ∈ s, α i r • τ i n) j = ∑ i ∈ s, α i r * τ i n j := by
      simp [Finset.sum_apply]
    rw [hs]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => ?_))
    rw [norm_mul]
    exact mul_le_mul (hr i hi) (hB i n j) (norm_nonneg _) (by positivity)
  lim := fun n => tendsto_finset_sum _ (fun i _ => (hα i).smul_const (τ i n))

/-- The position vector of a unit direction is continuous in the direction. -/
theorem position_continuous : Continuous (fun n : Sphere => position (n : Space)) := by
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp
    continuous_subtype_val)

theorem position_norm_le (n : Sphere) (i : Fin 3) : ‖position (n : Space) i‖ ≤ 1 := by
  have h := PiLp.norm_apply_le (n : Space) i
  rw [OQ14.AngularPower.sphere_norm n] at h
  simpa [position] using h

theorem cross_continuous {u v : Sphere → Vector} (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun n => crossProduct (u n) (v n)) := by
  have hu' (j : Fin 3) : Continuous (fun n => u n j) := (continuous_apply j).comp hu
  have hv' (j : Fin 3) : Continuous (fun n => v n j) := (continuous_apply j).comp hv
  apply continuous_pi
  intro i
  fin_cases i <;> simp [cross_apply] <;> fun_prop

theorem cross_norm_le (u v : Vector) (C : ℝ) (hu : ∀ j, ‖u j‖ ≤ 1) (hv : ∀ j, ‖v j‖ ≤ C) (i : Fin 3) :
    ‖crossProduct u v i‖ ≤ 2 * C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hv 0)
  have h (a b : Fin 3) : ‖u a * v b‖ ≤ C := by
    rw [norm_mul]
    calc ‖u a‖ * ‖v b‖ ≤ 1 * C := mul_le_mul (hu a) (hv b) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  fin_cases i <;> simp [cross_apply] <;>
    exact (norm_sub_le _ _).trans (by linarith [h 1 2, h 2 1, h 2 0, h 0 2, h 0 1, h 1 0])

/-- For a unit direction `n` and a transverse vector `F`, `n x (n x F) = - F`. -/
theorem cross_cross_neg (n : Sphere) (F : Vector) (hF : dot (position (n : Space)) F = 0) :
    crossProduct (position (n : Space)) (crossProduct (position (n : Space)) F) = -F := by
  have hn : ‖(n : Space)‖ = 1 := OQ14.AngularPower.sphere_norm n
  have hn0 : (n : Space) ≠ 0 := by intro h; simp [h] at hn
  have hd : MaxwellRadiation.direction (n : Space) = position (n : Space) := by
    ext i
    simp [MaxwellRadiation.direction, GreenKernel.unitCoordinate, position, hn]
  have hN : dot (position (n : Space)) (position (n : Space)) = 1 := by
    rw [← hd]
    exact MaxwellRadiation.direction_dot _ hn0
  unfold dot at hF hN
  ext i
  fin_cases i
  · simp [cross_apply]
    linear_combination (position (n : Space) 0) * hF - (F 0) * hN
  · simp [cross_apply]
    linear_combination (position (n : Space) 1) * hF - (F 1) * hN
  · simp [cross_apply]
    linear_combination (position (n : Space) 2) * hF - (F 2) * hN


/-! ### The incident finite TE field: incoming and outgoing Hankel parts -/

/-- The angular vector field `angularToroidal` of the polynomial of the index `q`. -/
def tau (q : Idx) (n : Sphere) : Vector := angularToroidal (RestrictedTEIncoming.polynomial q) (n : Space)

theorem tau_continuous (q : Idx) : Continuous (tau q) :=
  (HarmonicRadiationGeometry.angularToroidal_continuous (RestrictedTEIncoming.polynomial q)).comp
    continuous_subtype_val

theorem poly_homogeneous (q : Idx) : (RestrictedTEIncoming.polynomial q).IsHomogeneous q.val.1 :=
  EvenHarmonicProjection.homogeneous _ _ q.property.1

theorem poly_harmonic (q : Idx) : HarmonicPolynomial.formalLaplacian (RestrictedTEIncoming.polynomial q) = 0 :=
  EvenHarmonicProjection.harmonic _ _ q.property.2

/-- The incoming (`b = true`) or outgoing (`b = false`) Hankel part of the incident finite TE electric field. -/
def partE (A : Idx →₀ ℂ) (b : Bool) : Field := fun x j =>
  ∑ q ∈ A.support, RestrictedTEIncoming.coefficient A q *
    RegularTEIncoming.electric q.val.1 b (RestrictedTEIncoming.polynomial q) x j

/-- The magnetic counterpart of `partE`. -/
def partH (A : Idx →₀ ℂ) (b : Bool) : Field := fun x j =>
  ∑ q ∈ A.support, RestrictedTEIncoming.coefficient A q *
    RegularTEIncoming.magnetic q.val.1 b (RestrictedTEIncoming.polynomial q) x j

theorem partE_true (A : Idx →₀ ℂ) : RestrictedTEIncoming.incomingElectric A = partE A true := rfl
theorem partE_false (A : Idx →₀ ℂ) : RestrictedTEIncoming.outgoingElectric A = partE A false := rfl
theorem partH_true (A : Idx →₀ ℂ) : RestrictedTEIncoming.incomingMagnetic A = partH A true := rfl
theorem partH_false (A : Idx →₀ ℂ) : RestrictedTEIncoming.outgoingMagnetic A = partH A false := rfl

theorem partE_ray (A : Idx →₀ ℂ) (b : Bool) (n : Sphere) (r : ℝ) (hr : 0 < r) :
    (RegularTEIncoming.phase b r * (r : ℂ)) • partE A b (r • (n : Space)) =
      ∑ q ∈ A.support, (RestrictedTEIncoming.coefficient A q *
        (RegularTEIncoming.phase b r * RegularTEIncoming.radial q.val.1 b r / 2)) • tau q n := by
  ext j
  simp only [partE, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [RegularTEIncoming.electric_ray q.val.1 b (RestrictedTEIncoming.polynomial q) (poly_homogeneous q) n r hr]
  simp only [tau, Pi.smul_apply, smul_eq_mul]
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  field_simp
  ring

theorem partH_ray (A : Idx →₀ ℂ) (b : Bool) (n : Sphere) (r : ℝ) (hr : 0 < r) :
    (RegularTEIncoming.phase b r * (r : ℂ)) • crossProduct (position (n : Space)) (partH A b (r • (n : Space))) =
      ∑ q ∈ A.support, (RestrictedTEIncoming.coefficient A q *
        (Complex.I * (RegularTEIncoming.phase b r * RegularTEIncoming.radialD q.val.1 b r) / 2)) • tau q n := by
  have hH : partH A b (r • (n : Space)) = ∑ q ∈ A.support, RestrictedTEIncoming.coefficient A q •
      RegularTEIncoming.magnetic q.val.1 b (RestrictedTEIncoming.polynomial q) (r • (n : Space)) := by
    ext j
    simp [partH, Finset.sum_apply]
  rw [hH, map_sum, Finset.smul_sum]
  ext j
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul, RegularTEIncoming.magnetic_tangent_ray q.val.1 b (RestrictedTEIncoming.polynomial q)
    (poly_homogeneous q) (poly_harmonic q) n r hr]
  simp only [tau, Pi.smul_apply, smul_eq_mul]
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  field_simp
  ring

/-- The electric amplitude of the Hankel part `b` of the incident field. -/
def aE (A : Idx →₀ ℂ) (b : Bool) (n : Sphere) : Vector :=
  ∑ q ∈ A.support, (RestrictedTEIncoming.coefficient A q * (RegularTEIncoming.coefficient q.val.1 b / 2)) • tau q n

/-- The tangential magnetic trace amplitude of the Hankel part `b` of the incident field. -/
def aT (A : Idx →₀ ℂ) (b : Bool) (n : Sphere) : Vector :=
  ∑ q ∈ A.support, (RestrictedTEIncoming.coefficient A q *
    (Complex.I * (RegularTEIncoming.coefficient q.val.1 b * (if b then -Complex.I else Complex.I)) / 2)) • tau q n

theorem good_partE (A : Idx →₀ ℂ) (b : Bool) :
    Good (fun r n => (RegularTEIncoming.phase b r * (r : ℂ)) • partE A b (r • (n : Space))) (aE A b) := by
  have h := good_sum A.support
    (fun q r => RestrictedTEIncoming.coefficient A q *
      (RegularTEIncoming.phase b r * RegularTEIncoming.radial q.val.1 b r / 2))
    (fun q => RestrictedTEIncoming.coefficient A q * (RegularTEIncoming.coefficient q.val.1 b / 2))
    (fun q => ((RegularTEIncoming.scaled_radial_limit q.val.1 b).div_const 2).const_mul _) tau tau_continuous
  refine h.congr ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr n
  exact partE_ray A b n r hr

theorem good_partH (A : Idx →₀ ℂ) (b : Bool) :
    Good (fun r n => (RegularTEIncoming.phase b r * (r : ℂ)) •
      crossProduct (position (n : Space)) (partH A b (r • (n : Space)))) (aT A b) := by
  have h := good_sum A.support
    (fun q r => RestrictedTEIncoming.coefficient A q *
      (Complex.I * (RegularTEIncoming.phase b r * RegularTEIncoming.radialD q.val.1 b r) / 2))
    (fun q => RestrictedTEIncoming.coefficient A q *
      (Complex.I * (RegularTEIncoming.coefficient q.val.1 b * (if b then -Complex.I else Complex.I)) / 2))
    (fun q => (((RegularTEIncoming.scaled_radialD_limit q.val.1 b).const_mul Complex.I).div_const 2).const_mul _)
    tau tau_continuous
  refine h.congr ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr n
  exact partH_ray A b n r hr

theorem aT_true (A : Idx →₀ ℂ) : aT A true = aE A true := by
  funext n
  unfold aT aE
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  simp only [if_true]
  have : Complex.I * (RegularTEIncoming.coefficient q.val.1 true * -Complex.I) =
      RegularTEIncoming.coefficient q.val.1 true := by
    calc _ = RegularTEIncoming.coefficient q.val.1 true * (-(Complex.I * Complex.I)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [this]

theorem aT_false (A : Idx →₀ ℂ) : aT A false = fun n => -aE A false n := by
  funext n
  unfold aT aE
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have : Complex.I * (RegularTEIncoming.coefficient q.val.1 false * Complex.I) =
      -RegularTEIncoming.coefficient q.val.1 false := by
    calc _ = RegularTEIncoming.coefficient q.val.1 false * (Complex.I * Complex.I) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  simp only [Bool.false_eq_true, if_false]
  rw [this, ← neg_smul]
  congr 1
  ring

/-! ### The scattered field of a compactly supported integrable source -/

/-- Scaled scattered electric field. -/
def Usc (ρ : Fin 3 → Space → ℂ) (r : ℝ) (n : Sphere) : Vector :=
  MaxwellFarField.factor 1 r • ExteriorContinuity.electric 1 ρ (r • (n : Space))

/-- Scaled tangential magnetic trace of the scattered field. -/
def Tsc (ρ : Fin 3 → Space → ℂ) (r : ℝ) (n : Sphere) : Vector :=
  crossProduct (position (n : Space)) (MaxwellFarField.factor 1 r • MagneticResponse.magnetic 1 ρ (r • (n : Space)))

theorem good_Usc (R : ℝ) (hR : 0 ≤ R) (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) :
    Good (Usc ρ) (fun n => MaxwellFarField.electricAmplitude 1 ρ (n : Space)) where
  cont := by
    filter_upwards [eventually_gt_atTop R] with r hr
    exact continuous_const.smul (OQ14.AngularPower.actual_fields_sphere_continuous 1 R r hR hr ρ hρ hc).1
  bound := by
    obtain ⟨C, _, hC⟩ := OQ14.AngularPower.actual_fields_uniform_bound 1 R hR ρ hρ hc
    refine ⟨C, ?_⟩
    filter_upwards [eventually_gt_atTop (max (2 * R) 2)] with r hr n i
    have := (hC r hr (n : Space) (OQ14.AngularPower.sphere_norm n) i).1
    simpa [Usc] using this
  lim := fun n => MaxwellFarField.electric_far_vector_limit 1 R hR ρ hρ hc (n : Space)
    (OQ14.AngularPower.sphere_norm n)

theorem Fsc_transverse (ρ : Fin 3 → Space → ℂ) (n : Sphere) :
    dot (position (n : Space)) (MaxwellFarField.electricAmplitude 1 ρ (n : Space)) = 0 := by
  have hn : ‖(n : Space)‖ = 1 := OQ14.AngularPower.sphere_norm n
  have hd : MaxwellRadiation.direction (n : Space) = position (n : Space) := by
    ext i
    simp [MaxwellRadiation.direction, GreenKernel.unitCoordinate, position, hn]
  rw [← hd]
  exact MaxwellFarField.amplitude_transverse 1 ρ (n : Space) hn

theorem cross_magAmp (ρ : Fin 3 → Space → ℂ) (n : Sphere) :
    crossProduct (position (n : Space)) (MaxwellFarField.magneticAmplitude 1 ρ (n : Space)) =
      -MaxwellFarField.electricAmplitude 1 ρ (n : Space) := by
  have hn : ‖(n : Space)‖ = 1 := OQ14.AngularPower.sphere_norm n
  have hd : MaxwellRadiation.direction (n : Space) = position (n : Space) := by
    ext i
    simp [MaxwellRadiation.direction, GreenKernel.unitCoordinate, position, hn]
  rw [← MaxwellFarField.amplitude_tangential_relation, hd]
  exact cross_cross_neg n _ (Fsc_transverse ρ n)

theorem good_Tsc (R : ℝ) (hR : 0 ≤ R) (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) :
    Good (Tsc ρ) (fun n => -MaxwellFarField.electricAmplitude 1 ρ (n : Space)) where
  cont := by
    filter_upwards [eventually_gt_atTop R] with r hr
    exact cross_continuous position_continuous
      (continuous_const.smul (OQ14.AngularPower.actual_fields_sphere_continuous 1 R r hR hr ρ hρ hc).2)
  bound := by
    obtain ⟨C, _, hC⟩ := OQ14.AngularPower.actual_fields_uniform_bound 1 R hR ρ hρ hc
    refine ⟨2 * C, ?_⟩
    filter_upwards [eventually_gt_atTop (max (2 * R) 2)] with r hr n i
    exact cross_norm_le _ _ C (position_norm_le n) (fun j => by
      simpa using (hC r hr (n : Space) (OQ14.AngularPower.sphere_norm n) j).2) i
  lim := fun n => by
    have h := ((crossProduct (position (n : Space))).continuous_of_finiteDimensional.tendsto _).comp
      (MaxwellFarField.magnetic_far_vector_limit 1 R hR ρ hρ hc (n : Space) (OQ14.AngularPower.sphere_norm n))
    rw [cross_magAmp] at h
    exact h

end OQ14.ChannelScaledFields
#print axioms OQ14.ChannelScaledFields.Good.add
#print axioms OQ14.ChannelScaledFields.Good.congr
#print axioms OQ14.ChannelScaledFields.Good.congr_lim
#print axioms OQ14.ChannelScaledFields.pair_continuous
#print axioms OQ14.ChannelScaledFields.pair_norm_le
#print axioms OQ14.ChannelScaledFields.pairing_integrable
#print axioms OQ14.ChannelScaledFields.pairing_limit
#print axioms OQ14.ChannelScaledFields.good_sum
#print axioms OQ14.ChannelScaledFields.position_continuous
#print axioms OQ14.ChannelScaledFields.position_norm_le
#print axioms OQ14.ChannelScaledFields.cross_continuous
#print axioms OQ14.ChannelScaledFields.cross_norm_le
#print axioms OQ14.ChannelScaledFields.cross_cross_neg
#print axioms OQ14.ChannelScaledFields.tau_continuous
#print axioms OQ14.ChannelScaledFields.poly_homogeneous
#print axioms OQ14.ChannelScaledFields.poly_harmonic
#print axioms OQ14.ChannelScaledFields.partE_true
#print axioms OQ14.ChannelScaledFields.partE_false
#print axioms OQ14.ChannelScaledFields.partH_true
#print axioms OQ14.ChannelScaledFields.partH_false
#print axioms OQ14.ChannelScaledFields.partE_ray
#print axioms OQ14.ChannelScaledFields.partH_ray
#print axioms OQ14.ChannelScaledFields.good_partE
#print axioms OQ14.ChannelScaledFields.good_partH
#print axioms OQ14.ChannelScaledFields.aT_true
#print axioms OQ14.ChannelScaledFields.aT_false
#print axioms OQ14.ChannelScaledFields.good_Usc
#print axioms OQ14.ChannelScaledFields.Fsc_transverse
#print axioms OQ14.ChannelScaledFields.cross_magAmp
#print axioms OQ14.ChannelScaledFields.good_Tsc
