import SourceRadiatedFlux
import SourceRadiatedMagnetic
import SourceRadiatedSeries

/-! The annulus identification of the radiated field of the paired device with the generalized layered
mode series, the export of the decomposition of that series, and its measurability and linearity.

The electric field and the magnetic field of the shell polarization driven by the shell datum of the
inclusion source, added to the free fields of the inclusion source, equal the electric and the magnetic
components of the all-degree series `genElectric`, `genMagnetic` almost everywhere on the whole region
`{radius s < ‖x‖}` (shell annulus and exterior).  The proof is geometry free: the pairing of the shell field
with a smooth test function is a bounded linear functional of the shell vector (a uniform bound of the
translated Green pairing), the shell solution series converges in the material Hilbert space, the mode
fields are identified almost everywhere mode by mode, and the pairings of the absolutely summable pointwise
series pass to the limit by dominated convergence; a locally integrable function whose pairings against all
test functions vanish is zero almost everywhere.  The decomposition of the series outside the inner radius is
exported with constants depending only on the mass bound and the parameters; the moments, hence the series, are
linear in the inclusion source; and the series are almost everywhere strongly measurable on the plane. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.SourceRadiatedAnnulus
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution
  OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open scoped Topology

/-! ### A uniform bound for the translated scalar pairing -/

/-- The pairing of the outgoing Green kernel with the translates of a compactly supported test function
is bounded uniformly for translations in a fixed ball. -/
theorem scalarPair_translate_bound (k : ℝ) (g : Test) (Y : ℝ) :
    ∃ C : ℝ, ∀ y : Space, ‖y‖ ≤ Y → ‖scalarPair k (translate y g)‖ ≤ C := by
  obtain ⟨Cg, hCg⟩ : ∃ C, ∀ x, ‖g.val x‖ ≤ C :=
    g.val.continuous.bounded_above_of_compact_support g.property
  obtain ⟨ρ0, hρ0⟩ := g.property.isCompact.isBounded.subset_closedBall (0 : Space)
  have hzero : ∀ x : Space, ρ0 < ‖x‖ → g.val x = 0 := by
    intro x hx
    by_contra hne
    have hx' : x ∈ tsupport (g.val : Space → ℂ) := subset_tsupport _ hne
    have := hρ0 hx'
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  set C0 : ℝ := max Cg 0 with hC0
  have hint : Integrable (Set.indicator (closedBall (0 : Space) (Y + ρ0))
      (fun x => C0 * ‖OQ14.GreenKernel.phi k x‖)) := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact ((KernelIntegrability.phi_integrable_ball k (Y + ρ0)).norm.const_mul C0)
  refine ⟨∫ x, Set.indicator (closedBall (0 : Space) (Y + ρ0))
      (fun x => C0 * ‖OQ14.GreenKernel.phi k x‖) x, fun y hy => ?_⟩
  unfold scalarPair
  refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ closedBall (0 : Space) (Y + ρ0)
  · rw [Set.indicator_of_mem hx, norm_mul]
    have h1 : ‖(translate y g).val x‖ ≤ C0 := (hCg (x + y)).trans (le_max_left _ _)
    calc ‖OQ14.GreenKernel.phi k x‖ * ‖(translate y g).val x‖ ≤ ‖OQ14.GreenKernel.phi k x‖ * C0 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = C0 * ‖OQ14.GreenKernel.phi k x‖ := by ring
  · rw [Set.indicator_of_not_mem hx]
    have hx' : Y + ρ0 < ‖x‖ := by
      rw [mem_closedBall, dist_zero_right, not_le] at hx
      exact hx
    have : (translate y g).val x = 0 := by
      change g.val (x + y) = 0
      apply hzero
      have := norm_sub_norm_le x (-y)
      rw [sub_neg_eq_add, norm_neg] at this
      linarith
    rw [this]
    simp

/-! ### Bounded functionals for the pairings of the shell polarization fields with test functions -/

abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

/-- The bounded functional `w ↦ ∫ y, source c w j y * g y` for a kernel `g` bounded on the carrier whose
products with the sources are integrable. -/
def srcFunctional (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (g : Space → ℂ) (B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ y ∈ d.carrier, ‖g y‖ ≤ B) (j : Fin 3)
    (hint : ∀ w : VectorL2, Integrable (fun y => DynamicVolume.source c w j y * g y)) :
    VectorL2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun w => ∫ y, DynamicVolume.source c w j y * g y
      map_add' := fun u v => by
        rw [← integral_add (hint u) (hint v)]
        apply integral_congr_ae
        filter_upwards [SourcePairedPlaneIdentification.source_add_ae c u v j] with y hy
        rw [hy]
        ring
      map_smul' := fun z u => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [SourcePairedPlaneIdentification.source_smul_ae c z u j] with y hy
        rw [hy]
        ring }
    (B * (Real.sqrt c.bound * Real.sqrt (volume.real d.carrier)))
    (fun w => by
      have h1 : Integrable (fun y => ‖DynamicVolume.source c w j y‖) :=
        (DynamicVolume.source_integrable c w d.radius d.ballZero j).norm
      have h2 := SourcePairedReactionField.source_mass' c d w j
      calc ‖∫ y, DynamicVolume.source c w j y * g y‖
          ≤ ∫ y, B * ‖DynamicVolume.source c w j y‖ := by
            refine norm_integral_le_of_norm_le (h1.const_mul B) (Eventually.of_forall fun y => ?_)
            by_cases hy : DynamicVolume.source c w j y = 0
            · simp [hy]
            · rw [norm_mul]
              have := hB y (SourcePairedPlaneCompact.source_mem_carrier c d w j y hy)
              calc ‖DynamicVolume.source c w j y‖ * ‖g y‖ ≤ ‖DynamicVolume.source c w j y‖ * B :=
                    mul_le_mul_of_nonneg_left this (norm_nonneg _)
                _ = B * ‖DynamicVolume.source c w j y‖ := by ring
        _ = B * ∫ y, ‖DynamicVolume.source c w j y‖ := integral_const_mul _ _
        _ ≤ B * ((Real.sqrt c.bound * Real.sqrt (volume.real d.carrier)) * ‖w‖) :=
            mul_le_mul_of_nonneg_left h2 hB0
        _ = B * (Real.sqrt c.bound * Real.sqrt (volume.real d.carrier)) * ‖w‖ := by ring)

theorem srcFunctional_apply (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (g : Space → ℂ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ y ∈ d.carrier, ‖g y‖ ≤ B) (j : Fin 3)
    (hint : ∀ w : VectorL2, Integrable (fun y => DynamicVolume.source c w j y * g y)) (w : VectorL2) :
    srcFunctional c d g B hB0 hB j hint w = ∫ y, DynamicVolume.source c w j y * g y := rfl

/-- The pairing of the electric field of the shell polarization with a test function is a bounded
linear functional of the shell vector. -/
theorem exists_electric_functional (cs : Coefficient) (X : ℝ)
    (hcX : ∀ x : Space, x ∉ closedBall (0 : Space) X → cs.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) :
    ∃ Λ : VectorL2 →L[ℂ] ℂ, ∀ u : VectorL2,
      Λ u = ∫ x, MaterialField.scattered cs 1 u x i * f.val x := by
  let dd := SourcePairedPlaneIdentification.ballSupportData cs X hcX
  have hB (j : Fin 3) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y : Space, ‖y‖ ≤ X →
      ‖dyadicPair 1 i j (translate y f)‖ ≤ B := by
    obtain ⟨C1, h1⟩ := scalarPair_translate_bound 1 f X
    obtain ⟨C2, h2⟩ := scalarPair_translate_bound 1 (testPartial j (testPartial i f)) X
    refine ⟨|C1| + |C2|, by positivity, fun y hy => ?_⟩
    unfold dyadicPair
    refine (norm_add_le _ _).trans ?_
    have e : testPartial j (testPartial i (translate y f)) =
        translate y (testPartial j (testPartial i f)) := by
      rw [← translate_partial, ← translate_partial]
    rw [e]
    have a1 : ‖((1 : ℝ) : ℂ)^2 * (if i = j then (1 : ℂ) else 0) * scalarPair 1 (translate y f)‖ ≤
        |C1| := by
      rw [norm_mul]
      have : ‖((1 : ℝ) : ℂ)^2 * (if i = j then (1 : ℂ) else 0)‖ ≤ 1 := by
        split_ifs <;> simp
      calc _ ≤ 1 * ‖scalarPair 1 (translate y f)‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ ≤ |C1| := by rw [one_mul]; exact (h1 y hy).trans (le_abs_self _)
    have a2 := (h2 y hy).trans (le_abs_self C2)
    linarith
  choose B hB0 hBd using hB
  have hint (j : Fin 3) (w : VectorL2) :
      Integrable (fun y => DynamicVolume.source cs w j y * dyadicPair 1 i j (translate y f)) :=
    WaveResponse.dyadic_source_integrable 1 (DynamicVolume.source cs w j)
      (DynamicVolume.source_integrable cs w X hcX j) (MaterialField.source_compact cs w X hcX j) i j f
  refine ⟨∑ j : Fin 3, srcFunctional cs dd (fun y => dyadicPair 1 i j (translate y f)) (B j) (hB0 j)
    (fun y hy => hBd j y (by simpa [dd, SourcePairedPlaneIdentification.ballSupportData] using hy)) j
    (hint j), fun u => ?_⟩
  rw [ContinuousLinearMap.sum_apply]
  simp only [srcFunctional_apply]
  have hpair := FieldResponse.electric_pairing 1 (StaticCoefficient.sqrtMultiplier cs u)
    (DynamicVolume.source cs u) (fun j => DynamicVolume.source_integrable cs u X hcX j)
    (fun j => MaterialField.source_compact cs u X hcX j)
    (StaticNewton.material_source_ae cs u) i f
  exact hpair.symm

/-- The pairing of the magnetic field of the shell polarization with a test function is a bounded
linear functional of the shell vector. -/
theorem exists_magnetic_functional (cs : Coefficient) (X : ℝ)
    (hcX : ∀ x : Space, x ∉ closedBall (0 : Space) X → cs.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) :
    ∃ Ψ : VectorL2 →L[ℂ] ℂ, ∀ u : VectorL2,
      Ψ u = ∫ x, MagneticResponse.magnetic 1 (DynamicVolume.source cs u) x i * f.val x := by
  let dd := SourcePairedPlaneIdentification.ballSupportData cs X hcX
  have hB (h : Test) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y : Space, ‖y‖ ≤ X → ‖scalarPair 1 (translate y h)‖ ≤ B := by
    obtain ⟨C, hC⟩ := scalarPair_translate_bound 1 h X
    exact ⟨|C|, abs_nonneg _, fun y hy => (hC y hy).trans (le_abs_self _)⟩
  obtain ⟨B1, hB10, hB1⟩ := hB (testPartial (WeakCurl.previous i) f)
  obtain ⟨B2, hB20, hB2⟩ := hB (testPartial (WeakCurl.next i) f)
  have hint (j : Fin 3) (h : Test) (w : VectorL2) :
      Integrable (fun y => DynamicVolume.source cs w j y * scalarPair 1 (translate y h)) :=
    translated_source_integrable (OQ14.GreenKernel.phi 1) (DynamicVolume.source cs w j)
      (KernelIntegrability.phi_locallyIntegrable 1) (DynamicVolume.source_integrable cs w X hcX j)
      (MaterialField.source_compact cs w X hcX j) h
  let Φ1 := srcFunctional cs dd (fun y => scalarPair 1 (translate y (testPartial (WeakCurl.previous i) f)))
    B1 hB10 (fun y hy => hB1 y (by simpa [dd, SourcePairedPlaneIdentification.ballSupportData] using hy))
    (WeakCurl.next i) (hint (WeakCurl.next i) _)
  let Φ2 := srcFunctional cs dd (fun y => scalarPair 1 (translate y (testPartial (WeakCurl.next i) f)))
    B2 hB20 (fun y hy => hB2 y (by simpa [dd, SourcePairedPlaneIdentification.ballSupportData] using hy))
    (WeakCurl.previous i) (hint (WeakCurl.previous i) _)
  refine ⟨(-(Complex.I * ((1 : ℝ) : ℂ))) • (Φ1 - Φ2), fun u => ?_⟩
  have hpair := MagneticResponse.magnetic_pairing 1 (DynamicVolume.source cs u)
    (fun j => DynamicVolume.source_integrable cs u X hcX j)
    (fun j => MaterialField.source_compact cs u X hcX j) i f
  rw [hpair]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]
  unfold MagneticResponse.curlPair MagneticResponse.potentialPair
  rfl

/-! ### Almost-everywhere identification from a weakly convergent series -/

/-- **A locally integrable function whose pairings with test functions supported in an open set are the
sums of the pairings of an absolutely summable pointwise series equals the pointwise sum almost
everywhere on that open set.** -/
theorem ae_eq_of_weak_series {α : Type*} [Countable α] (U : Set Space) (hU : IsOpen U)
    (scat Psum : Space → ℂ) (hscat : LocallyIntegrable scat) (τ : α → Space → ℂ) (u : α → ℝ)
    (hu : Summable u) (hmeas : ∀ a, AEStronglyMeasurable (τ a) volume)
    (hbound : ∀ a x, x ∈ U → ‖τ a x‖ ≤ u a) (hsum : ∀ x ∈ U, HasSum (fun a => τ a x) (Psum x))
    (hweak : ∀ f : Test, tsupport (f.val : Space → ℂ) ⊆ U →
      HasSum (fun a => ∫ x, τ a x * f.val x) (∫ x, scat x * f.val x)) :
    ∀ᵐ x ∂(volume : Measure Space), x ∈ U → scat x = Psum x := by
  classical
  have hUm : MeasurableSet U := hU.measurableSet
  have hPbound : ∀ x ∈ U, ‖Psum x‖ ≤ ∑' a, u a := fun x hx =>
    (hsum x hx).norm_le_of_bounded hu.hasSum (fun a => hbound a x hx)
  have hPm : AEStronglyMeasurable Psum (volume.restrict U) := by
    refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset α))
      (f := fun (N : Finset α) x => ∑ a ∈ N, τ a x) (fun N => ?_) ?_
    · exact (Finset.aestronglyMeasurable_sum N (fun a _ => hmeas a)).mono_measure Measure.restrict_le_self
    · exact ae_restrict_of_forall_mem hUm (fun x hx => hsum x hx)
  have hPint : LocallyIntegrableOn Psum U := by
    intro x hx
    refine ⟨U ∩ ball x 1, inter_mem_nhdsWithin _ (ball_mem_nhds x one_pos), ?_⟩
    have hfin : volume (U ∩ ball x 1) ≠ ⊤ :=
      ((measure_mono inter_subset_right).trans_lt (measure_ball_lt_top (x := x) (r := 1))).ne
    refine Integrable.mono' (integrableOn_const (C := ∑' a, u a) |>.mpr (Or.inr hfin.lt_top))
      (hPm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)) ?_
    exact ae_restrict_of_forall_mem (hUm.inter measurableSet_ball) (fun y hy => hPbound y hy.1)
  have hdiff : LocallyIntegrableOn (fun x => scat x - Psum x) U :=
    (hscat.locallyIntegrableOn U).sub hPint
  have hae : ∀ᵐ x ∂(volume : Measure Space), x ∈ U → scat x - Psum x = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hdiff ?_
    intro η hη hc hs
    let φ : Space → ℂ := fun y => (η y : ℂ)
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := Complex.ofRealCLM.contDiff.comp hη
    have hcφ : HasCompactSupport φ := hc.comp_left (g := Complex.ofReal) (by simp)
    have hsφ : tsupport φ ⊆ U := by
      have he : tsupport φ = tsupport η := by
        apply congrArg closure
        ext y
        exact not_congr Complex.ofReal_eq_zero
      rwa [he]
    let f : Test := ⟨FourierL2.compactSmoothSchwartz φ hφ hcφ, hcφ⟩
    have hfv : ∀ y, f.val y = (η y : ℂ) := fun y => rfl
    have hfzero : ∀ x, x ∉ U → f.val x = 0 := fun x hx => by
      have : x ∉ tsupport φ := fun h => hx (hsφ h)
      exact image_eq_zero_of_nmem_tsupport this
    have hfint : Integrable (fun x => f.val x) := f.val.integrable
    -- measurability of the product with the test function
    have hPf : AEStronglyMeasurable (fun x => Psum x * f.val x) volume := by
      refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset α))
        (f := fun (N : Finset α) x => ∑ a ∈ N, τ a x * f.val x) (fun N => ?_) ?_
      · exact Finset.aestronglyMeasurable_sum N
          (fun a _ => (hmeas a).mul f.val.continuous.aestronglyMeasurable)
      · refine Eventually.of_forall fun x => ?_
        by_cases hx : x ∈ U
        · exact (hsum x hx).mul_right (f.val x)
        · simp [hfzero x hx]
    have hPfi : Integrable (fun x => Psum x * f.val x) := by
      refine Integrable.mono' (hfint.norm.const_mul (∑' a, u a)) hPf (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ U
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hPbound x hx) (norm_nonneg _)
      · simp [hfzero x hx]
    have hSi : Integrable (fun x => η x • scat x) :=
      hscat.integrable_smul_left_of_hasCompactSupport hη.continuous hc
    -- dominated convergence for the series of pairings
    have hdc := hasSum_integral_of_dominated_convergence (μ := volume)
      (F := fun a x => τ a x * f.val x) (f := fun x => Psum x * f.val x)
      (fun a x => u a * ‖f.val x‖)
      (fun a => (hmeas a).mul f.val.continuous.aestronglyMeasurable)
      (fun a => Eventually.of_forall fun x => by
        by_cases hx : x ∈ U
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hbound a x hx) (norm_nonneg _)
        · simp [hfzero x hx])
      (Eventually.of_forall fun x => hu.mul_right _)
      (by
        have : (fun x => ∑' a, u a * ‖f.val x‖) = fun x => (∑' a, u a) * ‖f.val x‖ := by
          funext x; exact tsum_mul_right
        rw [this]
        exact hfint.norm.const_mul _)
      (Eventually.of_forall fun x => by
        by_cases hx : x ∈ U
        · exact (hsum x hx).mul_right (f.val x)
        · simp [hfzero x hx]
          exact hasSum_zero)
    have hw := hweak f (by simpa [f] using hsφ)
    have heq : ∫ x, scat x * f.val x = ∫ x, Psum x * f.val x := hw.unique hdc
    have h2 : (fun x => η x • scat x) = fun x => scat x * f.val x := by
      funext x; simp only [Complex.real_smul, hfv]; ring
    have h3 : (fun x => η x • (scat x - Psum x)) = fun x => scat x * f.val x - Psum x * f.val x := by
      funext x; simp only [Complex.real_smul, hfv]; ring
    rw [h3, integral_sub (by rw [← h2]; exact hSi) hPfi, heq, sub_self]
  filter_upwards [hae] with x hx hxU
  exact sub_eq_zero.mp (hx hxU)

/-! ### Helper estimates and the mode-level almost-everywhere identifications -/

theorem decomp_component_le {K1 K2 : ℝ} {F : Vector} {x : Space}
    (h : SourceRemotePlaneBand.Decomp K1 K2 F x) (hx : 1 ≤ ‖x‖) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (i : Fin 3) : ‖F i‖ ≤ K1 + K2 := by
  obtain ⟨Et, Er, hF, -, -, h1, h2⟩ := h
  calc ‖F i‖ ≤ ‖F‖ := norm_le_pi_norm F i
    _ = ‖Et + Er‖ := by rw [hF]
    _ ≤ ‖Et‖ + ‖Er‖ := norm_add_le _ _
    _ ≤ K1 / ‖x‖ + K2 / ‖x‖^2 := add_le_add h1 h2
    _ ≤ K1 + K2 := add_le_add (div_le_self hK1 hx) (div_le_self hK2 (one_le_pow₀ hx))

theorem integrable_mul_test (g : Space → ℂ) (hg : LocallyIntegrable g) (f : Test) :
    Integrable (fun x => g x * f.val x) := by
  have hK : IsCompact (tsupport (f.val : Space → ℂ)) := f.property
  have h1 : IntegrableOn (fun x => g x * f.val x) (tsupport (f.val : Space → ℂ)) :=
    (hg.integrableOn_isCompact hK).mul_continuousOn f.val.continuous.continuousOn hK
  rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport (f.val : Space → ℂ))]
  · exact h1
  · intro x hx
    by_contra hn
    apply hx
    simp [image_eq_zero_of_nmem_tsupport hn]

theorem magnetic_congr (k : ℝ) (ρ τ : Fin 3 → Space → ℂ) (h : ∀ j, ρ j =ᵐ[volume] τ j) :
    MagneticResponse.magnetic k ρ = MagneticResponse.magnetic k τ := by
  funext x i
  unfold MagneticResponse.magnetic
  congr 2
  · unfold KernelConvolution.response
    apply integral_congr_ae
    filter_upwards [h (WeakCurl.previous i)] with y hy
    rw [hy]
  · unfold KernelConvolution.response
    apply integral_congr_ae
    filter_upwards [h (WeakCurl.next i)] with y hy
    rw [hy]

theorem scattered_tm_mode_ae (cs : Coefficient) (d : SourceRadialSystem.Data)
    (hm : ∀ x : Space, (cs.value (VectorFourier.coordinateMap x) : ℂ) = SourceRadialSystem.sigma d ‖x‖ - 1)
    (hdisp : ∀ g ∈ d.gs, g.q^2 = g.σ) (hu : IsUnit (DynamicVolume.volumeBlock cs 1 d.X))
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (a : PositiveIndex) (i : Fin 3) :
    (fun x => MaterialField.scattered cs 1
        (MaterialField.solution cs 1 d.X (SourceModeDatum.tmIncident cs d hc a)) x i) =ᵐ[volume]
      fun x => SourceRegularCorrection.electric (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i := by
  have hw := SourceModeInverse.tm_inverse cs d hm hdisp hu hc a
  have hae := SourceMaterialResponse.scattered_actual cs (SourceDielectricModes.tmData d (a.1+1)) hm hdisp
    (representative (a.1+1) a.2) (representative_homogeneous _ _) (representative_harmonic _ _)
  rw [hw]
  filter_upwards [hae] with z hz
  exact congrFun hz i

theorem scattered_te_mode_ae (cs : Coefficient) (d : SourceRadialSystem.Data)
    (hm : ∀ x : Space, (cs.value (VectorFourier.coordinateMap x) : ℂ) = SourceRadialSystem.sigma d ‖x‖ - 1)
    (hdisp : ∀ g ∈ d.gs, g.q^2 = g.σ) (hu : IsUnit (DynamicVolume.volumeBlock cs 1 d.X))
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (a : PositiveIndex) (i : Fin 3) :
    (fun x => MaterialField.scattered cs 1
        (MaterialField.solution cs 1 d.X (SourceModeDatum.teIncident cs d hc a)) x i) =ᵐ[volume]
      fun x => SourceTECorrection.electric (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i := by
  have hw := SourceModeInverse.te_inverse cs d hm hdisp hu hc a
  have hmu (z : Space) : (cs.value (VectorFourier.coordinateMap z) : ℂ) =
      SourceGeneralMaxwell.mu (SourceDielectricModes.teData d (a.1+1)) ‖z‖ - 1 := by
    rw [SourceDielectricModes.te_mu d hdisp, hm]
  have hae := SourceTEMaterialResponse.scattered_actual cs (SourceDielectricModes.teData d (a.1+1)) hmu
    (SourceDielectricModes.te_sigma d _)
    (representative (a.1+1) a.2) (representative_homogeneous _ _) (representative_harmonic _ _)
  rw [hw]
  filter_upwards [hae] with z hz
  exact congrFun hz i

theorem magnetic_tm_mode_ae (cs : Coefficient) (d : SourceRadialSystem.Data)
    (hm : ∀ x : Space, (cs.value (VectorFourier.coordinateMap x) : ℂ) = SourceRadialSystem.sigma d ‖x‖ - 1)
    (hdisp : ∀ g ∈ d.gs, g.q^2 = g.σ) (hu : IsUnit (DynamicVolume.volumeBlock cs 1 d.X))
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (a : PositiveIndex) (i : Fin 3) :
    (fun x => MagneticResponse.magnetic 1 (DynamicVolume.source cs
        (MaterialField.solution cs 1 d.X (SourceModeDatum.tmIncident cs d hc a))) x i) =ᵐ[volume]
      fun x => SourceRegularCorrection.magnetic (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i := by
  have hsrc : ∀ j, DynamicVolume.source cs
      (MaterialField.solution cs 1 d.X (SourceModeDatum.tmIncident cs d hc a)) j =ᵐ[volume]
      SourceRegularCorrection.polarization (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) j := fun j => SourceModeInverse.tm_source cs d hm hdisp hu hc a j
  rw [magnetic_congr 1 _ _ hsrc]
  have hrep := (SourceVolumeRepresentation.actual_response (SourceDielectricModes.tmData d (a.1+1)) hdisp
    (representative (a.1+1) a.2) (representative_homogeneous _ _) (representative_harmonic _ _)).2
  filter_upwards [hrep] with z hz
  exact (congrFun hz i).symm

theorem magnetic_te_mode_ae (cs : Coefficient) (d : SourceRadialSystem.Data)
    (hm : ∀ x : Space, (cs.value (VectorFourier.coordinateMap x) : ℂ) = SourceRadialSystem.sigma d ‖x‖ - 1)
    (hdisp : ∀ g ∈ d.gs, g.q^2 = g.σ) (hu : IsUnit (DynamicVolume.volumeBlock cs 1 d.X))
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (a : PositiveIndex) (i : Fin 3) :
    (fun x => MagneticResponse.magnetic 1 (DynamicVolume.source cs
        (MaterialField.solution cs 1 d.X (SourceModeDatum.teIncident cs d hc a))) x i) =ᵐ[volume]
      fun x => SourceTECorrection.magnetic (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i := by
  have hsrc : ∀ j, DynamicVolume.source cs
      (MaterialField.solution cs 1 d.X (SourceModeDatum.teIncident cs d hc a)) j =ᵐ[volume]
      SourceTECorrection.polarization (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) j := fun j => SourceModeInverse.te_source cs d hm hdisp hu hc a j
  rw [magnetic_congr 1 _ _ hsrc]
  have hrep := (SourceTEVolumeRepresentation.actual_response (SourceDielectricModes.teData d (a.1+1))
    (SourceDielectricModes.te_sigma d _) (representative (a.1+1) a.2) (representative_homogeneous _ _)
    (representative_harmonic _ _)).2
  filter_upwards [hrep] with z hz
  exact (congrFun hz i).symm

/-! ### Algebra and constants for the annulus identification -/

theorem one_lt_radius (s : ℕ) : 1 < RadialPhaseLimit.radius s := by
  unfold RadialPhaseLimit.radius
  have h := Real.two_le_pi
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  nlinarith

theorem Kc_nonneg (q : ℝ) (hq : 0 < q) (hq1 : 1 ≤ q) (n : ℕ) (b B s0 M : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hBs : B < s0) (hs0 : 0 < s0) (hM : 0 ≤ M) (i : SourceRadiatedFlux.ModeIdx) :
    0 ≤ SourceRadiatedFlux.Kc BarrierDegreeDecomp.mK1 q hq n b B s0 M i ∧
      0 ≤ SourceRadiatedFlux.Kc BarrierDegreeDecomp.mK2 q hq n b B s0 M i ∧
      0 ≤ SourceRadiatedFlux.Kc BarrierDegreeDecomp.mL1 q hq n b B s0 M i ∧
      0 ≤ SourceRadiatedFlux.Kc BarrierDegreeDecomp.mL2 q hq n b B s0 M i := by
  have hr := SourceRadiatedFlux.momentRat_nonneg b B s0 M hb hB hBs hs0 hM (SourceRadiatedFlux.idxOf i)
  have hσ := SourceRadiatedFlux.innerScale_pos s0 hs0 (SourceRadiatedFlux.degFam i)
  have hR1 := BarrierDegreeDecomp.R1pair_pos q hq n (SourceRadiatedFlux.innerScale s0 (SourceRadiatedFlux.degFam i))
  have hn := BarrierDegreeDecomp.mode_constants_nonneg (SourceRadiatedFlux.tmFlag i) q
    (BarrierDegreeDecomp.Wpair q hq n) (SourceRadiatedFlux.innerScale s0 (SourceRadiatedFlux.degFam i))
    (BarrierDegreeDecomp.R1pair q hq n (SourceRadiatedFlux.innerScale s0 (SourceRadiatedFlux.degFam i)))
    hq1 hσ.le hR1 (SourceRadiatedFlux.degFam i)
  exact ⟨mul_nonneg hr hn.1, mul_nonneg hr hn.2.1, mul_nonneg hr hn.2.2.1, mul_nonneg hr hn.2.2.2⟩

/-- The hypotheses on the paired shell used by the modal identifications. -/
theorem shell_hyps (q : ℝ) (hq : 1 ≤ q) (n s : ℕ) :
    (∀ z : Space, (((OQ14.SourcePairedInclusion.shell q hq n s).value
      (VectorFourier.coordinateMap z) : ℝ) : ℂ) =
      SourceRadialSystem.sigma (OQ14.SourcePairedInclusion.data q hq n s) ‖z‖ - 1) ∧
    (∀ g ∈ (OQ14.SourcePairedInclusion.data q hq n s).gs, g.q^2 = g.σ) ∧
    IsUnit (DynamicVolume.volumeBlock (OQ14.SourcePairedInclusion.shell q hq n s) 1
      (OQ14.SourcePairedInclusion.data q hq n s).X) ∧
    (∀ z : Space, z ∉ closedBall (0 : Space) (OQ14.SourcePairedInclusion.data q hq n s).X →
      (OQ14.SourcePairedInclusion.shell q hq n s).value (VectorFourier.coordinateMap z) = 0) ∧
    (∀ z : Space, ‖z‖ ≤ (OQ14.SourcePairedInclusion.data q hq n s).R →
      (OQ14.SourcePairedInclusion.shell q hq n s).value (VectorFourier.coordinateMap z) = 0) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine ⟨fun z => ?_, OQ14.SourcePairedGeometry.physical_dispersion q hq0 n s,
    OQ14.SourcePairedInclusion.shell_isUnit q hq n s,
    fun z hz => OQ14.SourcePairedInclusion.shell_support q hq n s z hz,
    fun z hz => OQ14.SourcePairedInclusion.shell_inner q hq n s z hz⟩
  exact SourceMaterialCoefficient.value_complex (OQ14.SourcePairedGeometry.physicalData q hq0 n s) (q^2)
    (by nlinarith) (OQ14.SourcePairedGeometry.physical_material_bounds q hq0 hq n s) z

theorem magnetic_shell_locallyIntegrable (cs : Coefficient) (X : ℝ)
    (hcX : ∀ x : Space, x ∉ closedBall (0 : Space) X → cs.value (VectorFourier.coordinateMap x) = 0)
    (w : VectorL2) (i : Fin 3) :
    LocallyIntegrable (fun x => MagneticResponse.magnetic 1 (DynamicVolume.source cs w) x i) :=
  MagneticLocal.magnetic_locallyIntegrable 1 X (StaticCoefficient.sqrtMultiplier cs w)
    (DynamicVolume.source cs w) (fun j => DynamicVolume.source_integrable cs w X hcX j)
    (fun j y hy => DynamicVolume.source_zero cs w X hcX j y hy) (StaticNewton.material_source_ae cs w) i

theorem tauE_eq (d : SourceRadialSystem.Data) (a : PositiveIndex) (x : Space) (hx : x ≠ 0) (i : Fin 3)
    (m1 m2 : ℂ) :
    m1 * SourceRegularCorrection.electric (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i +
      m2 * SourceTECorrection.electric (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i =
    (m1 * SourceUnclippedMaxwell.electric (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i +
      m2 * SourceGeneralMaxwell.teElectric (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i) -
    (m1 * SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data (a.1+1))
        (representative (a.1+1) a.2) x i +
      m2 * SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data (a.1+1))
        (representative (a.1+1) a.2) x i) := by
  have e1 := SourceRadiatedSeries.tm_total_eq d a x hx i
  have e2 := SourceRadiatedSeries.te_total_eq d a x hx i
  linear_combination m1 * e1 + m2 * e2

theorem tauH_eq (d : SourceRadialSystem.Data) (a : PositiveIndex) (x : Space) (hx : x ≠ 0) (i : Fin 3)
    (m1 m2 : ℂ) :
    m1 * SourceRegularCorrection.magnetic (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i +
      m2 * SourceTECorrection.magnetic (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i =
    (m1 * SourceUnclippedMaxwell.magnetic (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i +
      m2 * SourceGeneralMaxwell.teMagnetic (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i) -
    (m1 * SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data (a.1+1))
        (representative (a.1+1) a.2) x i +
      m2 * (-SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data (a.1+1))
        (representative (a.1+1) a.2) x i)) := by
  have e1 := SourceRadiatedMagnetic.tm_total_mag_eq d a x hx i
  have e2 := SourceRadiatedMagnetic.te_total_mag_eq d a x hx i
  linear_combination m1 * e1 + m2 * e2

/-! ### The annulus identification of the electric field -/

/-- The electric shell term of degree `a.1+1`: the moments times the actual regular corrections
(layered minus vacuum) of the shell modes. -/
def shellTermE (d : SourceRadialSystem.Data) (ρ : Fin 3 → Space → ℂ) (i : Fin 3) (a : PositiveIndex)
    (x : Space) : ℂ :=
  SourceRadiatedSeries.tmMoment a ρ * SourceRegularCorrection.electric
      (SourceDielectricModes.tmData d (a.1+1)) (representative (a.1+1) a.2) x i +
    SourceRadiatedSeries.teMoment a ρ * SourceTECorrection.electric
      (SourceDielectricModes.teData d (a.1+1)) (representative (a.1+1) a.2) x i

/-- The magnetic shell term of degree `a.1+1`. -/
def shellTermH (d : SourceRadialSystem.Data) (ρ : Fin 3 → Space → ℂ) (i : Fin 3) (a : PositiveIndex)
    (x : Space) : ℂ :=
  SourceRadiatedSeries.tmMoment a ρ * SourceRegularCorrection.magnetic
      (SourceDielectricModes.tmData d (a.1+1)) (representative (a.1+1) a.2) x i +
    SourceRadiatedSeries.teMoment a ρ * SourceTECorrection.magnetic
      (SourceDielectricModes.teData d (a.1+1)) (representative (a.1+1) a.2) x i

/-- The dominating sequence of the shell terms. -/
def termBound (K1 K2 : SourceRadiatedFlux.ModeIdx → ℝ) (c b T : ℝ) (a : PositiveIndex) : ℝ :=
  (K1 (Sum.inl a) + K2 (Sum.inl a)) + (K1 (Sum.inr a) + K2 (Sum.inr a)) +
    OutgoingGeometricTail.majorant b T a * c

theorem termBound_summable (K1 K2 : SourceRadiatedFlux.ModeIdx → ℝ) (hK1 : Summable K1)
    (hK2 : Summable K2) (c b T : ℝ) (hb : 0 ≤ b) : Summable (termBound K1 K2 c b T) := by
  unfold termBound
  exact (((hK1.comp_injective Sum.inl_injective).add (hK2.comp_injective Sum.inl_injective)).add
    ((hK1.comp_injective Sum.inr_injective).add (hK2.comp_injective Sum.inr_injective))).add
    ((OutgoingGeometricTail.majorant_summable b T hb).mul_right c)

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- **Annulus identification of the electric field of the shell polarization.**  For all large shell
indices, almost everywhere on `{radius s < ‖x‖}` (the shell annulus and the exterior), the `L2` class
`MaterialField.scattered` of the shell polarization driven by `Ss T Si (v s)`, plus the free potential of
the inclusion source, equals the electric component of the all-degree layered mode series
`genElectric`. -/
theorem paired_annulus_electric_ae (q : ℝ) (hq : 1 ≤ q) (n : ℕ)
    (ci : SourceRadiatedSeries.Coefficient) (b B s0 N : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0)
    (hs0 : 0 < s0) (v : ℕ → SourceRadiatedSeries.VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (hN : ∀ s, ‖v s‖ ≤ N) :
    ∀ᶠ s : ℕ in atTop, ∀ᵐ x ∂(volume : Measure Space), RadialPhaseLimit.radius s < ‖x‖ → ∀ i : Fin 3,
      MaterialField.scattered (OQ14.SourcePairedInclusion.shell q hq n s) 1
          (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
            (OQ14.SourcePairedInclusion.data q hq n s).X (StaticCoefficient.sqrtMultiplier
              (OQ14.SourcePairedInclusion.shell q hq n s)
              (ShellInclusionVolume.kernel 1 (OQ14.SourcePairedInclusion.data q hq n s).X
                (StaticCoefficient.sqrtMultiplier ci (v s))))) x i +
        ExteriorContinuity.electric 1 (fun j => DynamicVolume.source ci (v s) j) x i =
      SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q (zero_lt_one.trans_le hq) n)
        SourceRadiatedFlux.tmFlag SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s x i := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  set M : ℝ := 3 * ((Real.sqrt ci.bound * Real.sqrt (volume.real (closedBall (0 : Space) b))) * N)
    with hMdef
  have hmass : ∀ s, SourceRadiatedSeries.mass (fun j => DynamicVolume.source ci (v s) j) ≤ M := fun s =>
    (SourceRadiatedFlux.mass_le_norm ci b hci (v s)).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hN s) (by positivity)) (by norm_num))
  have hM : 0 ≤ M := (SourceRadiatedSeries.mass_nonneg _).trans (hmass 0)
  have hρ : ∀ s j, Integrable (DynamicVolume.source ci (v s) j) volume := fun s j =>
    DynamicVolume.source_integrable ci (v s) b hci j
  have hsupp : ∀ s j y, b < ‖y‖ → DynamicVolume.source ci (v s) j y = 0 := fun s j y hy =>
    DynamicVolume.source_zero ci (v s) b hci j y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy)
  obtain ⟨h1, h2, h3, h4⟩ := SourceRadiatedFlux.Kc_summable q hq0 hq n b B s0 M hb hs0 hM
  set T : ℝ := max 2 (2*(B*AngularExteriorBounds.base)) with hTdef
  have e1 : ∀ᶠ s : ℕ in atTop, max (s1pair q hq0 n s0) (s1pair q hq0 n 1) ≤ s := eventually_ge_atTop _
  have e2 : ∀ᶠ s : ℕ in atTop, max T b < RadialPhaseLimit.radius s :=
    RadialPhaseLimit.radius_tendsto.eventually_gt_atTop _
  filter_upwards [e1, e2] with s hs hsR
  obtain ⟨hm, hdisp, hu, hc, hi⟩ := shell_hyps q hq n s
  have hTR : T < (OQ14.SourcePairedInclusion.data q hq n s).R := (le_max_left T b).trans_lt hsR
  have hbR : b < (OQ14.SourcePairedInclusion.data q hq n s).R := (le_max_right T b).trans_lt hsR
  have hRX : RadialPhaseLimit.radius s ≤ (OQ14.SourcePairedInclusion.data q hq n s).X :=
    OQ14.SourcePairedInclusion.radii_ordered q hq n s
  have hxfacts : ∀ x : Space, RadialPhaseLimit.radius s < ‖x‖ →
      x ≠ 0 ∧ 1 ≤ ‖x‖ ∧ max T b < ‖x‖ := fun x hx =>
    ⟨norm_pos_iff.mp ((RadialPhaseLimit.radius_pos s).trans hx),
      (one_lt_radius s).le.trans hx.le, hsR.trans hx⟩
  have key : ∀ i : Fin 3, ∀ᵐ x ∂(volume : Measure Space), x ∈ {x : Space | RadialPhaseLimit.radius s < ‖x‖} →
      MaterialField.scattered (OQ14.SourcePairedInclusion.shell q hq n s) 1
        (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
          (OQ14.SourcePairedInclusion.data q hq n s).X (StaticCoefficient.sqrtMultiplier
            (OQ14.SourcePairedInclusion.shell q hq n s)
            (ShellInclusionVolume.kernel 1 (OQ14.SourcePairedInclusion.data q hq n s).X
              (StaticCoefficient.sqrtMultiplier ci (v s))))) x i =
      SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q hq0 n)
        SourceRadiatedFlux.tmFlag SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s x i -
      ExteriorContinuity.electric 1 (fun j => DynamicVolume.source ci (v s) j) x i := by
    intro i
    refine ae_eq_of_weak_series (α := PositiveIndex) {x : Space | RadialPhaseLimit.radius s < ‖x‖}
      (isOpen_lt continuous_const continuous_norm) _ _
      (MaterialField.scattered_locallyIntegrable _ 1 _ _ hc i)
      (fun a x => shellTermE (OQ14.SourcePairedInclusion.data q hq n s)
        (fun j => DynamicVolume.source ci (v s) j) i a x)
      (termBound (SourceRadiatedFlux.Kc mK1 q hq0 n b B s0 M) (SourceRadiatedFlux.Kc mK2 q hq0 n b B s0 M)
        (SourceRadiatedSeries.mass (fun j => DynamicVolume.source ci (v s) j)) b T)
      (termBound_summable _ _ h1 h2 _ b T hb) ?_ ?_ ?_ ?_
    · intro a
      exact ((SourceCorrectionLocalBounds.electric_locallyIntegrable _ _ i).aestronglyMeasurable.const_mul
        _).add ((SourceMuBounds.electric_locallyIntegrable _ _ i).aestronglyMeasurable.const_mul _)
    · intro a x hx
      obtain ⟨hx0, hx1, hxT⟩ := hxfacts x hx
      beta_reduce
      unfold shellTermE termBound
      rw [tauE_eq _ a x hx0 i]
      have hEi := (SourceRadiatedFlux.scaled_decomp q hq0 hq n b B s0 M hb hB hscale hBs hs0
        (fun s j => DynamicVolume.source ci (v s) j) hρ hsupp hmass (Sum.inl a) s x hs hx).1
      have hEr := (SourceRadiatedFlux.scaled_decomp q hq0 hq n b B s0 M hb hB hscale hBs hs0
        (fun s j => DynamicVolume.source ci (v s) j) hρ hsupp hmass (Sum.inr a) s x hs hx).1
      have nn1 := Kc_nonneg q hq0 hq n b B s0 M hb hB hBs hs0 hM (Sum.inl a)
      have nn2 := Kc_nonneg q hq0 hq n b B s0 M hb hB hBs hs0 hM (Sum.inr a)
      have c1 := decomp_component_le hEi hx1 nn1.1 nn1.2.1 i
      have c2 := decomp_component_le hEr hx1 nn2.1 nn2.2.1 i
      have hFt := SourceRadiatedMagnetic.Ft_bound b B T hb hB hscale (le_max_left _ _) (le_max_right _ _)
        (fun j => DynamicVolume.source ci (v s) j) (hρ s) (hsupp s) a x ((le_max_left T b).trans hxT.le) i
      unfold SourceRadiatedMagnetic.Ft at hFt
      refine (norm_sub_le _ _).trans ?_
      have hl : ‖(SourceRadiatedSeries.tmMoment a fun j => DynamicVolume.source ci (v s) j) *
          SourceUnclippedMaxwell.electric (SourceDielectricModes.tmData
            (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i +
          (SourceRadiatedSeries.teMoment a fun j => DynamicVolume.source ci (v s) j) *
          SourceGeneralMaxwell.teElectric (SourceDielectricModes.teData
            (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i‖ ≤
          (SourceRadiatedFlux.Kc mK1 q hq0 n b B s0 M (Sum.inl a) +
            SourceRadiatedFlux.Kc mK2 q hq0 n b B s0 M (Sum.inl a)) +
          (SourceRadiatedFlux.Kc mK1 q hq0 n b B s0 M (Sum.inr a) +
            SourceRadiatedFlux.Kc mK2 q hq0 n b B s0 M (Sum.inr a)) :=
        (norm_add_le _ _).trans (add_le_add c1 c2)
      linarith
    · intro x hx
      obtain ⟨hx0, hx1, hxT⟩ := hxfacts x hx
      have hsumE : Summable (fun k : SourceRadiatedFlux.ModeIdx =>
          SourceRadiatedFlux.coeffFam (fun s j => DynamicVolume.source ci (v s) j) s k •
            OQ14.SourceRemotePlaneBand.modeElectric (SourceRadiatedFlux.tmFlag k) (SourceRadiatedFlux.dataFam q hq0 n k s)
              (SourceRadiatedFlux.polyFam k) x) :=
        (SourceRadiatedFlux.decomp_tsum_gen _ _ _ h1 h2 x hx0 (fun k => (SourceRadiatedFlux.scaled_decomp q hq0 hq n b B s0 M
          hb hB hscale hBs hs0 (fun s j => DynamicVolume.source ci (v s) j) hρ hsupp hmass k s x hs hx).1)).1
      have hA1 := (Pi.summable.mp hsumE i).comp_injective (Sum.inl_injective (α := PositiveIndex)
        (β := PositiveIndex))
      have hA2 := (Pi.summable.mp hsumE i).comp_injective (Sum.inr_injective (α := PositiveIndex)
        (β := PositiveIndex))
      have hlay : HasSum (fun a : PositiveIndex =>
          (SourceRadiatedSeries.tmMoment a fun j => DynamicVolume.source ci (v s) j) *
          SourceUnclippedMaxwell.electric (SourceDielectricModes.tmData
            (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i +
          (SourceRadiatedSeries.teMoment a fun j => DynamicVolume.source ci (v s) j) *
          SourceGeneralMaxwell.teElectric (SourceDielectricModes.teData
            (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i)
          (SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q hq0 n)
            SourceRadiatedFlux.tmFlag SourceRadiatedFlux.polyFam
            (SourceRadiatedFlux.coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s x i) := by
        rw [SourceRadiatedFlux.genElectric_apply _ s x i hsumE]
        exact (hA1.add hA2).hasSum
      have hfree := SourceRadiatedSeries.free_field_series_outside b B T hb hB hscale (le_max_left _ _)
        (le_max_right _ _) (fun j => DynamicVolume.source ci (v s) j) (hρ s) (hsupp s) x hxT i
      have hres := hlay.sub hfree
      convert hres using 1
      funext a
      beta_reduce
      unfold shellTermE
      rw [tauE_eq _ a x hx0 i]
    · intro f hf
      obtain ⟨Λ, hΛ⟩ := exists_electric_functional (OQ14.SourcePairedInclusion.shell q hq n s)
        (OQ14.SourcePairedInclusion.data q hq n s).X hc i f
      have h := (SourceRadiatedSeries.shell_solution_series (OQ14.SourcePairedInclusion.shell q hq n s) ci
        (OQ14.SourcePairedInclusion.data q hq n s) b B T hb hB hscale (le_max_left _ _)
        (le_max_right _ _) hTR hbR hc hi hci (v s)).mapL Λ
      have h2 : HasSum (fun a : PositiveIndex => ∫ x, shellTermE (OQ14.SourcePairedInclusion.data q hq n s)
          (fun j => DynamicVolume.source ci (v s) j) i a x * f.val x)
          (Λ (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
            (OQ14.SourcePairedInclusion.data q hq n s).X (StaticCoefficient.sqrtMultiplier
              (OQ14.SourcePairedInclusion.shell q hq n s)
              (ShellInclusionVolume.kernel 1 (OQ14.SourcePairedInclusion.data q hq n s).X
                (StaticCoefficient.sqrtMultiplier ci (v s)))))) := by
        convert h using 1
        funext a
        simp only [Function.comp_apply, map_add, map_smul, smul_eq_mul]
        rw [hΛ, hΛ]
        have e1 : ∫ x, MaterialField.scattered (OQ14.SourcePairedInclusion.shell q hq n s) 1
            (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
              (OQ14.SourcePairedInclusion.data q hq n s).X
              (SourceModeDatum.tmIncident (OQ14.SourcePairedInclusion.shell q hq n s)
                (OQ14.SourcePairedInclusion.data q hq n s) hc a)) x i * f.val x =
            ∫ x, SourceRegularCorrection.electric (SourceDielectricModes.tmData
              (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i *
              f.val x := by
          apply integral_congr_ae
          filter_upwards [scattered_tm_mode_ae (OQ14.SourcePairedInclusion.shell q hq n s)
            (OQ14.SourcePairedInclusion.data q hq n s) hm hdisp hu hc a i] with z hz
          rw [hz]
        have e2 : ∫ x, MaterialField.scattered (OQ14.SourcePairedInclusion.shell q hq n s) 1
            (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
              (OQ14.SourcePairedInclusion.data q hq n s).X
              (SourceModeDatum.teIncident (OQ14.SourcePairedInclusion.shell q hq n s)
                (OQ14.SourcePairedInclusion.data q hq n s) hc a)) x i * f.val x =
            ∫ x, SourceTECorrection.electric (SourceDielectricModes.teData
              (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i *
              f.val x := by
          apply integral_congr_ae
          filter_upwards [scattered_te_mode_ae (OQ14.SourcePairedInclusion.shell q hq n s)
            (OQ14.SourcePairedInclusion.data q hq n s) hm hdisp hu hc a i] with z hz
          rw [hz]
        rw [e1, e2]
        have i1 := integrable_mul_test _ (SourceCorrectionLocalBounds.electric_locallyIntegrable
          (SourceDielectricModes.tmData (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1))
          (representative (a.1+1) a.2) i) f
        have i2 := integrable_mul_test _ (SourceMuBounds.electric_locallyIntegrable
          (SourceDielectricModes.teData (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1))
          (representative (a.1+1) a.2) i) f
        have hsp : (fun x => shellTermE (OQ14.SourcePairedInclusion.data q hq n s)
            (fun j => DynamicVolume.source ci (v s) j) i a x * f.val x) = fun x =>
            (SourceRadiatedSeries.tmMoment a fun j => DynamicVolume.source ci (v s) j) *
              (SourceRegularCorrection.electric (SourceDielectricModes.tmData
                (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i *
                f.val x) +
            (SourceRadiatedSeries.teMoment a fun j => DynamicVolume.source ci (v s) j) *
              (SourceTECorrection.electric (SourceDielectricModes.teData
                (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i *
                f.val x) := by
          funext x
          unfold shellTermE
          ring
        rw [hsp, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
      rw [hΛ] at h2
      exact h2
  filter_upwards [ae_all_iff.mpr key] with x hx hxU i
  have := hx i hxU
  linear_combination this

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- **Annulus identification of the magnetic field of the shell polarization.**  For all large shell
indices, almost everywhere on `{radius s < ‖x‖}` (the shell annulus and the exterior), the magnetic field
`MagneticResponse.magnetic 1` of the shell polarization driven by `Ss T Si (v s)`, plus the free magnetic
field of the inclusion source, equals the magnetic component of the all-degree layered mode series
`genMagnetic`. -/
theorem paired_annulus_magnetic_ae (q : ℝ) (hq : 1 ≤ q) (n : ℕ)
    (ci : SourceRadiatedSeries.Coefficient) (b B s0 N : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0)
    (hs0 : 0 < s0) (v : ℕ → SourceRadiatedSeries.VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (hN : ∀ s, ‖v s‖ ≤ N) :
    ∀ᶠ s : ℕ in atTop, ∀ᵐ x ∂(volume : Measure Space), RadialPhaseLimit.radius s < ‖x‖ → ∀ i : Fin 3,
      MagneticResponse.magnetic 1 (DynamicVolume.source (OQ14.SourcePairedInclusion.shell q hq n s)
          (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
            (OQ14.SourcePairedInclusion.data q hq n s).X (StaticCoefficient.sqrtMultiplier
              (OQ14.SourcePairedInclusion.shell q hq n s)
              (ShellInclusionVolume.kernel 1 (OQ14.SourcePairedInclusion.data q hq n s).X
                (StaticCoefficient.sqrtMultiplier ci (v s)))))) x i +
        MagneticResponse.magnetic 1 (fun j => DynamicVolume.source ci (v s) j) x i =
      SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q (zero_lt_one.trans_le hq) n)
        SourceRadiatedFlux.tmFlag SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s x i := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  set M : ℝ := 3 * ((Real.sqrt ci.bound * Real.sqrt (volume.real (closedBall (0 : Space) b))) * N)
    with hMdef
  have hmass : ∀ s, SourceRadiatedSeries.mass (fun j => DynamicVolume.source ci (v s) j) ≤ M := fun s =>
    (SourceRadiatedFlux.mass_le_norm ci b hci (v s)).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hN s) (by positivity)) (by norm_num))
  have hM : 0 ≤ M := (SourceRadiatedSeries.mass_nonneg _).trans (hmass 0)
  have hρ : ∀ s j, Integrable (DynamicVolume.source ci (v s) j) volume := fun s j =>
    DynamicVolume.source_integrable ci (v s) b hci j
  have hsupp : ∀ s j y, b < ‖y‖ → DynamicVolume.source ci (v s) j y = 0 := fun s j y hy =>
    DynamicVolume.source_zero ci (v s) b hci j y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy)
  obtain ⟨h1, h2, h3, h4⟩ := SourceRadiatedFlux.Kc_summable q hq0 hq n b B s0 M hb hs0 hM
  set T : ℝ := max 2 (2*(B*AngularExteriorBounds.base)) with hTdef
  have e1 : ∀ᶠ s : ℕ in atTop, max (s1pair q hq0 n s0) (s1pair q hq0 n 1) ≤ s := eventually_ge_atTop _
  have e2 : ∀ᶠ s : ℕ in atTop, max T b < RadialPhaseLimit.radius s :=
    RadialPhaseLimit.radius_tendsto.eventually_gt_atTop _
  filter_upwards [e1, e2] with s hs hsR
  obtain ⟨hm, hdisp, hu, hc, hi⟩ := shell_hyps q hq n s
  have hTR : T < (OQ14.SourcePairedInclusion.data q hq n s).R := (le_max_left T b).trans_lt hsR
  have hbR : b < (OQ14.SourcePairedInclusion.data q hq n s).R := (le_max_right T b).trans_lt hsR
  have hRX : RadialPhaseLimit.radius s ≤ (OQ14.SourcePairedInclusion.data q hq n s).X :=
    OQ14.SourcePairedInclusion.radii_ordered q hq n s
  have hxfacts : ∀ x : Space, RadialPhaseLimit.radius s < ‖x‖ →
      x ≠ 0 ∧ 1 ≤ ‖x‖ ∧ max T b < ‖x‖ := fun x hx =>
    ⟨norm_pos_iff.mp ((RadialPhaseLimit.radius_pos s).trans hx),
      (one_lt_radius s).le.trans hx.le, hsR.trans hx⟩
  have key : ∀ i : Fin 3, ∀ᵐ x ∂(volume : Measure Space), x ∈ {x : Space | RadialPhaseLimit.radius s < ‖x‖} →
      MagneticResponse.magnetic 1 (DynamicVolume.source (OQ14.SourcePairedInclusion.shell q hq n s)
        (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
          (OQ14.SourcePairedInclusion.data q hq n s).X (StaticCoefficient.sqrtMultiplier
            (OQ14.SourcePairedInclusion.shell q hq n s)
            (ShellInclusionVolume.kernel 1 (OQ14.SourcePairedInclusion.data q hq n s).X
              (StaticCoefficient.sqrtMultiplier ci (v s)))))) x i =
      SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q hq0 n)
        SourceRadiatedFlux.tmFlag SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s x i -
      MagneticResponse.magnetic 1 (fun j => DynamicVolume.source ci (v s) j) x i := by
    intro i
    refine ae_eq_of_weak_series (α := PositiveIndex) {x : Space | RadialPhaseLimit.radius s < ‖x‖}
      (isOpen_lt continuous_const continuous_norm) _ _
      (magnetic_shell_locallyIntegrable _ _ hc _ i)
      (fun a x => shellTermH (OQ14.SourcePairedInclusion.data q hq n s)
        (fun j => DynamicVolume.source ci (v s) j) i a x)
      (termBound (SourceRadiatedFlux.Kc mL1 q hq0 n b B s0 M) (SourceRadiatedFlux.Kc mL2 q hq0 n b B s0 M)
        (SourceRadiatedSeries.mass (fun j => DynamicVolume.source ci (v s) j)) b T)
      (termBound_summable _ _ h3 h4 _ b T hb) ?_ ?_ ?_ ?_
    · intro a
      exact ((SourceCorrectionLocalBounds.magnetic_locallyIntegrable _ _ i).aestronglyMeasurable.const_mul
        _).add ((SourceMuBounds.magnetic_locallyIntegrable _ _ i).aestronglyMeasurable.const_mul _)
    · intro a x hx
      obtain ⟨hx0, hx1, hxT⟩ := hxfacts x hx
      beta_reduce
      unfold shellTermH termBound
      rw [tauH_eq _ a x hx0 i]
      have hEi := (SourceRadiatedFlux.scaled_decomp q hq0 hq n b B s0 M hb hB hscale hBs hs0
        (fun s j => DynamicVolume.source ci (v s) j) hρ hsupp hmass (Sum.inl a) s x hs hx).2
      have hEr := (SourceRadiatedFlux.scaled_decomp q hq0 hq n b B s0 M hb hB hscale hBs hs0
        (fun s j => DynamicVolume.source ci (v s) j) hρ hsupp hmass (Sum.inr a) s x hs hx).2
      have nn1 := Kc_nonneg q hq0 hq n b B s0 M hb hB hBs hs0 hM (Sum.inl a)
      have nn2 := Kc_nonneg q hq0 hq n b B s0 M hb hB hBs hs0 hM (Sum.inr a)
      have c1 := decomp_component_le hEi hx1 nn1.2.2.1 nn1.2.2.2 i
      have c2 := decomp_component_le hEr hx1 nn2.2.2.1 nn2.2.2.2 i
      have hFt := SourceRadiatedMagnetic.Gt_bound b B T hb hB hscale (le_max_left _ _) (le_max_right _ _)
        (fun j => DynamicVolume.source ci (v s) j) (hρ s) (hsupp s) a x ((le_max_left T b).trans hxT.le) i
      unfold SourceRadiatedMagnetic.Gt at hFt
      refine (norm_sub_le _ _).trans ?_
      have hl : ‖(SourceRadiatedSeries.tmMoment a fun j => DynamicVolume.source ci (v s) j) *
          SourceUnclippedMaxwell.magnetic (SourceDielectricModes.tmData
            (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i +
          (SourceRadiatedSeries.teMoment a fun j => DynamicVolume.source ci (v s) j) *
          SourceGeneralMaxwell.teMagnetic (SourceDielectricModes.teData
            (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i‖ ≤
          (SourceRadiatedFlux.Kc mL1 q hq0 n b B s0 M (Sum.inl a) +
            SourceRadiatedFlux.Kc mL2 q hq0 n b B s0 M (Sum.inl a)) +
          (SourceRadiatedFlux.Kc mL1 q hq0 n b B s0 M (Sum.inr a) +
            SourceRadiatedFlux.Kc mL2 q hq0 n b B s0 M (Sum.inr a)) :=
        (norm_add_le _ _).trans (add_le_add c1 c2)
      linarith
    · intro x hx
      obtain ⟨hx0, hx1, hxT⟩ := hxfacts x hx
      have hsumE : Summable (fun k : SourceRadiatedFlux.ModeIdx =>
          SourceRadiatedFlux.coeffFam (fun s j => DynamicVolume.source ci (v s) j) s k •
            OQ14.SourceRemotePlaneBand.modeMagnetic (SourceRadiatedFlux.tmFlag k) (SourceRadiatedFlux.dataFam q hq0 n k s)
              (SourceRadiatedFlux.polyFam k) x) :=
        (SourceRadiatedFlux.decomp_tsum_gen _ _ _ h3 h4 x hx0 (fun k => (SourceRadiatedFlux.scaled_decomp q hq0 hq n b B s0 M
          hb hB hscale hBs hs0 (fun s j => DynamicVolume.source ci (v s) j) hρ hsupp hmass k s x hs hx).2)).1
      have hA1 := (Pi.summable.mp hsumE i).comp_injective (Sum.inl_injective (α := PositiveIndex)
        (β := PositiveIndex))
      have hA2 := (Pi.summable.mp hsumE i).comp_injective (Sum.inr_injective (α := PositiveIndex)
        (β := PositiveIndex))
      have hlay : HasSum (fun a : PositiveIndex =>
          (SourceRadiatedSeries.tmMoment a fun j => DynamicVolume.source ci (v s) j) *
          SourceUnclippedMaxwell.magnetic (SourceDielectricModes.tmData
            (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i +
          (SourceRadiatedSeries.teMoment a fun j => DynamicVolume.source ci (v s) j) *
          SourceGeneralMaxwell.teMagnetic (SourceDielectricModes.teData
            (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i)
          (SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q hq0 n)
            SourceRadiatedFlux.tmFlag SourceRadiatedFlux.polyFam
            (SourceRadiatedFlux.coeffFam (fun s j => DynamicVolume.source ci (v s) j)) s x i) := by
        rw [SourceRadiatedFlux.genMagnetic_apply _ s x i hsumE]
        exact (hA1.add hA2).hasSum
      have hfree := SourceRadiatedMagnetic.free_magnetic_series_outside b B T hb hB hscale (le_max_left _ _)
        (le_max_right _ _) (fun j => DynamicVolume.source ci (v s) j) (hρ s) (hsupp s) x hxT i
      have hres := hlay.sub hfree
      convert hres using 1
      funext a
      beta_reduce
      unfold shellTermH
      rw [tauH_eq _ a x hx0 i]
      rfl
    · intro f hf
      obtain ⟨Λ, hΛ⟩ := exists_magnetic_functional (OQ14.SourcePairedInclusion.shell q hq n s)
        (OQ14.SourcePairedInclusion.data q hq n s).X hc i f
      have h := (SourceRadiatedSeries.shell_solution_series (OQ14.SourcePairedInclusion.shell q hq n s) ci
        (OQ14.SourcePairedInclusion.data q hq n s) b B T hb hB hscale (le_max_left _ _)
        (le_max_right _ _) hTR hbR hc hi hci (v s)).mapL Λ
      have h2 : HasSum (fun a : PositiveIndex => ∫ x, shellTermH (OQ14.SourcePairedInclusion.data q hq n s)
          (fun j => DynamicVolume.source ci (v s) j) i a x * f.val x)
          (Λ (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
            (OQ14.SourcePairedInclusion.data q hq n s).X (StaticCoefficient.sqrtMultiplier
              (OQ14.SourcePairedInclusion.shell q hq n s)
              (ShellInclusionVolume.kernel 1 (OQ14.SourcePairedInclusion.data q hq n s).X
                (StaticCoefficient.sqrtMultiplier ci (v s)))))) := by
        convert h using 1
        funext a
        simp only [Function.comp_apply, map_add, map_smul, smul_eq_mul]
        rw [hΛ, hΛ]
        have e1 : ∫ x, MagneticResponse.magnetic 1 (DynamicVolume.source (OQ14.SourcePairedInclusion.shell q hq n s)
            (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
              (OQ14.SourcePairedInclusion.data q hq n s).X
              (SourceModeDatum.tmIncident (OQ14.SourcePairedInclusion.shell q hq n s)
                (OQ14.SourcePairedInclusion.data q hq n s) hc a))) x i * f.val x =
            ∫ x, SourceRegularCorrection.magnetic (SourceDielectricModes.tmData
              (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i *
              f.val x := by
          apply integral_congr_ae
          filter_upwards [magnetic_tm_mode_ae (OQ14.SourcePairedInclusion.shell q hq n s)
            (OQ14.SourcePairedInclusion.data q hq n s) hm hdisp hu hc a i] with z hz
          rw [hz]
        have e2 : ∫ x, MagneticResponse.magnetic 1 (DynamicVolume.source (OQ14.SourcePairedInclusion.shell q hq n s)
            (MaterialField.solution (OQ14.SourcePairedInclusion.shell q hq n s) 1
              (OQ14.SourcePairedInclusion.data q hq n s).X
              (SourceModeDatum.teIncident (OQ14.SourcePairedInclusion.shell q hq n s)
                (OQ14.SourcePairedInclusion.data q hq n s) hc a))) x i * f.val x =
            ∫ x, SourceTECorrection.magnetic (SourceDielectricModes.teData
              (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i *
              f.val x := by
          apply integral_congr_ae
          filter_upwards [magnetic_te_mode_ae (OQ14.SourcePairedInclusion.shell q hq n s)
            (OQ14.SourcePairedInclusion.data q hq n s) hm hdisp hu hc a i] with z hz
          rw [hz]
        rw [e1, e2]
        have i1 := integrable_mul_test _ (SourceCorrectionLocalBounds.magnetic_locallyIntegrable
          (SourceDielectricModes.tmData (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1))
          (representative (a.1+1) a.2) i) f
        have i2 := integrable_mul_test _ (SourceMuBounds.magnetic_locallyIntegrable
          (SourceDielectricModes.teData (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1))
          (representative (a.1+1) a.2) i) f
        have hsp : (fun x => shellTermH (OQ14.SourcePairedInclusion.data q hq n s)
            (fun j => DynamicVolume.source ci (v s) j) i a x * f.val x) = fun x =>
            (SourceRadiatedSeries.tmMoment a fun j => DynamicVolume.source ci (v s) j) *
              (SourceRegularCorrection.magnetic (SourceDielectricModes.tmData
                (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i *
                f.val x) +
            (SourceRadiatedSeries.teMoment a fun j => DynamicVolume.source ci (v s) j) *
              (SourceTECorrection.magnetic (SourceDielectricModes.teData
                (OQ14.SourcePairedInclusion.data q hq n s) (a.1+1)) (representative (a.1+1) a.2) x i *
                f.val x) := by
          funext x
          unfold shellTermH
          ring
        rw [hsp, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
      rw [hΛ] at h2
      exact h2
  filter_upwards [ae_all_iff.mpr key] with x hx hxU i
  have := hx i hxU
  linear_combination this



/-! ### Export of the decomposition of the radiated series -/

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- **The radiated series decomposes at every point outside the inner radius, with constants depending
only on the mass bound and the parameters.**  For a family `ρ k s` of current densities supported in the
ball of radius `b` with `L¹` masses at most `M` (for all parameters `k` and all shell indices `s`), there
are constants `K1 K2 L1 L2 ≥ 0` and a shell index `s1`, independent of `k`, such that for `s ≥ s1` and
`radius s < ‖x‖` the electric series `genElectric` and the magnetic series `genMagnetic` of the moments of
`ρ k s` decompose into a part orthogonal to the position of size `K1/‖x‖` (`L1/‖x‖`) and a radial part of
size `K2/‖x‖²` (`L2/‖x‖²`). -/
theorem radiated_decomp_outside (q : ℝ) (hq : 0 < q) (hq1 : 1 ≤ q) (n : ℕ) (b B s0 M : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0)
    (hs0 : 0 < s0) {κ : Type*} (ρ : κ → ℕ → Fin 3 → Space → ℂ)
    (hρ : ∀ k s j, Integrable (ρ k s j) volume)
    (hsupp : ∀ k s j y, b < ‖y‖ → ρ k s j y = 0)
    (hmass : ∀ k s, SourceRadiatedSeries.mass (ρ k s) ≤ M) :
    ∃ (K1 K2 L1 L2 : ℝ) (s1 : ℕ), 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ L1 ∧ 0 ≤ L2 ∧
      ∀ k, ∀ s ≥ s1, ∀ x : Space, RadialPhaseLimit.radius s < ‖x‖ →
        SourceRemotePlaneBand.Decomp K1 K2
          (SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
            SourceRadiatedFlux.polyFam (SourceRadiatedFlux.coeffFam (ρ k)) s x) x ∧
        SourceRemotePlaneBand.Decomp L1 L2
          (SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
            SourceRadiatedFlux.polyFam (SourceRadiatedFlux.coeffFam (ρ k)) s x) x := by
  set M' : ℝ := max M 0 with hM'
  have hM0 : 0 ≤ M' := le_max_right _ _
  have hmass' : ∀ k s, SourceRadiatedSeries.mass (ρ k s) ≤ M' := fun k s => (hmass k s).trans (le_max_left _ _)
  obtain ⟨h1, h2, h3, h4⟩ := SourceRadiatedFlux.Kc_summable q hq hq1 n b B s0 M' hb hs0 hM0
  have nn (i : SourceRadiatedFlux.ModeIdx) := Kc_nonneg q hq hq1 n b B s0 M' hb hB hBs hs0 hM0 i
  refine ⟨∑' i, SourceRadiatedFlux.Kc mK1 q hq n b B s0 M' i, ∑' i, SourceRadiatedFlux.Kc mK2 q hq n b B s0 M' i,
    ∑' i, SourceRadiatedFlux.Kc mL1 q hq n b B s0 M' i, ∑' i, SourceRadiatedFlux.Kc mL2 q hq n b B s0 M' i,
    max (s1pair q hq n s0) (s1pair q hq n 1), tsum_nonneg fun i => (nn i).1,
    tsum_nonneg fun i => (nn i).2.1, tsum_nonneg fun i => (nn i).2.2.1,
    tsum_nonneg fun i => (nn i).2.2.2, fun k s hs x hx => ?_⟩
  have hx0 : x ≠ 0 := norm_pos_iff.mp ((RadialPhaseLimit.radius_pos s).trans hx)
  exact ⟨(SourceRadiatedFlux.decomp_tsum_gen _ _ _ h1 h2 x hx0 (fun i => (SourceRadiatedFlux.scaled_decomp q hq
      hq1 n b B s0 M' hb hB hscale hBs hs0 (ρ k) (hρ k) (hsupp k) (hmass' k) i s x hs hx).1)).2,
    (SourceRadiatedFlux.decomp_tsum_gen _ _ _ h3 h4 x hx0 (fun i => (SourceRadiatedFlux.scaled_decomp q hq
      hq1 n b B s0 M' hb hB hscale hBs hs0 (ρ k) (hρ k) (hsupp k) (hmass' k) i s x hs hx).2)).2⟩

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- The same for the radiated series of the moments of the inclusion sources `source ci (v k s)` with the
inclusion vectors bounded in norm, `‖v k s‖ ≤ N`; the constants depend only on `N`, `b`, `B`, `s0`, `q`,
`n` and the inclusion coefficient. -/
theorem radiated_decomp_outside_of_norm_bound (q : ℝ) (hq : 0 < q) (hq1 : 1 ≤ q) (n : ℕ)
    (ci : SourceRadiatedSeries.Coefficient) (b B s0 N : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0)
    (hs0 : 0 < s0) {κ : Type*} (v : κ → ℕ → SourceRadiatedSeries.VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (hN : ∀ k s, ‖v k s‖ ≤ N) :
    ∃ (K1 K2 L1 L2 : ℝ) (s1 : ℕ), 0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ L1 ∧ 0 ≤ L2 ∧
      ∀ k, ∀ s ≥ s1, ∀ x : Space, RadialPhaseLimit.radius s < ‖x‖ →
        SourceRemotePlaneBand.Decomp K1 K2
          (SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
            SourceRadiatedFlux.polyFam
            (SourceRadiatedFlux.coeffFam (fun s j => DynamicVolume.source ci (v k s) j)) s x) x ∧
        SourceRemotePlaneBand.Decomp L1 L2
          (SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
            SourceRadiatedFlux.polyFam
            (SourceRadiatedFlux.coeffFam (fun s j => DynamicVolume.source ci (v k s) j)) s x) x :=
  radiated_decomp_outside q hq hq1 n b B s0
    (3 * ((Real.sqrt ci.bound * Real.sqrt (volume.real (closedBall (0 : Space) b))) * N)) hb hB hscale hBs
    hs0 (fun k s j => DynamicVolume.source ci (v k s) j)
    (fun k s j => DynamicVolume.source_integrable ci (v k s) b hci j)
    (fun k s j y hy => DynamicVolume.source_zero ci (v k s) b hci j y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy))
    (fun k s => (SourceRadiatedFlux.mass_le_norm ci b hci (v k s)).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hN k s) (by positivity)) (by norm_num)))

/-! ### Linearity of the radiated series in the inclusion source -/

theorem source_lin (c : Coefficient) (w1 w2 : VectorL2) (α β : ℂ) (j : Fin 3) :
    DynamicVolume.source c (α • w1 + β • w2) j =ᵐ[volume]
      fun y => α * DynamicVolume.source c w1 j y + β * DynamicVolume.source c w2 j y := by
  filter_upwards [SourcePairedPlaneIdentification.source_add_ae c (α • w1) (β • w2) j,
    SourcePairedPlaneIdentification.source_smul_ae c α w1 j,
    SourcePairedPlaneIdentification.source_smul_ae c β w2 j] with y h1 h2 h3
  rw [h1, h2, h3]

theorem moments_linear (ci : Coefficient) (b : ℝ)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (w1 w2 : VectorL2) (α β : ℂ) (a : PositiveIndex) :
    SourceRadiatedSeries.tmMoment a (fun j => DynamicVolume.source ci (α • w1 + β • w2) j) =
        α * SourceRadiatedSeries.tmMoment a (fun j => DynamicVolume.source ci w1 j) +
          β * SourceRadiatedSeries.tmMoment a (fun j => DynamicVolume.source ci w2 j) ∧
      SourceRadiatedSeries.teMoment a (fun j => DynamicVolume.source ci (α • w1 + β • w2) j) =
        α * SourceRadiatedSeries.teMoment a (fun j => DynamicVolume.source ci w1 j) +
          β * SourceRadiatedSeries.teMoment a (fun j => DynamicVolume.source ci w2 j) := by
  have hsupp (w : VectorL2) (j : Fin 3) (y : Space) (hy : b < ‖y‖) : DynamicVolume.source ci w j y = 0 :=
    DynamicVolume.source_zero ci w b hci j y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy)
  have hint (w : VectorL2) (j : Fin 3) := DynamicVolume.source_integrable ci w b hci j
  have key : ∀ (c : Space → Fin 3 → ℂ), (∀ j, Continuous fun y => c y j) →
      ∑ j, ∫ y, c y j * DynamicVolume.source ci (α • w1 + β • w2) j y =
        α * (∑ j, ∫ y, c y j * DynamicVolume.source ci w1 j y) +
          β * (∑ j, ∫ y, c y j * DynamicVolume.source ci w2 j y) := by
    intro c hc
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have i1 := SourceRadiatedSeries.coefficient_mul_integrable (hc j) (hint w1 j) b (hsupp w1 j)
    have i2 := SourceRadiatedSeries.coefficient_mul_integrable (hc j) (hint w2 j) b (hsupp w2 j)
    have hcong : ∫ y, c y j * DynamicVolume.source ci (α • w1 + β • w2) j y =
        ∫ y, (α * (c y j * DynamicVolume.source ci w1 j y) + β * (c y j * DynamicVolume.source ci w2 j y)) := by
      apply integral_congr_ae
      filter_upwards [source_lin ci w1 w2 α β j] with y hy
      rw [hy]
      ring
    rw [hcong, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
  unfold SourceRadiatedSeries.tmMoment SourceRadiatedSeries.teMoment
  exact ⟨key _ (fun j => SourceRadiatedSeries.tmCoefficient_continuous a j),
    key _ (fun j => SourceRadiatedSeries.teCoefficient_continuous a j)⟩

theorem coeffFam_linear (ci : Coefficient) (b : ℝ)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (w1 w2 : VectorL2) (α β : ℂ) (s : ℕ) (k : SourceRadiatedFlux.ModeIdx) :
    SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci (α • w1 + β • w2) j) s k =
      α * SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci w1 j) s k +
        β * SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci w2 j) s k := by
  cases k with
  | inl a => exact (moments_linear ci b hci w1 w2 α β a).1
  | inr a => exact (moments_linear ci b hci w1 w2 α β a).2

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- Summability of the layered mode series of the moments of a single inclusion source, at every point
outside the inner radius, for large shell index. -/
theorem genElectric_summable (q : ℝ) (hq : 0 < q) (hq1 : 1 ≤ q) (n : ℕ)
    (ci : SourceRadiatedSeries.Coefficient) (b B s0 : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0)
    (hs0 : 0 < s0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (w : SourceRadiatedSeries.VectorL2) (s : ℕ)
    (hs : max (s1pair q hq n s0) (s1pair q hq n 1) ≤ s) (x : Space)
    (hx : RadialPhaseLimit.radius s < ‖x‖) :
    Summable (fun k : SourceRadiatedFlux.ModeIdx =>
      SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci w j) s k •
        OQ14.SourceRemotePlaneBand.modeElectric (SourceRadiatedFlux.tmFlag k)
          (SourceRadiatedFlux.dataFam q hq n k s) (SourceRadiatedFlux.polyFam k) x) ∧
    Summable (fun k : SourceRadiatedFlux.ModeIdx =>
      SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci w j) s k •
        OQ14.SourceRemotePlaneBand.modeMagnetic (SourceRadiatedFlux.tmFlag k)
          (SourceRadiatedFlux.dataFam q hq n k s) (SourceRadiatedFlux.polyFam k) x) := by
  set M : ℝ := max (3 * ((Real.sqrt ci.bound * Real.sqrt (volume.real (closedBall (0 : Space) b))) *
    ‖w‖)) 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hmass : ∀ s' : ℕ, SourceRadiatedSeries.mass (fun j => DynamicVolume.source ci w j) ≤ M := fun s' =>
    ((SourceRadiatedFlux.mass_le_norm ci b hci w).trans (le_refl _)).trans (le_max_left _ _)
  obtain ⟨h1, h2, h3, h4⟩ := SourceRadiatedFlux.Kc_summable q hq hq1 n b B s0 M hb hs0 hM
  have hx0 : x ≠ 0 := norm_pos_iff.mp ((RadialPhaseLimit.radius_pos s).trans hx)
  have hρ : ∀ (s' : ℕ) (j : Fin 3), Integrable (DynamicVolume.source ci w j) volume := fun s' j =>
    DynamicVolume.source_integrable ci w b hci j
  have hsupp : ∀ (s' : ℕ) (j : Fin 3) (y : Space), b < ‖y‖ → DynamicVolume.source ci w j y = 0 :=
    fun s' j y hy => DynamicVolume.source_zero ci w b hci j y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy)
  exact ⟨(SourceRadiatedFlux.decomp_tsum_gen _ _ _ h1 h2 x hx0 (fun i =>
      (SourceRadiatedFlux.scaled_decomp q hq hq1 n b B s0 M hb hB hscale hBs hs0
        (fun _ j => DynamicVolume.source ci w j) hρ hsupp hmass i s x hs hx).1)).1,
    (SourceRadiatedFlux.decomp_tsum_gen _ _ _ h3 h4 x hx0 (fun i =>
      (SourceRadiatedFlux.scaled_decomp q hq hq1 n b B s0 M hb hB hscale hBs hs0
        (fun _ j => DynamicVolume.source ci w j) hρ hsupp hmass i s x hs hx).2)).1⟩

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- **Linearity of the radiated series in the inclusion source.**  For `s ≥ s1` and `x` outside the
inner radius, the electric series and the magnetic series of the moments of the source of
`α • w1 + β • w2` are the corresponding combinations of the series of the sources of `w1` and `w2`.  In
particular `x ↦ genElectric (coeffFam (source ci (U x))) s ξ` is `ℂ`-linear for every linear map `U` into
`VectorL2` (for instance the inclusion solution as a function of the incident vector). -/
theorem genSeries_linear_source (q : ℝ) (hq : 0 < q) (hq1 : 1 ≤ q) (n : ℕ)
    (ci : SourceRadiatedSeries.Coefficient) (b B s0 : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0)
    (hs0 : 0 < s0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (s : ℕ) (hs : max (s1pair q hq n s0) (s1pair q hq n 1) ≤ s) (x : Space)
    (hx : RadialPhaseLimit.radius s < ‖x‖) (w1 w2 : SourceRadiatedSeries.VectorL2) (α β : ℂ) :
    SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci (α • w1 + β • w2) j)) s x =
      α • SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci w1 j)) s x +
      β • SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci w2 j)) s x ∧
    SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci (α • w1 + β • w2) j)) s x =
      α • SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci w1 j)) s x +
      β • SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci w2 j)) s x := by
  obtain ⟨e1, m1⟩ := genElectric_summable q hq hq1 n ci b B s0 hb hB hscale hBs hs0 hci w1 s hs x hx
  obtain ⟨e2, m2⟩ := genElectric_summable q hq hq1 n ci b B s0 hb hB hscale hBs hs0 hci w2 s hs x hx
  constructor
  · unfold SourceRadiatedFlux.genElectric
    have h := (e1.hasSum.const_smul α).add (e2.hasSum.const_smul β)
    refine HasSum.tsum_eq ?_
    convert h using 1
    funext k
    rw [coeffFam_linear ci b hci w1 w2 α β s k]
    simp only [add_smul, mul_smul]
  · unfold SourceRadiatedFlux.genMagnetic
    have h := (m1.hasSum.const_smul α).add (m2.hasSum.const_smul β)
    refine HasSum.tsum_eq ?_
    convert h using 1
    funext k
    rw [coeffFam_linear ci b hci w1 w2 α β s k]
    simp only [add_smul, mul_smul]

/-! ### Measurability on the plane -/

theorem sphere_null (T : ℝ) :
    (volume : Measure PlaneInverseCube.Plane) {u : PlaneInverseCube.Plane | ‖u‖ = T} = 0 := by
  have : {u : PlaneInverseCube.Plane | ‖u‖ = T} = sphere 0 T := by
    ext u; simp [mem_sphere_iff_norm]
  rw [this]
  exact Measure.addHaar_sphere volume 0 T

theorem gen_electric_aesm {ι : Type*} [Countable ι] (D : ι → ℕ → SourceRadialSystem.Data) (tm : ι → Bool)
    (P : ι → HarmonicPolynomial.Poly) (hP : ∀ i s, (P i).IsHomogeneous (D i s).l)
    (hDR : ∀ i s, (D i s).R = RadialPhaseLimit.radius s) (c : ℕ → ι → ℂ)
    (K1 K2 : ι → ℝ) (hK1 : Summable K1) (hK2 : Summable K2) (s1 s : ℕ) (hs : s1 ≤ s)
    (hE : ∀ (i : ι) (s : ℕ) (x : Space), s1 ≤ s → RadialPhaseLimit.radius s < ‖x‖ →
      SourceRemotePlaneBand.Decomp (K1 i) (K2 i)
        (c s i • SourceRemotePlaneBand.modeElectric (tm i) (D i s) (P i) x) x) :
    AEStronglyMeasurable (fun u : PlaneInverseCube.Plane =>
      SourceRadiatedFlux.genElectric D tm P c s (MaxwellPlaneTail.planePoint u))
      (volume.restrict {u : PlaneInverseCube.Plane | RadialPhaseLimit.radius s < ‖u‖}) := by
  have hSm : MeasurableSet {u : PlaneInverseCube.Plane | RadialPhaseLimit.radius s < ‖u‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hT : 0 < RadialPhaseLimit.radius s := RadialPhaseLimit.radius_pos s
  have hpt : ∀ u : PlaneInverseCube.Plane, u ∈ {u : PlaneInverseCube.Plane | RadialPhaseLimit.radius s < ‖u‖} →
      MaxwellPlaneTail.planePoint u ≠ 0 ∧ RadialPhaseLimit.radius s < ‖MaxwellPlaneTail.planePoint u‖ := by
    intro u hu
    have hu' : RadialPhaseLimit.radius s < ‖u‖ := hu
    have hn : RadialPhaseLimit.radius s < ‖MaxwellPlaneTail.planePoint u‖ := by
      rw [MaxwellPlaneTail.planePoint_norm]; exact hu'
    exact ⟨norm_pos_iff.mp (hT.trans hn), hn⟩
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun (N : Finset ι) (u : PlaneInverseCube.Plane) => ∑ i ∈ N, c s i •
      SourceRemotePlaneBand.modeElectric (tm i) (D i s) (P i) (MaxwellPlaneTail.planePoint u))
  · intro N
    refine Finset.aestronglyMeasurable_sum N (fun i _ => ?_)
    have h := (SourceRemotePlaneSeries.modeElectric_aesm_outside (tm i) (D i s) (P i)
      (hP i s)).const_smul (c s i)
    rw [hDR i s] at h
    exact h
  · apply ae_restrict_of_forall_mem hSm
    intro u hu
    obtain ⟨hx0, hxR⟩ := hpt u hu
    exact (SourceRadiatedFlux.decomp_tsum_gen _ K1 K2 hK1 hK2 _ hx0
      (fun i => hE i s _ hs hxR)).1.hasSum

theorem gen_magnetic_aesm {ι : Type*} [Countable ι] (D : ι → ℕ → SourceRadialSystem.Data) (tm : ι → Bool)
    (P : ι → HarmonicPolynomial.Poly) (hP : ∀ i s, (P i).IsHomogeneous (D i s).l)
    (hDR : ∀ i s, (D i s).R = RadialPhaseLimit.radius s) (c : ℕ → ι → ℂ)
    (L1 L2 : ι → ℝ) (hL1 : Summable L1) (hL2 : Summable L2) (s1 s : ℕ) (hs : s1 ≤ s)
    (hH : ∀ (i : ι) (s : ℕ) (x : Space), s1 ≤ s → RadialPhaseLimit.radius s < ‖x‖ →
      SourceRemotePlaneBand.Decomp (L1 i) (L2 i)
        (c s i • SourceRemotePlaneBand.modeMagnetic (tm i) (D i s) (P i) x) x) :
    AEStronglyMeasurable (fun u : PlaneInverseCube.Plane =>
      SourceRadiatedFlux.genMagnetic D tm P c s (MaxwellPlaneTail.planePoint u))
      (volume.restrict {u : PlaneInverseCube.Plane | RadialPhaseLimit.radius s < ‖u‖}) := by
  have hSm : MeasurableSet {u : PlaneInverseCube.Plane | RadialPhaseLimit.radius s < ‖u‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hT : 0 < RadialPhaseLimit.radius s := RadialPhaseLimit.radius_pos s
  have hpt : ∀ u : PlaneInverseCube.Plane, u ∈ {u : PlaneInverseCube.Plane | RadialPhaseLimit.radius s < ‖u‖} →
      MaxwellPlaneTail.planePoint u ≠ 0 ∧ RadialPhaseLimit.radius s < ‖MaxwellPlaneTail.planePoint u‖ := by
    intro u hu
    have hu' : RadialPhaseLimit.radius s < ‖u‖ := hu
    have hn : RadialPhaseLimit.radius s < ‖MaxwellPlaneTail.planePoint u‖ := by
      rw [MaxwellPlaneTail.planePoint_norm]; exact hu'
    exact ⟨norm_pos_iff.mp (hT.trans hn), hn⟩
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun (N : Finset ι) (u : PlaneInverseCube.Plane) => ∑ i ∈ N, c s i •
      SourceRemotePlaneBand.modeMagnetic (tm i) (D i s) (P i) (MaxwellPlaneTail.planePoint u))
  · intro N
    refine Finset.aestronglyMeasurable_sum N (fun i _ => ?_)
    have h := (SourceRemotePlaneSeries.modeMagnetic_aesm_outside (tm i) (D i s) (P i)
      (hP i s)).const_smul (c s i)
    rw [hDR i s] at h
    exact h
  · apply ae_restrict_of_forall_mem hSm
    intro u hu
    obtain ⟨hx0, hxR⟩ := hpt u hu
    exact (SourceRadiatedFlux.decomp_tsum_gen _ L1 L2 hL1 hL2 _ hx0
      (fun i => hH i s _ hs hxR)).1.hasSum

/-- The closed region `{radius s ≤ ‖u‖}` differs from the open one by a circle of plane measure zero. -/
theorem aesm_closed_of_open {β : Type*} [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    (f : PlaneInverseCube.Plane → β) (T : ℝ)
    (h : AEStronglyMeasurable f (volume.restrict {u : PlaneInverseCube.Plane | T < ‖u‖})) :
    AEStronglyMeasurable f (volume.restrict {u : PlaneInverseCube.Plane | T ≤ ‖u‖}) := by
  have hsub : {u : PlaneInverseCube.Plane | T ≤ ‖u‖} ⊆
      {u : PlaneInverseCube.Plane | T < ‖u‖} ∪ {u : PlaneInverseCube.Plane | ‖u‖ = T} := by
    intro u hu
    rcases (show T ≤ ‖u‖ from hu).lt_or_eq with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1.symm
  have h0 : (volume : Measure PlaneInverseCube.Plane).restrict
      {u : PlaneInverseCube.Plane | ‖u‖ = T} = 0 := Measure.restrict_eq_zero.mpr (sphere_null T)
  have h2 : AEStronglyMeasurable f (volume.restrict
      ({u : PlaneInverseCube.Plane | T < ‖u‖} ∪ {u : PlaneInverseCube.Plane | ‖u‖ = T})) := by
    exact aestronglyMeasurable_union_iff.mpr ⟨h, by rw [h0]; exact aestronglyMeasurable_zero_measure f⟩
  exact h2.mono_measure (Measure.restrict_mono hsub le_rfl)

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- **Plane measurability of the radiated series.**  For `s ≥ s1`, every component of the electric and of
the magnetic series of the moments of the sources `ρ s`, restricted to the plane section `ξ ↦ planePoint ξ`
over `{radius s ≤ ‖ξ‖}`, is almost everywhere strongly measurable (the circle `‖ξ‖ = radius s` is null in
the plane). -/
theorem radiated_plane_aesm (q : ℝ) (hq : 0 < q) (hq1 : 1 ≤ q) (n : ℕ) (b B s0 M : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0)
    (hs0 : 0 < s0) (ρ : ℕ → Fin 3 → Space → ℂ) (hρ : ∀ s j, Integrable (ρ s j) volume)
    (hsupp : ∀ s j y, b < ‖y‖ → ρ s j y = 0) (hmass : ∀ s, SourceRadiatedSeries.mass (ρ s) ≤ M)
    (s : ℕ) (hs : max (s1pair q hq n s0) (s1pair q hq n 1) ≤ s) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ : PlaneInverseCube.Plane =>
      SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam (SourceRadiatedFlux.coeffFam ρ) s (MaxwellPlaneTail.planePoint ξ) i)
      (volume.restrict {ξ : PlaneInverseCube.Plane | RadialPhaseLimit.radius s ≤ ‖ξ‖}) ∧
    AEStronglyMeasurable (fun ξ : PlaneInverseCube.Plane =>
      SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam (SourceRadiatedFlux.coeffFam ρ) s (MaxwellPlaneTail.planePoint ξ) i)
      (volume.restrict {ξ : PlaneInverseCube.Plane | RadialPhaseLimit.radius s ≤ ‖ξ‖}) := by
  set M' : ℝ := max M 0
  have hM0 : 0 ≤ M' := le_max_right _ _
  have hmass' : ∀ s, SourceRadiatedSeries.mass (ρ s) ≤ M' := fun s => (hmass s).trans (le_max_left _ _)
  obtain ⟨h1, h2, h3, h4⟩ := SourceRadiatedFlux.Kc_summable q hq hq1 n b B s0 M' hb hs0 hM0
  constructor
  · have h := gen_electric_aesm (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
      SourceRadiatedFlux.polyFam (SourceRadiatedFlux.polyFam_hom q hq n) (SourceRadiatedFlux.dataFam_R q hq n)
      (SourceRadiatedFlux.coeffFam ρ) _ _ h1 h2 (max (s1pair q hq n s0) (s1pair q hq n 1)) s hs
      (fun k s x hs hx => (SourceRadiatedFlux.scaled_decomp q hq hq1 n b B s0 M' hb hB hscale hBs hs0 ρ
        hρ hsupp hmass' k s x hs hx).1)
    exact (continuous_apply i).comp_aestronglyMeasurable
      (aesm_closed_of_open _ (RadialPhaseLimit.radius s) h)
  · have h := gen_magnetic_aesm (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
      SourceRadiatedFlux.polyFam (SourceRadiatedFlux.polyFam_hom q hq n) (SourceRadiatedFlux.dataFam_R q hq n)
      (SourceRadiatedFlux.coeffFam ρ) _ _ h3 h4 (max (s1pair q hq n s0) (s1pair q hq n 1)) s hs
      (fun k s x hs hx => (SourceRadiatedFlux.scaled_decomp q hq hq1 n b B s0 M' hb hB hscale hBs hs0 ρ
        hρ hsupp hmass' k s x hs hx).2)
    exact (continuous_apply i).comp_aestronglyMeasurable
      (aesm_closed_of_open _ (RadialPhaseLimit.radius s) h)

open OQ14.BarrierDegreeDecomp OQ14.BarrierDegreeFluxConstants in
/-- **Linearity along a linear family of inclusion vectors.**  For a linear map `U` from a complex vector
space into `VectorL2` (the inclusion solution as a function of the incident vector, say), the radiated
electric and magnetic series of the sources `source ci (U e)` are linear in `e`, at every point outside the
inner radius and for `s ≥ s1`. -/
theorem genSeries_linear_map {E : Type*} [AddCommGroup E] [Module ℂ E]
    (U : E →ₗ[ℂ] SourceRadiatedSeries.VectorL2) (q : ℝ) (hq : 0 < q) (hq1 : 1 ≤ q) (n : ℕ)
    (ci : SourceRadiatedSeries.Coefficient) (b B s0 : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0)
    (hs0 : 0 < s0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (s : ℕ) (hs : max (s1pair q hq n s0) (s1pair q hq n 1) ≤ s) (x : Space)
    (hx : RadialPhaseLimit.radius s < ‖x‖) (e1 e2 : E) (α β : ℂ) :
    SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci (U (α • e1 + β • e2)) j)) s x =
      α • SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci (U e1) j)) s x +
      β • SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci (U e2) j)) s x ∧
    SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci (U (α • e1 + β • e2)) j)) s x =
      α • SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci (U e1) j)) s x +
      β • SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q hq n) SourceRadiatedFlux.tmFlag
        SourceRadiatedFlux.polyFam
        (SourceRadiatedFlux.coeffFam (fun _ j => DynamicVolume.source ci (U e2) j)) s x := by
  rw [map_add, map_smul, map_smul]
  exact genSeries_linear_source q hq hq1 n ci b B s0 hb hB hscale hBs hs0 hci s hs x hx (U e1) (U e2) α β

end OQ14.SourceRadiatedAnnulus

#print axioms OQ14.SourceRadiatedAnnulus.scalarPair_translate_bound
#print axioms OQ14.SourceRadiatedAnnulus.srcFunctional_apply
#print axioms OQ14.SourceRadiatedAnnulus.exists_electric_functional
#print axioms OQ14.SourceRadiatedAnnulus.exists_magnetic_functional
#print axioms OQ14.SourceRadiatedAnnulus.ae_eq_of_weak_series
#print axioms OQ14.SourceRadiatedAnnulus.decomp_component_le
#print axioms OQ14.SourceRadiatedAnnulus.integrable_mul_test
#print axioms OQ14.SourceRadiatedAnnulus.magnetic_congr
#print axioms OQ14.SourceRadiatedAnnulus.scattered_tm_mode_ae
#print axioms OQ14.SourceRadiatedAnnulus.scattered_te_mode_ae
#print axioms OQ14.SourceRadiatedAnnulus.magnetic_tm_mode_ae
#print axioms OQ14.SourceRadiatedAnnulus.magnetic_te_mode_ae
#print axioms OQ14.SourceRadiatedAnnulus.one_lt_radius
#print axioms OQ14.SourceRadiatedAnnulus.Kc_nonneg
#print axioms OQ14.SourceRadiatedAnnulus.shell_hyps
#print axioms OQ14.SourceRadiatedAnnulus.magnetic_shell_locallyIntegrable
#print axioms OQ14.SourceRadiatedAnnulus.tauE_eq
#print axioms OQ14.SourceRadiatedAnnulus.tauH_eq
#print axioms OQ14.SourceRadiatedAnnulus.termBound_summable
#print axioms OQ14.SourceRadiatedAnnulus.paired_annulus_electric_ae
#print axioms OQ14.SourceRadiatedAnnulus.paired_annulus_magnetic_ae
#print axioms OQ14.SourceRadiatedAnnulus.radiated_decomp_outside
#print axioms OQ14.SourceRadiatedAnnulus.radiated_decomp_outside_of_norm_bound
#print axioms OQ14.SourceRadiatedAnnulus.source_lin
#print axioms OQ14.SourceRadiatedAnnulus.moments_linear
#print axioms OQ14.SourceRadiatedAnnulus.coeffFam_linear
#print axioms OQ14.SourceRadiatedAnnulus.genElectric_summable
#print axioms OQ14.SourceRadiatedAnnulus.genSeries_linear_source
#print axioms OQ14.SourceRadiatedAnnulus.sphere_null
#print axioms OQ14.SourceRadiatedAnnulus.gen_electric_aesm
#print axioms OQ14.SourceRadiatedAnnulus.gen_magnetic_aesm
#print axioms OQ14.SourceRadiatedAnnulus.aesm_closed_of_open
#print axioms OQ14.SourceRadiatedAnnulus.radiated_plane_aesm
#print axioms OQ14.SourceRadiatedAnnulus.genSeries_linear_map
