import CoreOutgoingModes

/-! The free dyadic potential of a compactly supported source outside its support.  Outside a ball of radius
`R ≥ 2` containing the support (and with `2 (B base) ≤ R`) the electric potential is the vacuum outgoing mode
series with the source moments as coefficients; the magnetic potential is the dual series (identified from the
electric one by the weak first Maxwell equation).  Both series have a degree-summable plane decomposition
(radial part `O(1/|x|^2)`, tangential part `O(1/|x|)`) with constants independent of the point. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.CoreFreePotential
open MeasureTheory Filter Set Metric Complex OQ14.Maxwell OQ14.SourceRemotePlaneBand OQ14.CoreWeakSeries
  OQ14.CoreWeakLinear OQ14.CoreOutgoingModes OQ14.BackgroundModeMaxwell OQ14.HarmonicPolynomial
  OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization OQ14.AngularExteriorBounds
open OQ14.ModalAlgebra (xi xiD)
open OQ14.BarrierDegreeFluxConstants (decomp_mono)
open scoped Topology ComplexConjugate

/-! ### Modes, moments and coefficient bounds -/

/-- The harmonic polynomial of the positive index `a` (degree `a.1+1`). -/
abbrev modeP (a : PositiveIndex) : Poly := (representative (a.1+1) a.2 : Poly)

theorem modeP_hom (a : PositiveIndex) : (modeP a).IsHomogeneous (a.1+1) := representative_homogeneous _ _

theorem modeP_harm (a : PositiveIndex) : formalLaplacian (modeP a) = 0 := representative_harmonic _ _

/-- The electric moment of the source against the regular TM mode of the index. -/
def momentTM (ρ : Fin 3 → Space → ℂ) (a : PositiveIndex) : ℂ :=
  ∑ j, ∫ y, FreeSourceCoefficients.tmCoefficient a y j * ρ j y

/-- The moment of the source against the regular TE mode of the index. -/
def momentTE (ρ : Fin 3 → Space → ℂ) (a : PositiveIndex) : ℂ :=
  ∑ j, ∫ y, FreeSourceCoefficients.teCoefficient a y j * ρ j y

/-- The total mass of the source. -/
def mass (ρ : Fin 3 → Space → ℂ) : ℝ := ∑ j, ∫ y, ‖ρ j y‖

/-- The bound of the regular mode coefficients on the ball of radius `b`. -/
def coefBound (b B : ℝ) (a : PositiveIndex) : ℝ :=
  DebyeJetBounds.scale 0 b * RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (a.1+2 : ℝ)^3 * B^(a.1+1)

theorem coefBound_nonneg (b B : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B) (a : PositiveIndex) : 0 ≤ coefBound b B a := by
  have h := DebyeJetBounds.scale_nonnegative 0 b hb
  have h' := (RiccatiSeriesCoefficients.amplitude_pos (a.1+1) 0).le
  unfold coefBound
  positivity

theorem mass_nonneg (ρ : Fin 3 → Space → ℂ) : 0 ≤ mass ρ :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _

theorem continuous_tm (a : PositiveIndex) (j : Fin 3) :
    Continuous (fun y : Space => FreeSourceCoefficients.tmCoefficient a y j) := by
  have h : Continuous (fun y : Space => SolidMaxwellProfiles.electric (a.1+1) (modeP a) y j) :=
    (SolidMaxwellProfiles.electric_smooth (a.1+1) (modeP a) j).continuous
  exact continuous_const.mul h

theorem continuous_te (a : PositiveIndex) (j : Fin 3) :
    Continuous (fun y : Space => FreeSourceCoefficients.teCoefficient a y j) := by
  have h : Continuous (fun y : Space => DebyeUnitReaction.toroidal a y j) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (DebyeCalculus.toroidal_smooth _ y
      (SolidScalarHelmholtz.wave_contDiff (a.1+1) 1 (modeP a)).contDiffAt j).continuousAt
  exact continuous_const.mul h

theorem integrable_coeff (g : Space → ℂ) (hg : Continuous g) (T b : ℝ) (hgb : ∀ y : Space, ‖y‖ ≤ b → ‖g y‖ ≤ T)
    (f : Space → ℂ) (hf : Integrable f) (hz : ∀ y, y ∉ closedBall (0 : Space) b → f y = 0) :
    Integrable (fun y => g y * f y) ∧ ‖∫ y, g y * f y‖ ≤ T * ∫ y, ‖f y‖ := by
  have hpt : ∀ y, ‖g y * f y‖ ≤ T * ‖f y‖ := by
    intro y
    by_cases hy : ‖y‖ ≤ b
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hgb y hy) (norm_nonneg _)
    · have : f y = 0 := hz y (by simpa [mem_closedBall_zero_iff] using hy)
      simp [this]
  have hi : Integrable (fun y => g y * f y) :=
    (hf.norm.const_mul T).mono' (hg.aestronglyMeasurable.mul hf.aestronglyMeasurable)
      (Eventually.of_forall hpt)
  refine ⟨hi, ?_⟩
  exact (norm_integral_le_of_norm_le (hf.norm.const_mul T) (Eventually.of_forall hpt)).trans_eq
    (integral_const_mul T _)

theorem moment_bounds (b B : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j y, y ∉ closedBall (0 : Space) b → ρ j y = 0)
    (a : PositiveIndex) :
    (∀ j, Integrable (fun y => FreeSourceCoefficients.tmCoefficient a y j * ρ j y)) ∧
    (∀ j, Integrable (fun y => FreeSourceCoefficients.teCoefficient a y j * ρ j y)) ∧
    ‖momentTM ρ a‖ ≤ coefBound b B a * mass ρ ∧ ‖momentTE ρ a‖ ≤ coefBound b B a * mass ρ := by
  have hcoef (y : Space) (hy : ‖y‖ ≤ b) (j : Fin 3) :=
    OutgoingDyadBounds.regular_coefficient_bound a b B hb hB hscale y hy j
  have ht (j : Fin 3) := integrable_coeff _ (continuous_tm a j) (coefBound b B a) b
    (fun y hy => (hcoef y hy j).1) (ρ j) (hρ j) (hc j)
  have he (j : Fin 3) := integrable_coeff _ (continuous_te a j) (coefBound b B a) b
    (fun y hy => (hcoef y hy j).2) (ρ j) (hρ j) (hc j)
  refine ⟨fun j => (ht j).1, fun j => (he j).1, ?_, ?_⟩
  · calc ‖momentTM ρ a‖ ≤ ∑ j, ‖∫ y, FreeSourceCoefficients.tmCoefficient a y j * ρ j y‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j, coefBound b B a * ∫ y, ‖ρ j y‖ := Finset.sum_le_sum fun j _ => (ht j).2
      _ = coefBound b B a * mass ρ := by rw [mass, Finset.mul_sum]
  · calc ‖momentTE ρ a‖ ≤ ∑ j, ‖∫ y, FreeSourceCoefficients.teCoefficient a y j * ρ j y‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j, coefBound b B a * ∫ y, ‖ρ j y‖ := Finset.sum_le_sum fun j _ => (he j).2
      _ = coefBound b B a * mass ρ := by rw [mass, Finset.mul_sum]

/-! ### The outgoing series of the free dyadic potential -/

theorem term_eq (a : PositiveIndex) (x y : Space) (i j : Fin 3) :
    OutgoingSpatialSeries.term a x y i j =
      FreeSourceCoefficients.tmCoefficient a y j * (-Complex.I * outE (a.1+1) (modeP a) x i) +
      FreeSourceCoefficients.teCoefficient a y j * (-Complex.I * outH (a.1+1) (modeP a) x i) := by
  unfold OutgoingSpatialSeries.term
  rw [electric_data, magnetic_data]

theorem continuous_term_y (a : PositiveIndex) (x : Space) (i j : Fin 3) :
    Continuous (fun y : Space => OutgoingSpatialSeries.term a x y i j) := by
  have : (fun y : Space => OutgoingSpatialSeries.term a x y i j) = fun y =>
      FreeSourceCoefficients.tmCoefficient a y j * (-Complex.I * outE (a.1+1) (modeP a) x i) +
      FreeSourceCoefficients.teCoefficient a y j * (-Complex.I * outH (a.1+1) (modeP a) x i) :=
    funext fun y => term_eq a x y i j
  rw [this]
  exact ((continuous_tm a j).mul continuous_const).add ((continuous_te a j).mul continuous_const)

theorem electric_free_hasSum (b B R : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R) (hbR : b ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall (0 : Space) b → ρ j y = 0)
    (x : Space) (hx : R < ‖x‖) (i : Fin 3) :
    HasSum (fun a : PositiveIndex => (-Complex.I * momentTM ρ a) * outE (a.1+1) (modeP a) x i +
        (-Complex.I * momentTE ρ a) * outH (a.1+1) (modeP a) x i)
      (ExteriorContinuity.electric 1 ρ x i) := by
  have hj (j : Fin 3) : HasSum (fun a : PositiveIndex => ∫ y, ρ j y * OutgoingSpatialSeries.term a x y i j)
      (∫ y, ρ j y * DyadicKernel.dyadic 1 (x - y) i j) := by
    have hbound (a : PositiveIndex) (y : Space) :
        ‖ρ j y * OutgoingSpatialSeries.term a x y i j‖ ≤ ‖ρ j y‖ * OutgoingGeometricTail.majorant b R a := by
      by_cases hy : ‖y‖ ≤ b
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (OutgoingSpatialSeries.term_bound a b B R hb hB hscale hR hBR x y hx.le hy i j) (norm_nonneg _)
      · have : ρ j y = 0 := hc j y (by simpa [mem_closedBall_zero_iff] using hy)
        simp [this]
    have hlim (y : Space) : HasSum (fun a : PositiveIndex => ρ j y * OutgoingSpatialSeries.term a x y i j)
        (ρ j y * DyadicKernel.dyadic 1 (x - y) i j) := by
      by_cases hy : ‖y‖ ≤ b
      · have hxy : max R ‖y‖ < ‖x‖ := max_lt hx ((hy.trans hbR).trans_lt hx)
        have h := OutgoingFreeDyadic.actual_free_dyadic b B R hb hB hscale hR hBR y hy i j x hxy
        have hs := (OutgoingSpatialSeries.term_summable b B R hb hB hscale hR hBR x y hx.le hy i j).hasSum
        have hs' : HasSum (fun a : PositiveIndex => OutgoingSpatialSeries.term a x y i j)
            (DyadicKernel.dyadic 1 (x - y) i j) := by
          rw [← h]
          exact hs
        exact hs'.mul_left (ρ j y)
      · have : ρ j y = 0 := hc j y (by simpa [mem_closedBall_zero_iff] using hy)
        simpa [this] using (hasSum_zero : HasSum (fun _ : PositiveIndex => (0 : ℂ)) 0)
    exact hasSum_integral_of_dominated_convergence (μ := volume)
      (F := fun (a : PositiveIndex) (y : Space) => ρ j y * OutgoingSpatialSeries.term a x y i j)
      (f := fun y => ρ j y * DyadicKernel.dyadic 1 (x - y) i j)
      (fun a y => ‖ρ j y‖ * OutgoingGeometricTail.majorant b R a)
      (fun a => (hρ j).aestronglyMeasurable.mul (continuous_term_y a x i j).aestronglyMeasurable)
      (fun a => Eventually.of_forall fun y => hbound a y)
      (Eventually.of_forall fun y => (OutgoingGeometricTail.majorant_summable b R hb).mul_left _)
      (by
        simp_rw [tsum_mul_left]
        exact (hρ j).norm.mul_const _)
      (Eventually.of_forall hlim)
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ => hj j)
  have e : ExteriorContinuity.electric 1 ρ x i = ∑ j, ∫ y, ρ j y * DyadicKernel.dyadic 1 (x - y) i j := by
    unfold ExteriorContinuity.electric KernelConvolution.response
    rfl
  rw [e]
  convert hsum using 1
  funext a
  obtain ⟨ht, he, -, -⟩ := moment_bounds b B hb hB hscale ρ hρ hc a
  have hterm (j : Fin 3) : (∫ y, ρ j y * OutgoingSpatialSeries.term a x y i j) =
      (∫ y, FreeSourceCoefficients.tmCoefficient a y j * ρ j y) * (-Complex.I * outE (a.1+1) (modeP a) x i) +
      (∫ y, FreeSourceCoefficients.teCoefficient a y j * ρ j y) * (-Complex.I * outH (a.1+1) (modeP a) x i) := by
    have : (fun y => ρ j y * OutgoingSpatialSeries.term a x y i j) = fun y =>
        (FreeSourceCoefficients.tmCoefficient a y j * ρ j y) * (-Complex.I * outE (a.1+1) (modeP a) x i) +
        (FreeSourceCoefficients.teCoefficient a y j * ρ j y) * (-Complex.I * outH (a.1+1) (modeP a) x i) := by
      funext y
      rw [term_eq]
      ring
    rw [this, integral_add ((ht j).mul_const _) ((he j).mul_const _), integral_mul_const, integral_mul_const]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  unfold momentTM momentTE
  ring

/-! ### Plane decomposition of the outgoing modes -/

/-- The degree majorant of the free potential: a quarter of the geometric tail majorant times the mass bound. -/
def degConst (b R m : ℝ) (a : PositiveIndex) : ℝ := m/4 * OutgoingGeometricTail.majorant b R a

/-- The sum of the degree majorants. -/
def freeConst (b R m : ℝ) : ℝ := ∑' a, degConst b R m a

theorem degConst_nonneg (b R m : ℝ) (hb : 0 ≤ b) (hm : 0 ≤ m) (a : PositiveIndex) :
    0 ≤ degConst b R m a := by
  have h := OutgoingGeometricTail.prefactor_nonnegative b R hb
  unfold degConst OutgoingGeometricTail.majorant
  positivity

theorem degConst_summable (b R m : ℝ) (hb : 0 ≤ b) : Summable (degConst b R m) :=
  (OutgoingGeometricTail.majorant_summable b R hb).mul_left _

theorem freeConst_nonneg (b R m : ℝ) (hb : 0 ≤ b) (hm : 0 ≤ m) : 0 ≤ freeConst b R m :=
  tsum_nonneg (degConst_nonneg b R m hb hm)

theorem outgoing_piece (b B R m : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R) (hm : 0 ≤ m) (a : PositiveIndex) (c : ℂ)
    (hc : ‖c‖ ≤ m * coefBound b B a) (x : Space) (hx : R ≤ ‖x‖) :
    Decomp (degConst b R m a) (degConst b R m a) (c • fun i => outE (a.1+1) (modeP a) x i) x ∧
    Decomp (2 * degConst b R m a) 0 (c • fun i => outH (a.1+1) (modeP a) x i) x := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    linarith
  have hbase : 0 ≤ AngularExteriorBounds.base := by
    dsimp [AngularExteriorBounds.base, HarmonicSpatialMajorant.angularScale]
    positivity
  have hscale0 := DebyeJetBounds.scale_nonnegative 0 b hb
  have hscaleA : 0 ≤ AngularExteriorBounds.scale := by
    dsimp [AngularExteriorBounds.scale, HarmonicSpatialMajorant.areaScale]
    positivity
  have he := envelope_nonnegative (a.1+1)
  have hgeo := HankelExteriorBounds.regular_outgoing_geometric (a.1+1) (B*AngularExteriorBounds.base) R ‖x‖
    (mul_nonneg hB hbase) (by linarith) hBR hx
  obtain ⟨hE, hH⟩ := BackgroundFluxMajorant.eh_decomp_state (a.1+1) (modeP a) (modeP_hom a)
    ((((a.1+1 : ℕ) : ℝ)+1)*envelope (a.1+1)) (envelope (a.1+1)) (2*envelope (a.1+1))
    (fun n => (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => poloidal_bound (a.1+1) a.2 n i))
    (fun n => scalar_value_bound (a.1+1) a.2 n)
    (fun n => (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => toroidal_bound (a.1+1) a.2 n i))
    1 (by simp) (xi (a.1+1) (‖x‖ : ℂ)) (xiD (a.1+1) (‖x‖ : ℂ)) x hx0
  have hcoef := coefBound_nonneg b B hb hB a
  have hexp : 0 ≤ Real.exp R * (1/2 : ℝ)^(a.1+1) := by positivity
  have hp7 : (a.1+2 : ℝ)^7 ≤ (a.1+2 : ℝ)^8 := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg a.1 : (0:ℝ) ≤ a.1)]) (by norm_num)
  have hp6 : (a.1+2 : ℝ)^6 ≤ (a.1+2 : ℝ)^8 := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg a.1 : (0:ℝ) ≤ a.1)]) (by norm_num)
  have hp71 : ((a.1 : ℝ)+1)*(a.1+2 : ℝ)^7 ≤ (a.1+2 : ℝ)^8 := by
    have : (a.1+2 : ℝ)^8 = (a.1+2)*(a.1+2 : ℝ)^7 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hcm : ‖c‖ * 1 ≤ m * coefBound b B a := by simpa using hc
  refine ⟨?_, ?_⟩
  · have h1 := decomp_smul c hE
    have hdeg : degConst b R m a = m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale *
        (a.1+2 : ℝ)^8 * (Real.exp R * (1/2 : ℝ)^(a.1+1)) := by
      unfold degConst OutgoingGeometricTail.majorant OutgoingGeometricTail.prefactor
      ring
    refine decomp_mono hx0 h1 ?_ ?_
    · calc ‖c‖ * (‖xiD (a.1+1) (‖x‖ : ℂ)‖ * ((((a.1+1 : ℕ) : ℝ)+1)*envelope (a.1+1)))
          ≤ (m * coefBound b B a) * (‖xiD (a.1+1) (‖x‖ : ℂ)‖ * ((((a.1+1 : ℕ) : ℝ)+1)*envelope (a.1+1))) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ = m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * (a.1+2 : ℝ)^7 *
            (RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) *
              ‖xiD (a.1+1) (‖x‖ : ℂ)‖) := by
            unfold coefBound envelope
            push_cast
            ring
        _ ≤ m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * (a.1+2 : ℝ)^7 *
            (Real.exp R * (1/2 : ℝ)^(a.1+1)) :=
            mul_le_mul_of_nonneg_left hgeo.2 (by positivity)
        _ ≤ m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * (a.1+2 : ℝ)^8 *
            (Real.exp R * (1/2 : ℝ)^(a.1+1)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hp7 (by positivity)) hexp
        _ = degConst b R m a := hdeg.symm
    · calc ‖c‖ * (((((a.1+1 : ℕ) : ℝ))*((((a.1+1 : ℕ) : ℝ))+1))*‖xi (a.1+1) (‖x‖ : ℂ)‖*envelope (a.1+1))
          ≤ (m * coefBound b B a) * (((((a.1+1 : ℕ) : ℝ))*((((a.1+1 : ℕ) : ℝ))+1))*‖xi (a.1+1) (‖x‖ : ℂ)‖*envelope (a.1+1)) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ = m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * (((a.1 : ℝ)+1)*(a.1+2 : ℝ)^7) *
            (RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) *
              ‖xi (a.1+1) (‖x‖ : ℂ)‖) := by
            unfold coefBound envelope
            push_cast
            ring
        _ ≤ m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * (((a.1 : ℝ)+1)*(a.1+2 : ℝ)^7) *
            (Real.exp R * (1/2 : ℝ)^(a.1+1)) :=
            mul_le_mul_of_nonneg_left hgeo.1 (by positivity)
        _ ≤ m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * (a.1+2 : ℝ)^8 *
            (Real.exp R * (1/2 : ℝ)^(a.1+1)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hp71 (by positivity)) hexp
        _ = degConst b R m a := hdeg.symm
  · have h1 := decomp_smul c hH
    have hdeg : 2 * degConst b R m a = 2 * (m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale *
        (a.1+2 : ℝ)^8 * (Real.exp R * (1/2 : ℝ)^(a.1+1))) := by
      unfold degConst OutgoingGeometricTail.majorant OutgoingGeometricTail.prefactor
      ring
    refine decomp_mono hx0 h1 ?_ (by simp)
    calc ‖c‖ * (‖xi (a.1+1) (‖x‖ : ℂ)‖ * (2*envelope (a.1+1)))
        ≤ (m * coefBound b B a) * (‖xi (a.1+1) (‖x‖ : ℂ)‖ * (2*envelope (a.1+1))) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 2 * (m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * (a.1+2 : ℝ)^6 *
          (RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) *
            ‖xi (a.1+1) (‖x‖ : ℂ)‖)) := by
          unfold coefBound envelope
          push_cast
          ring
      _ ≤ 2 * (m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * (a.1+2 : ℝ)^6 *
          (Real.exp R * (1/2 : ℝ)^(a.1+1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeo.1 (by positivity)) (by norm_num)
      _ ≤ 2 * (m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * (a.1+2 : ℝ)^8 *
          (Real.exp R * (1/2 : ℝ)^(a.1+1))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp6 (by positivity)) hexp) (by norm_num)
      _ = 2 * degConst b R m a := hdeg.symm

theorem outgoing_pair_decomp (b B R m : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R) (hm : 0 ≤ m) (a : PositiveIndex) (α β : ℂ)
    (hα : ‖α‖ ≤ m * coefBound b B a) (hβ : ‖β‖ ≤ m * coefBound b B a) (x : Space) (hx : R ≤ ‖x‖) :
    Decomp (3 * degConst b R m a) (degConst b R m a)
      (fun i => α * outE (a.1+1) (modeP a) x i + β * outH (a.1+1) (modeP a) x i) x ∧
    Decomp (3 * degConst b R m a) (degConst b R m a)
      (fun i => α * outH (a.1+1) (modeP a) x i - β * outE (a.1+1) (modeP a) x i) x := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    linarith
  obtain ⟨p1, p2⟩ := outgoing_piece b B R m hb hB hR hBR hm a α hα x hx
  obtain ⟨q1, q2⟩ := outgoing_piece b B R m hb hB hR hBR hm a β hβ x hx
  obtain ⟨r1, r2⟩ := outgoing_piece b B R m hb hB hR hBR hm a (-β) (by simpa using hβ) x hx
  constructor
  · have h := decomp_add p1 q2
    have e : (fun i => α * outE (a.1+1) (modeP a) x i + β * outH (a.1+1) (modeP a) x i) =
        (α • fun i => outE (a.1+1) (modeP a) x i) + (β • fun i => outH (a.1+1) (modeP a) x i) := by
      funext i
      simp
    rw [e]
    exact decomp_mono hx0 h (by linarith) (by linarith)
  · have h := decomp_add p2 r1
    have e : (fun i => α * outH (a.1+1) (modeP a) x i - β * outE (a.1+1) (modeP a) x i) =
        (α • fun i => outH (a.1+1) (modeP a) x i) + ((-β) • fun i => outE (a.1+1) (modeP a) x i) := by
      funext i
      simp
      ring
    rw [e]
    exact decomp_mono hx0 h (by linarith) (by linarith)

theorem moment_norm_le (b B m : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j y, y ∉ closedBall (0 : Space) b → ρ j y = 0)
    (hm : mass ρ ≤ m) (a : PositiveIndex) :
    ‖-Complex.I * momentTM ρ a‖ ≤ m * coefBound b B a ∧ ‖-Complex.I * momentTE ρ a‖ ≤ m * coefBound b B a := by
  obtain ⟨-, -, h1, h2⟩ := moment_bounds b B hb hB hscale ρ hρ hc a
  have hcb := coefBound_nonneg b B hb hB a
  have hl : coefBound b B a * mass ρ ≤ m * coefBound b B a := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact h1.trans hl
  · rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    exact h2.trans hl

/-! ### The free potentials as plane-decomposed series -/

theorem electric_free_decomp (b B R m : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R) (hbR : b ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall (0 : Space) b → ρ j y = 0) (hm : mass ρ ≤ m)
    (x : Space) (hx : R < ‖x‖) :
    Decomp (3 * freeConst b R m) (freeConst b R m) (ExteriorContinuity.electric 1 ρ x) x := by
  have hm0 : 0 ≤ m := (mass_nonneg ρ).trans hm
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    linarith
  have hsum : HasSum (fun a : PositiveIndex => fun i : Fin 3 =>
      (-Complex.I * momentTM ρ a) * outE (a.1+1) (modeP a) x i +
        (-Complex.I * momentTE ρ a) * outH (a.1+1) (modeP a) x i) (ExteriorContinuity.electric 1 ρ x) :=
    Pi.hasSum.mpr fun i => electric_free_hasSum b B R hb hB hscale hR hBR hbR ρ hρ hc x hx i
  have hdec := decomp_tsum_gen (fun a : PositiveIndex => fun i : Fin 3 =>
      (-Complex.I * momentTM ρ a) * outE (a.1+1) (modeP a) x i +
        (-Complex.I * momentTE ρ a) * outH (a.1+1) (modeP a) x i)
    (fun a => 3 * degConst b R m a) (fun a => degConst b R m a)
    ((degConst_summable b R m hb).mul_left 3) (degConst_summable b R m hb) x hx0
    (fun a => (outgoing_pair_decomp b B R m hb hB hR hBR hm0 a _ _
      (moment_norm_le b B m hb hB hscale ρ hρ hc hm a).1 (moment_norm_le b B m hb hB hscale ρ hρ hc hm a).2
      x hx.le).1)
  rw [hsum.tsum_eq, tsum_mul_left] at hdec
  exact hdec.2

theorem magnetic_free_hasSum (b B R m : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R) (hbR : b ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall (0 : Space) b → ρ j y = 0)
    (hF : ∃ F : VectorFourier.VectorL2, ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j)
    (hm : mass ρ ≤ m) (x : Space) (hx : R < ‖x‖) (i : Fin 3) :
    HasSum (fun a : PositiveIndex => (-Complex.I * momentTM ρ a) * outH (a.1+1) (modeP a) x i -
        (-Complex.I * momentTE ρ a) * outE (a.1+1) (modeP a) x i)
      (MagneticResponse.magnetic 1 ρ x i) := by
  have hm0 : 0 ≤ m := (mass_nonneg ρ).trans hm
  obtain ⟨F, hFρ⟩ := hF
  have hR0 : 0 < R := by linarith
  let Ω : Set Space := {y : Space | R < ‖y‖}
  have hΩ : IsOpen Ω := isOpen_lt continuous_const continuous_norm
  have h0 : ∀ y ∈ Ω, y ≠ 0 := by
    intro y hy h
    have hy' : R < ‖y‖ := hy
    rw [h, norm_zero] at hy'
    linarith
  let Eh : PositiveIndex → Field := fun a y i => (-Complex.I * momentTM ρ a) * outE (a.1+1) (modeP a) y i +
    (-Complex.I * momentTE ρ a) * outH (a.1+1) (modeP a) y i
  let Hh : PositiveIndex → Field := fun a y i => (-Complex.I * momentTM ρ a) * outH (a.1+1) (modeP a) y i -
    (-Complex.I * momentTE ρ a) * outE (a.1+1) (modeP a) y i
  let M : PositiveIndex → ℝ := fun a => 3 * degConst b R m a / R + degConst b R m a / R^2
  have hMsum : Summable M :=
    (((degConst_summable b R m hb).mul_left 3).div_const R).add ((degConst_summable b R m hb).div_const (R^2))
  have hdec (a : PositiveIndex) (y : Space) (hy : y ∈ Ω) :=
    outgoing_pair_decomp b B R m hb hB hR hBR hm0 a _ _
      (moment_norm_le b B m hb hB hscale ρ hρ hc hm a).1 (moment_norm_le b B m hb hB hscale ρ hρ hc hm a).2
      y (le_of_lt hy)
  have hEb : ∀ a, ∀ y ∈ Ω, ∀ j, ‖Eh a y j‖ ≤ M a := fun a y hy j =>
    (norm_le_pi_norm (fun i => Eh a y i) j).trans (norm_le_of_decomp (hdec a y hy).1 R hR0 (le_of_lt hy))
  have hHb : ∀ a, ∀ y ∈ Ω, ∀ j, ‖Hh a y j‖ ≤ M a := fun a y hy j =>
    (norm_le_pi_norm (fun i => Hh a y i) j).trans (norm_le_of_decomp (hdec a y hy).2 R hR0 (le_of_lt hy))
  have hEc : ∀ a j, ContinuousOn (fun y => Eh a y j) Ω := fun a j =>
    (continuousOn_const.mul (continuousOn_outE _ _ Ω h0 j)).add
      (continuousOn_const.mul (continuousOn_outH _ _ Ω h0 j))
  have hHc : ∀ a j, ContinuousOn (fun y => Hh a y j) Ω := fun a j =>
    (continuousOn_const.mul (continuousOn_outH _ _ Ω h0 j)).sub
      (continuousOn_const.mul (continuousOn_outE _ _ Ω h0 j))
  have hw : ∀ a, WeakOn Ω (Eh a) (Hh a) := fun a =>
    weak_out_pair (a.1+1) (modeP a) (modeP_hom a) (modeP_harm a) Ω h0 _ _
  have hW := weakOn_tsum hΩ Eh Hh M hMsum hEc hHc hEb hHb hw
  have hEser : ∀ y ∈ Ω, ∀ j, (∑' a, Eh a y j) = ExteriorContinuity.electric 1 ρ y j := fun y hy j =>
    (electric_free_hasSum b B R hb hB hscale hR hBR hbR ρ hρ hc y hy j).tsum_eq
  have hW2 : WeakOn Ω (ExteriorContinuity.electric 1 ρ) (fun y j => ∑' a, Hh a y j) :=
    weakOn_congr hEser (fun y _ j => rfl) hW
  have hcR : ∀ j y, y ∉ closedBall (0 : Space) R → ρ j y = 0 := fun j y hy =>
    hc j y (fun hyb => hy (closedBall_subset_closedBall hbR hyb))
  have hforced := ForcedMaxwellResponse.representative_forced 1 R F ρ hρ hcR hFρ
  have hW1 : WeakOn Ω (ExteriorContinuity.representative 1 F ρ R) (MagneticResponse.magnetic 1 ρ) := by
    intro j f _
    have := (hforced j f).1
    simpa using this
  have hW1' : WeakOn Ω (ExteriorContinuity.electric 1 ρ) (MagneticResponse.magnetic 1 ρ) :=
    weakOn_congr (fun y hy j => by rw [ExteriorContinuity.representative_exterior 1 F ρ R y hy])
      (fun y _ j => rfl) hW1
  have hcontH : ∀ j, ContinuousOn (fun y => MagneticResponse.magnetic 1 ρ y j) Ω := fun j y hy =>
    ((continuousAt_pi.mp (ExteriorContinuity.magnetic_continuousAt 1 ρ hρ R hcR y hy)) j).continuousWithinAt
  have hcontS : ∀ j, ContinuousOn (fun y => ∑' a, Hh a y j) Ω := fun j =>
    continuousOn_tsum (fun a => hHc a j) hMsum (fun a y hy => hHb a y hy j)
  have heq := weak_unique hΩ (ExteriorContinuity.electric 1 ρ) (MagneticResponse.magnetic 1 ρ)
    (fun y j => ∑' a, Hh a y j) hcontH hcontS hW1' hW2 x hx i
  have hs : Summable (fun a => Hh a x i) :=
    Summable.of_norm_bounded M hMsum (fun a => hHb a x hx i)
  rw [heq]
  exact hs.hasSum

theorem magnetic_free_decomp (b B R m : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R) (hbR : b ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall (0 : Space) b → ρ j y = 0)
    (hF : ∃ F : VectorFourier.VectorL2, ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j)
    (hm : mass ρ ≤ m) (x : Space) (hx : R < ‖x‖) :
    Decomp (3 * freeConst b R m) (freeConst b R m) (MagneticResponse.magnetic 1 ρ x) x := by
  have hm0 : 0 ≤ m := (mass_nonneg ρ).trans hm
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    linarith
  have hsum : HasSum (fun a : PositiveIndex => fun i : Fin 3 =>
      (-Complex.I * momentTM ρ a) * outH (a.1+1) (modeP a) x i -
        (-Complex.I * momentTE ρ a) * outE (a.1+1) (modeP a) x i) (MagneticResponse.magnetic 1 ρ x) :=
    Pi.hasSum.mpr fun i => magnetic_free_hasSum b B R m hb hB hscale hR hBR hbR ρ hρ hc hF hm x hx i
  have hdec := decomp_tsum_gen (fun a : PositiveIndex => fun i : Fin 3 =>
      (-Complex.I * momentTM ρ a) * outH (a.1+1) (modeP a) x i -
        (-Complex.I * momentTE ρ a) * outE (a.1+1) (modeP a) x i)
    (fun a => 3 * degConst b R m a) (fun a => degConst b R m a)
    ((degConst_summable b R m hb).mul_left 3) (degConst_summable b R m hb) x hx0
    (fun a => (outgoing_pair_decomp b B R m hb hB hR hBR hm0 a _ _
      (moment_norm_le b B m hb hB hscale ρ hρ hc hm a).1 (moment_norm_le b B m hb hB hscale ρ hρ hc hm a).2
      x hx.le).2)
  rw [hsum.tsum_eq, tsum_mul_left] at hdec
  exact hdec.2

/-- **The free potential.**  For a source supported in the ball of radius `b ≤ R`, `R ≥ 2`, `2 (B base) ≤ R`,
with `B ≥ degreeScale 2 b`, mass at most `m` and an `L2` representative, the electric and magnetic dyadic
potentials have, at every point outside the ball of radius `R`, a plane decomposition (tangential part
`≤ 3 C/|x|`, radial part `≤ C/|x|^2`) with the constant `C = freeConst b R m` depending only on `b`, `R` and
the mass bound. -/
theorem free_potential_decomp (b B R m : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R) (hbR : b ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall (0 : Space) b → ρ j y = 0)
    (hF : ∃ F : VectorFourier.VectorL2, ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j)
    (hm : mass ρ ≤ m) :
    ∀ x : Space, R < ‖x‖ →
      Decomp (3 * freeConst b R m) (freeConst b R m) (ExteriorContinuity.electric 1 ρ x) x ∧
      Decomp (3 * freeConst b R m) (freeConst b R m) (MagneticResponse.magnetic 1 ρ x) x :=
  fun x hx => ⟨electric_free_decomp b B R m hb hB hscale hR hBR hbR ρ hρ hc hm x hx,
    magnetic_free_decomp b B R m hb hB hscale hR hBR hbR ρ hρ hc hF hm x hx⟩

end OQ14.CoreFreePotential

#print axioms OQ14.CoreFreePotential.modeP_hom
#print axioms OQ14.CoreFreePotential.modeP_harm
#print axioms OQ14.CoreFreePotential.coefBound_nonneg
#print axioms OQ14.CoreFreePotential.mass_nonneg
#print axioms OQ14.CoreFreePotential.continuous_tm
#print axioms OQ14.CoreFreePotential.continuous_te
#print axioms OQ14.CoreFreePotential.integrable_coeff
#print axioms OQ14.CoreFreePotential.moment_bounds
#print axioms OQ14.CoreFreePotential.term_eq
#print axioms OQ14.CoreFreePotential.continuous_term_y
#print axioms OQ14.CoreFreePotential.electric_free_hasSum
#print axioms OQ14.CoreFreePotential.degConst_nonneg
#print axioms OQ14.CoreFreePotential.degConst_summable
#print axioms OQ14.CoreFreePotential.freeConst_nonneg
#print axioms OQ14.CoreFreePotential.outgoing_piece
#print axioms OQ14.CoreFreePotential.outgoing_pair_decomp
#print axioms OQ14.CoreFreePotential.moment_norm_le
#print axioms OQ14.CoreFreePotential.electric_free_decomp
#print axioms OQ14.CoreFreePotential.magnetic_free_hasSum
#print axioms OQ14.CoreFreePotential.magnetic_free_decomp
#print axioms OQ14.CoreFreePotential.free_potential_decomp
