import CoreRegularModes
import SourcePairedPlaneIdentification

/-! The shell reaction field in the growing core: for the actual paired shells the reaction field of an
inclusion source is, at every point `x` of the core with `rho1 < |x| < R_r` and for large shell index `r`, the
regular-mode series with coefficients (reaction multiplier of the degree) times (source moment) times the regular
Maxwell mode, with a plane decomposition whose constants do not depend on `r`; the same for the magnetic
reaction field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.CoreReaction
open MeasureTheory Filter Set Metric Complex OQ14.Maxwell OQ14.SourceRemotePlaneBand OQ14.CoreWeakSeries
  OQ14.CoreWeakLinear OQ14.CoreOutgoingModes OQ14.CoreFreePotential OQ14.CoreRegularModes
  OQ14.BackgroundModeMaxwell OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis
  OQ14.VectorHarmonicNormalization OQ14.AngularExteriorBounds OQ14.HankelRealBasis
open OQ14.BarrierDegreeFluxConstants (decomp_mono)
open scoped Topology ComplexConjugate

variable (q : ℝ) (hq : 1 ≤ q) (n : ℕ)

/-! ### The degree majorant for the actual paired shells -/

theorem tm_parameters (r : ℕ) :
    (∀ g ∈ (SourcePairedInclusion.data q hq n r).gs, 1 ≤ g.σ ∧ g.σ ≤ q^2 ∧ g.q^2 ≤ q^2) ∧
    (∀ g ∈ (SourcePairedInclusion.data q hq n r).gs, g.q ≤ q) :=
  ⟨fun g hg => let h := SourcePairedGeometry.physical_parameters q (zero_lt_one.trans_le hq) hq n r g hg
    ⟨h.1, h.2.1, h.2.2.1⟩,
   fun g hg => (SourcePairedGeometry.physical_parameters q (zero_lt_one.trans_le hq) hq n r g hg).2.2.2⟩

theorem te_parameters (r : ℕ) :
    (∀ g ∈ (SourcePairedInclusion.data q hq n r).gs.map SourceDielectricModes.teLayer,
      1 ≤ g.σ ∧ g.σ ≤ q^2 ∧ g.q^2 ≤ q^2) ∧
    (∀ g ∈ (SourcePairedInclusion.data q hq n r).gs.map SourceDielectricModes.teLayer, g.q ≤ q) := by
  have hq2 : 1 ≤ q^2 := by nlinarith
  constructor
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have h := SourcePairedGeometry.physical_parameters q (zero_lt_one.trans_le hq) hq n r g0 hg0
    exact ⟨le_rfl, hq2, h.2.2.1⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact (SourcePairedGeometry.physical_parameters q (zero_lt_one.trans_le hq) hq n r g0 hg0).2.2.2

theorem shell_degree_majorant (b0 ρ1 : ℝ) (hb0 : 0 < b0) (hρ1 : 1 ≤ ρ1)
    (hρ0 : 2 * (b0 * Real.exp (8 * HankelIntermediateBounds.exponent q)) ≤ ρ1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℕ in atTop, ∀ (a : PositiveIndex) (s : ℝ), ρ1 ≤ s →
      s ≤ (SourcePairedInclusion.data q hq n r).R →
      (RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * b0^(a.1+1) *
        ‖SourceCoreReaction.multiplier
          (SourceDielectricModes.tmData (SourcePairedInclusion.data q hq n r) (a.1+1))‖ *
        (|regular (a.1+1) s| + |regularD (a.1+1) s|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1)) ∧
      (RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * b0^(a.1+1) *
        ‖SourceCoreReaction.multiplier
          (SourceDielectricModes.teData (SourcePairedInclusion.data q hq n r) (a.1+1))‖ *
        (|regular (a.1+1) s| + |regularD (a.1+1) s|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1)) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hq2 : 1 ≤ q^2 := by nlinarith
  obtain ⟨C, hC0, hC⟩ := CoreReactionDegree.reaction_degree_bound q (q^2)
    (RadialFiniteLimit.width (RadialPairedFamily.tm q hq0 n)) b0 ρ1 hq hq2 hb0 hρ1 hρ0
  refine ⟨C, hC0, ?_⟩
  filter_upwards [RadialPhaseLimit.radius_tendsto.eventually
      (eventually_ge_atTop (max ρ1 (2*Real.exp (3/4)*b0))),
    RadialPhaseLimit.radius_tendsto.eventually
      (eventually_ge_atTop (RadialFiniteLimit.width (RadialPairedFamily.tm q hq0 n)))] with r hR hw
  intro a s hs hsR
  have hdR : (SourcePairedInclusion.data q hq n r).R = RadialPhaseLimit.radius r := rfl
  have hdX : (SourcePairedInclusion.data q hq n r).X = RadialPhaseLimit.radius r +
      RadialFiniteLimit.width (RadialPairedFamily.tm q hq0 n) := rfl
  have hX : (SourcePairedInclusion.data q hq n r).X ≤ 2 * (SourcePairedInclusion.data q hq n r).R := by
    rw [hdX, hdR]
    linarith
  have hd : (SourcePairedInclusion.data q hq n r).X - (SourcePairedInclusion.data q hq n r).R ≤
      RadialFiniteLimit.width (RadialPairedFamily.tm q hq0 n) := by
    rw [hdX, hdR]
    linarith
  have hR' : max ρ1 (2*Real.exp (3/4)*b0) ≤ (SourcePairedInclusion.data q hq n r).R := by
    rw [hdR]
    exact hR
  have hcast : (((a.1+1 : ℕ) : ℝ)+1) = (a.1 : ℝ)+2 := by push_cast; ring
  obtain ⟨tp1, tp2⟩ := tm_parameters q hq n r
  obtain ⟨ep1, ep2⟩ := te_parameters q hq n r
  constructor
  · have h := hC (a.1+1) (SourcePairedInclusion.data q hq n r).gs (SourcePairedInclusion.data q hq n r).X
      (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).chain
      (SourcePairedInclusion.data q hq n r).hR tp1 tp2 hX hd hR' s hs hsR
    rw [hcast] at h
    exact h
  · have h := hC (a.1+1) ((SourcePairedInclusion.data q hq n r).gs.map SourceDielectricModes.teLayer)
      (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
      (SourceDielectricModes.te_chain (SourcePairedInclusion.data q hq n r).chain)
      (SourcePairedInclusion.data q hq n r).hR ep1 ep2 hX hd hR' s hs hsR
    rw [hcast] at h
    exact h

/-! ### The reaction multipliers and the term identity -/

/-- The TM reaction multiplier of the degree `a.1+1`. -/
def muTM (d : SourceRadialSystem.Data) (a : PositiveIndex) : ℂ :=
  SourceCoreReaction.multiplier (SourceDielectricModes.tmData d (a.1+1))

/-- The TE reaction multiplier of the degree `a.1+1`. -/
def muTE (d : SourceRadialSystem.Data) (a : PositiveIndex) : ℂ :=
  SourceCoreReaction.multiplier (SourceDielectricModes.teData d (a.1+1))

theorem term_eq' (d : SourceRadialSystem.Data) (a : PositiveIndex) (x y : Space) (i j : Fin 3) :
    SourceModeReaction.term d a x y i j =
      FreeSourceCoefficients.tmCoefficient a y j *
        (muTM d a * SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i) +
      FreeSourceCoefficients.teCoefficient a y j *
        (muTE d a * SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i) := by
  unfold SourceModeReaction.term muTM muTE
  rw [← SourceModeReaction.tm_normalization, ← SourceModeReaction.te_normalization]

theorem term_bound' (d : SourceRadialSystem.Data) (b B : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (a : PositiveIndex) (x y : Space)
    (hy : ‖y‖ ≤ b) (i j : Fin 3) :
    ‖SourceModeReaction.term d a x y i j‖ ≤ coefBound b B a *
      (‖muTM d a‖ * ‖SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i‖ +
        ‖muTE d a‖ * ‖SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i‖) := by
  rw [term_eq']
  obtain ⟨h1, h2⟩ := OutgoingDyadBounds.regular_coefficient_bound a b B hb hB hscale y hy j
  have hc := coefBound_nonneg b B hb hB a
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have e1 : ‖FreeSourceCoefficients.tmCoefficient a y j‖ ≤ coefBound b B a := h1
  have e2 : ‖FreeSourceCoefficients.teCoefficient a y j‖ ≤ coefBound b B a := h2
  calc ‖FreeSourceCoefficients.tmCoefficient a y j‖ *
        (‖muTM d a‖ * ‖SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i‖) +
      ‖FreeSourceCoefficients.teCoefficient a y j‖ *
        (‖muTE d a‖ * ‖SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i‖)
      ≤ coefBound b B a * (‖muTM d a‖ * ‖SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i‖) +
        coefBound b B a * (‖muTE d a‖ * ‖SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i‖) :=
        add_le_add (mul_le_mul_of_nonneg_right e1 (by positivity))
          (mul_le_mul_of_nonneg_right e2 (by positivity))
    _ = _ := by ring

theorem continuous_term_y' (d : SourceRadialSystem.Data) (a : PositiveIndex) (x : Space) (i j : Fin 3) :
    Continuous (fun y : Space => SourceModeReaction.term d a x y i j) := by
  have : (fun y : Space => SourceModeReaction.term d a x y i j) = fun y =>
      FreeSourceCoefficients.tmCoefficient a y j *
        (muTM d a * SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i) +
      FreeSourceCoefficients.teCoefficient a y j *
        (muTE d a * SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i) :=
    funext fun y => term_eq' d a x y i j
  rw [this]
  exact ((continuous_tm a j).mul continuous_const).add ((continuous_te a j).mul continuous_const)

/-- Unit-moment bound of the regular-mode terms: the coefficient bound times the multiplier times the regular
mode is summable over the degree with constants independent of the stack. -/
theorem unit_bound (d : SourceRadialSystem.Data) (b B C ρ1 : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hρ1 : 0 < ρ1)
    (hΘtm : ∀ (a : PositiveIndex) (s : ℝ), ρ1 ≤ s → s ≤ d.R →
      RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) * ‖muTM d a‖ *
        (|regular (a.1+1) s| + |regularD (a.1+1) s|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1))
    (hΘte : ∀ (a : PositiveIndex) (s : ℝ), ρ1 ≤ s → s ≤ d.R →
      RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) * ‖muTE d a‖ *
        (|regular (a.1+1) s| + |regularD (a.1+1) s|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1))
    (a : PositiveIndex) (x : Space) (hx1 : ρ1 ≤ ‖x‖) (hxR : ‖x‖ ≤ d.R) (i : Fin 3) :
    coefBound b B a * (‖muTM d a‖ * ‖SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i‖ +
        ‖muTE d a‖ * ‖SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i‖) ≤
      3 * regConst b 1 C a / ρ1 + regConst b 1 C a / ρ1^2 := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx1
    linarith
  have hcoef := coefBound_nonneg b B hb hB a
  have hn1 : 0 ≤ ‖muTM d a‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖muTE d a‖ := norm_nonneg _
  have hcc1 : ‖(((coefBound b B a * ‖muTM d a‖ : ℝ)) : ℂ)‖ ≤ 1 * coefBound b B a * ‖muTM d a‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hcc2 : ‖(((coefBound b B a * ‖muTE d a‖ : ℝ)) : ℂ)‖ ≤ 1 * coefBound b B a * ‖muTE d a‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  obtain ⟨p1, -⟩ := regular_piece b B 1 C ‖muTM d a‖ hb hB zero_le_one hC hn1 a _ hcc1 x hx0
    (hΘtm a ‖x‖ hx1 hxR)
  obtain ⟨-, q2⟩ := regular_piece b B 1 C ‖muTE d a‖ hb hB zero_le_one hC hn2 a _ hcc2 x hx0
    (hΘte a ‖x‖ hx1 hxR)
  have m1 := norm_le_of_decomp p1 ρ1 hρ1 hx1
  have m2 := norm_le_of_decomp q2 ρ1 hρ1 hx1
  have c1 := norm_le_pi_norm (((coefBound b B a * ‖muTM d a‖ : ℝ) : ℂ) •
    fun k => SolidMaxwellProfiles.electric (a.1+1) (modeP a) x k) i
  have c2 := norm_le_pi_norm (((coefBound b B a * ‖muTE d a‖ : ℝ) : ℂ) •
    fun k => SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x k) i
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hcoef, abs_of_nonneg hn1, abs_of_nonneg hn2] at c1 c2
  have e0 : (0 : ℝ) / ρ1^2 = 0 := by simp
  rw [e0, add_zero] at m2
  calc coefBound b B a * (‖muTM d a‖ * ‖SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i‖ +
        ‖muTE d a‖ * ‖SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i‖)
      = coefBound b B a * ‖muTM d a‖ * ‖SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i‖ +
        coefBound b B a * ‖muTE d a‖ * ‖SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i‖ := by ring
    _ ≤ (regConst b 1 C a / ρ1 + regConst b 1 C a / ρ1^2) + 2 * regConst b 1 C a / ρ1 :=
        add_le_add (c1.trans m1) (c2.trans m2)
    _ = 3 * regConst b 1 C a / ρ1 + regConst b 1 C a / ρ1^2 := by ring

/-! ### The regular-mode series of the shell reaction field -/

theorem reactionField_hasSum (r : ℕ) (b B T ρ1 C : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hT2 : 2 ≤ T)
    (hBT : 2*(B*AngularExteriorBounds.base) ≤ T) (hTR : T < (SourcePairedInclusion.data q hq n r).R)
    (hbR : b < (SourcePairedInclusion.data q hq n r).R) (hC : 0 ≤ C) (hρ1 : 0 < ρ1)
    (hΘtm : ∀ (a : PositiveIndex) (s : ℝ), ρ1 ≤ s → s ≤ (SourcePairedInclusion.data q hq n r).R →
      RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) *
        ‖muTM (SourcePairedInclusion.data q hq n r) a‖ *
        (|regular (a.1+1) s| + |regularD (a.1+1) s|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1))
    (hΘte : ∀ (a : PositiveIndex) (s : ℝ), ρ1 ≤ s → s ≤ (SourcePairedInclusion.data q hq n r).R →
      RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) *
        ‖muTE (SourcePairedInclusion.data q hq n r) a‖ *
        (|regular (a.1+1) s| + |regularD (a.1+1) s|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1))
    (ci : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (x : Space) (hx1 : ρ1 ≤ ‖x‖) (hxR : ‖x‖ < (SourcePairedInclusion.data q hq n r).R) (i : Fin 3) :
    HasSum (fun a : PositiveIndex =>
      (muTM (SourcePairedInclusion.data q hq n r) a * momentTM (DynamicVolume.source ci u) a) *
        SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i +
      (muTE (SourcePairedInclusion.data q hq n r) a * momentTE (DynamicVolume.source ci u) a) *
        SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i)
      (SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X u x i) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hq2 : 1 ≤ q^2 := by nlinarith
  have hs := SourcePairedGeometry.physical_material_bounds q hq0 hq n r
  have hdisp := SourcePairedGeometry.physical_dispersion q hq0 n r
  have hρint : ∀ j, Integrable (DynamicVolume.source ci u j) :=
    fun j => DynamicVolume.source_integrable ci u b hci j
  have hρvan : ∀ j y, y ∉ closedBall (0 : Space) b → DynamicVolume.source ci u j y = 0 := by
    intro j y hy
    simp [DynamicVolume.source, hci y hy]
  have hNsum : Summable (fun a : PositiveIndex => 3 * regConst b 1 C a / ρ1 + regConst b 1 C a / ρ1^2) :=
    (((regConst_summable b 1 C).mul_left 3).div_const ρ1).add ((regConst_summable b 1 C).div_const (ρ1^2))
  set N : PositiveIndex → ℝ := fun a => coefBound b B a *
    (‖muTM (SourcePairedInclusion.data q hq n r) a‖ * ‖SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i‖ +
      ‖muTE (SourcePairedInclusion.data q hq n r) a‖ * ‖SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i‖)
    with hNdef
  have hN0 : ∀ a, 0 ≤ N a := fun a => by
    have := coefBound_nonneg b B hb hB a
    simp only [hNdef]
    positivity
  have hNle : ∀ a, N a ≤ 3 * regConst b 1 C a / ρ1 + regConst b 1 C a / ρ1^2 := fun a =>
    unit_bound (SourcePairedInclusion.data q hq n r) b B C ρ1 hb hB hC hρ1 hΘtm hΘte a x hx1 hxR.le i
  have hNs : Summable N := Summable.of_nonneg_of_le hN0 hNle hNsum
  have hj (j : Fin 3) : HasSum (fun a : PositiveIndex => ∫ y,
      SourceModeReaction.term (SourcePairedInclusion.data q hq n r) a x y i j *
        DynamicVolume.source ci u j y)
      (∫ y, ShellReactionIdentification.reactionKernel (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X x y i j * DynamicVolume.source ci u j y) := by
    have hbound (a : PositiveIndex) (y : Space) :
        ‖SourceModeReaction.term (SourcePairedInclusion.data q hq n r) a x y i j *
          DynamicVolume.source ci u j y‖ ≤ N a * ‖DynamicVolume.source ci u j y‖ := by
      by_cases hy : ‖y‖ ≤ b
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (term_bound' (SourcePairedInclusion.data q hq n r) b B hb hB hscale a x y hy i j) (norm_nonneg _)
      · have : DynamicVolume.source ci u j y = 0 := hρvan j y (by simpa [mem_closedBall_zero_iff] using hy)
        simp [this]
    have hlim (y : Space) : HasSum (fun a : PositiveIndex =>
        SourceModeReaction.term (SourcePairedInclusion.data q hq n r) a x y i j *
          DynamicVolume.source ci u j y)
        (ShellReactionIdentification.reactionKernel (SourcePairedInclusion.shell q hq n r)
          (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
          (SourcePairedInclusion.data q hq n r).X x y i j * DynamicVolume.source ci u j y) := by
      by_cases hy : ‖y‖ ≤ b
      · have hyR : ‖y‖ < (SourcePairedInclusion.data q hq n r).R := hy.trans_lt hbR
        have hh := SourceTensorResponse.physical_hasSum (SourcePairedInclusion.data q hq n r) (q^2) hq2 hs
          hdisp b B T hb hB hscale hT2 hBT hTR x y hxR hy hyR i j
        have hk : ShellReactionIdentification.reactionKernel (SourcePairedInclusion.shell q hq n r)
            (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
            (SourcePairedInclusion.data q hq n r).X x y i j =
            SourceTensorResponse.reaction (SourceMaterialCoefficient.coefficient
              (SourcePairedInclusion.data q hq n r) (q^2) hq2 hs) (SourcePairedInclusion.data q hq n r)
              y hyR x i j := by
          rw [SourcePairedReduction.reactionKernel_eq_pairedKernel q hq n r x y hyR i j]
          exact dif_pos hyR
        rw [hk]
        exact hh.mul_right _
      · have : DynamicVolume.source ci u j y = 0 := hρvan j y (by simpa [mem_closedBall_zero_iff] using hy)
        simpa [this] using (hasSum_zero : HasSum (fun _ : PositiveIndex => (0 : ℂ)) 0)
    exact hasSum_integral_of_dominated_convergence (μ := volume)
      (F := fun (a : PositiveIndex) (y : Space) =>
        SourceModeReaction.term (SourcePairedInclusion.data q hq n r) a x y i j *
          DynamicVolume.source ci u j y)
      (f := fun y => ShellReactionIdentification.reactionKernel (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X x y i j * DynamicVolume.source ci u j y)
      (fun a y => N a * ‖DynamicVolume.source ci u j y‖)
      (fun a => (continuous_term_y' (SourcePairedInclusion.data q hq n r) a x i j).aestronglyMeasurable.mul
        (hρint j).aestronglyMeasurable)
      (fun a => Eventually.of_forall fun y => hbound a y)
      (Eventually.of_forall fun y => hNs.mul_right _)
      (by
        simp_rw [tsum_mul_right]
        exact (hρint j).norm.const_mul _)
      (Eventually.of_forall hlim)
  have hsum := hasSum_sum (s := Finset.univ) (fun j _ => hj j)
  unfold SourcePairedReactionField.reactionField
  convert hsum using 1
  funext a
  obtain ⟨ht, he, -, -⟩ := moment_bounds b B hb hB hscale (DynamicVolume.source ci u) hρint hρvan a
  have hterm (j : Fin 3) : (∫ y, SourceModeReaction.term (SourcePairedInclusion.data q hq n r) a x y i j *
        DynamicVolume.source ci u j y) =
      (∫ y, FreeSourceCoefficients.tmCoefficient a y j * DynamicVolume.source ci u j y) *
        (muTM (SourcePairedInclusion.data q hq n r) a * SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i) +
      (∫ y, FreeSourceCoefficients.teCoefficient a y j * DynamicVolume.source ci u j y) *
        (muTE (SourcePairedInclusion.data q hq n r) a * SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i) := by
    have : (fun y => SourceModeReaction.term (SourcePairedInclusion.data q hq n r) a x y i j *
          DynamicVolume.source ci u j y) = fun y =>
        (FreeSourceCoefficients.tmCoefficient a y j * DynamicVolume.source ci u j y) *
          (muTM (SourcePairedInclusion.data q hq n r) a * SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i) +
        (FreeSourceCoefficients.teCoefficient a y j * DynamicVolume.source ci u j y) *
          (muTE (SourcePairedInclusion.data q hq n r) a * SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i) := by
      funext y
      rw [term_eq']
      ring
    rw [this, integral_add ((ht j).mul_const _) ((he j).mul_const _), integral_mul_const, integral_mul_const]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  unfold momentTM momentTE
  ring

/-! ### Weak Maxwell equations and continuity of the free fields of sources in the core's exterior -/

theorem weakOn_mono {Ω Ω2 : Set Space} (h : Ω ⊆ Ω2) {E H : Field} (hw : WeakOn Ω2 E H) : WeakOn Ω E H :=
  fun i f hf => hw i f (hf.trans h)

theorem fieldPair_ae_congr {Ω : Set Space} (E E2 : Field) (hae : ∀ᵐ x : Space, x ∈ Ω → E x = E2 x)
    (j : Fin 3) (g : DynamicSource.Test) (hg : tsupport (g.val : Space → ℂ) ⊆ Ω) :
    MaterialMaxwell.fieldPair E j g = MaterialMaxwell.fieldPair E2 j g := by
  unfold MaterialMaxwell.fieldPair
  apply integral_congr_ae
  filter_upwards [hae] with x hx
  by_cases hxΩ : x ∈ Ω
  · rw [hx hxΩ]
  · have : g.val x = 0 := image_eq_zero_of_nmem_tsupport (fun h => hxΩ (hg h))
    simp [this]

/-- The free pair of a source vanishing in a ball satisfies the weak first Maxwell equation inside the ball. -/
theorem weak_free_interior (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (a S : ℝ)
    (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y = 0)
    (hi : ∀ j y, y ∈ ball (0 : Space) a → ρ j y = 0)
    (hF : ∃ F : VectorFourier.VectorL2, ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) :
    WeakOn (ball (0 : Space) a) (ExteriorContinuity.electric 1 ρ) (MagneticResponse.magnetic 1 ρ) := by
  obtain ⟨F, hFρ⟩ := hF
  have hforced := ForcedMaxwellResponse.response_forced 1 F ρ hρ
    (fun j => NewtonExteriorResponse.source_compact (ρ j) S (hc j)) hFρ
  have hae := ConicalInteriorResponse.electric_ae_interior 1 F ρ hρ hFρ a S hc hi
  intro i f hf
  have h := (hforced i f).1
  have e : MagneticResponse.curlPair (MaterialMaxwell.fieldPair (FieldResponse.electric 1 F ρ)) i f =
      MagneticResponse.curlPair (MaterialMaxwell.fieldPair (ExteriorContinuity.electric 1 ρ)) i f := by
    unfold MagneticResponse.curlPair
    rw [fieldPair_ae_congr (Ω := ball (0 : Space) a) _ _ hae _ _ ((tsupport_testPartial_subset _ f).trans hf),
      fieldPair_ae_congr (Ω := ball (0 : Space) a) _ _ hae _ _ ((tsupport_testPartial_subset _ f).trans hf)]
  rw [← e, h]
  simp

theorem magnetic_hollow_continuousAt (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (a S : ℝ)
    (hc : ∀ j y, y ∉ closedBall (0 : Space) S → ρ j y = 0)
    (hi : ∀ j y, y ∈ ball (0 : Space) a → ρ j y = 0) (x : Space) (hx : ‖x‖ < a) (i : Fin 3) :
    ContinuousAt (fun y => MagneticResponse.magnetic 1 ρ y i) x := by
  have hsupp (j : Fin 3) (y : Space) (hy : ρ j y ≠ 0) : a ≤ ‖y‖ ∧ ‖y‖ ≤ S := by
    constructor
    · by_contra h
      push_neg at h
      exact hy (hi j y (by simpa using h))
    · by_contra h
      push_neg at h
      exact hy (hc j y (by simpa [not_le] using h))
  have hd (j k : Fin 3) : DifferentiableAt ℝ
      (KernelConvolution.response (fun z => GreenKernel.phiGradient 1 z k) (ρ j)) x :=
    (SourcePairedPlaneMagnetic.response_dcoord_hollow (fun z => GreenKernel.phiGradient 1 z k)
      (KernelGradient.gradient_measurable 1 k) (fun z hz => ExteriorSmooth.gradient_contDiffAt 1 k z hz)
      (ρ j) (hρ j) a S (hsupp j) x hx 0).2.1
  unfold MagneticResponse.magnetic
  exact continuousAt_const.mul
    (((hd (WeakCurl.previous i) (WeakCurl.next i)).continuousAt).sub
      ((hd (WeakCurl.next i) (WeakCurl.previous i)).continuousAt))

/-! ### The induced shell polarization -/

/-- The polarization induced in the shell of index `r` by the inclusion vector `u`. -/
def shellSource (r : ℕ) (ci : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2) :
    Fin 3 → Space → ℂ :=
  DynamicVolume.source (SourcePairedInclusion.shell q hq n r)
    (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
      (SourcePairedInclusion.data q hq n r).X)
      (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r)
        (ShellInclusionVolume.kernel 1 (SourcePairedInclusion.data q hq n r).X
          (StaticCoefficient.sqrtMultiplier ci u))))

theorem shellSource_props (r : ℕ) (ci : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2) :
    (∀ j, Integrable (shellSource q hq n r ci u j)) ∧
    (∀ j y, y ∉ closedBall (0 : Space) (SourcePairedInclusion.data q hq n r).X →
      shellSource q hq n r ci u j y = 0) ∧
    (∀ j y, y ∈ ball (0 : Space) (SourcePairedInclusion.data q hq n r).R →
      shellSource q hq n r ci u j y = 0) ∧
    (∃ F : VectorFourier.VectorL2, ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume]
      shellSource q hq n r ci u j) := by
  refine ⟨fun j => DynamicVolume.source_integrable _ _ _
      (fun y hy => SourcePairedInclusion.shell_support q hq n r y (by simpa using hy)) j, ?_, ?_, ?_⟩
  · intro j y hy
    simp [shellSource, DynamicVolume.source, SourcePairedInclusion.shell_support q hq n r y hy]
  · intro j y hy
    simp [shellSource, DynamicVolume.source,
      SourcePairedInclusion.shell_inner q hq n r y (mem_ball_zero_iff.mp hy).le]
  · exact ⟨StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r) _,
      fun j => StaticNewton.material_source_ae _ _ j⟩

/-- The weak first Maxwell equation of the shell reaction pair in the core. -/
theorem weak_reaction (r : ℕ) (b : ℝ) (hb : b < (SourcePairedInclusion.data q hq n r).R)
    (ci : StaticCoefficient.Coefficient)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (u : VectorFourier.VectorL2) :
    WeakOn (ball (0 : Space) (SourcePairedInclusion.data q hq n r).R)
      (fun x i => SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X u x i)
      (fun x i => SourcePairedPlaneMagnetic.magneticReactionField (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X u x i) := by
  obtain ⟨hρ, hc, hi, hF⟩ := shellSource_props q hq n r ci u
  have hw := weak_free_interior (shellSource q hq n r ci u) hρ _ _ hc hi hF
  refine weakOn_congr (fun x hx i => ?_) (fun x hx i => ?_) hw
  · exact (SourcePairedPlaneIdentification.reactionField_eq_free (SourcePairedInclusion.shell q hq n r) ci b
      (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X
      (SourcePairedInclusion.data q hq n r).X hb (SourcePairedInclusion.radii_ordered q hq n r) le_rfl
      (SourcePairedPlaneIdentification.shell_hcs q hq n r) hci u x (mem_ball_zero_iff.mp hx) i).symm
  · exact (SourcePairedPlaneIdentification.magneticReactionField_eq_free
      (SourcePairedInclusion.shell q hq n r) ci b
      (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X
      (SourcePairedInclusion.data q hq n r).X hb (SourcePairedInclusion.radii_ordered q hq n r) le_rfl
      (SourcePairedPlaneIdentification.shell_hcs q hq n r) hci u x (mem_ball_zero_iff.mp hx) i).symm

theorem magneticReaction_continuousAt (r : ℕ) (b : ℝ) (hb : b < (SourcePairedInclusion.data q hq n r).R)
    (ci : StaticCoefficient.Coefficient)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (u : VectorFourier.VectorL2) (x : Space) (hx : ‖x‖ < (SourcePairedInclusion.data q hq n r).R)
    (i : Fin 3) :
    ContinuousAt (fun y => SourcePairedPlaneMagnetic.magneticReactionField (SourcePairedInclusion.shell q hq n r)
      ci (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
      (SourcePairedInclusion.data q hq n r).X u y i) x := by
  obtain ⟨hρ, hc, hi, -⟩ := shellSource_props q hq n r ci u
  have hcont := magnetic_hollow_continuousAt (shellSource q hq n r ci u) hρ _ _ hc hi x hx i
  refine hcont.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hx)] with y hy
  exact (SourcePairedPlaneIdentification.magneticReactionField_eq_free
    (SourcePairedInclusion.shell q hq n r) ci b
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X
    (SourcePairedInclusion.data q hq n r).X hb (SourcePairedInclusion.radii_ordered q hq n r) le_rfl
    (SourcePairedPlaneIdentification.shell_hcs q hq n r) hci u y (mem_ball_zero_iff.mp hy) i)

/-! ### Decomposition of the reaction fields -/

theorem moment_mul_bound (b B m : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j y, y ∉ closedBall (0 : Space) b → ρ j y = 0)
    (hm : mass ρ ≤ m) (a : PositiveIndex) (μ1 μ2 : ℂ) :
    ‖μ1 * momentTM ρ a‖ ≤ m * coefBound b B a * ‖μ1‖ ∧ ‖μ2 * momentTE ρ a‖ ≤ m * coefBound b B a * ‖μ2‖ := by
  obtain ⟨-, -, h1, h2⟩ := moment_bounds b B hb hB hscale ρ hρ hc a
  have hcb := coefBound_nonneg b B hb hB a
  have hl : coefBound b B a * mass ρ ≤ coefBound b B a * m := mul_le_mul_of_nonneg_left hm hcb
  constructor
  · rw [norm_mul]
    calc ‖μ1‖ * ‖momentTM ρ a‖ ≤ ‖μ1‖ * (coefBound b B a * m) :=
          mul_le_mul_of_nonneg_left (h1.trans hl) (norm_nonneg _)
      _ = m * coefBound b B a * ‖μ1‖ := by ring
  · rw [norm_mul]
    calc ‖μ2‖ * ‖momentTE ρ a‖ ≤ ‖μ2‖ * (coefBound b B a * m) :=
          mul_le_mul_of_nonneg_left (h2.trans hl) (norm_nonneg _)
      _ = m * coefBound b B a * ‖μ2‖ := by ring

theorem reaction_electric_decomp (r : ℕ) (b B T ρ1 C m : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hT2 : 2 ≤ T)
    (hBT : 2*(B*AngularExteriorBounds.base) ≤ T) (hTR : T < (SourcePairedInclusion.data q hq n r).R)
    (hbR : b < (SourcePairedInclusion.data q hq n r).R) (hC : 0 ≤ C) (hρ1 : 0 < ρ1)
    (hΘtm : ∀ (a : PositiveIndex) (s : ℝ), ρ1 ≤ s → s ≤ (SourcePairedInclusion.data q hq n r).R →
      RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) *
        ‖muTM (SourcePairedInclusion.data q hq n r) a‖ *
        (|regular (a.1+1) s| + |regularD (a.1+1) s|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1))
    (hΘte : ∀ (a : PositiveIndex) (s : ℝ), ρ1 ≤ s → s ≤ (SourcePairedInclusion.data q hq n r).R →
      RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) *
        ‖muTE (SourcePairedInclusion.data q hq n r) a‖ *
        (|regular (a.1+1) s| + |regularD (a.1+1) s|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1))
    (ci : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (hmass : mass (DynamicVolume.source ci u) ≤ m)
    (x : Space) (hx1 : ρ1 ≤ ‖x‖) (hxR : ‖x‖ < (SourcePairedInclusion.data q hq n r).R) :
    Decomp (3 * ∑' a, regConst b m C a) (∑' a, regConst b m C a)
      (fun i => SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X u x i) x := by
  have hm0 : 0 ≤ m := (mass_nonneg _).trans hmass
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx1
    linarith
  have hρint : ∀ j, Integrable (DynamicVolume.source ci u j) :=
    fun j => DynamicVolume.source_integrable ci u b hci j
  have hρvan : ∀ j y, y ∉ closedBall (0 : Space) b → DynamicVolume.source ci u j y = 0 := by
    intro j y hy
    simp [DynamicVolume.source, hci y hy]
  have hsum : HasSum (fun a : PositiveIndex => fun i : Fin 3 =>
      (muTM (SourcePairedInclusion.data q hq n r) a * momentTM (DynamicVolume.source ci u) a) *
        SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i +
      (muTE (SourcePairedInclusion.data q hq n r) a * momentTE (DynamicVolume.source ci u) a) *
        SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i)
      (fun i => SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X u x i) :=
    Pi.hasSum.mpr fun i => reactionField_hasSum q hq n r b B T ρ1 C hb hB hscale hT2 hBT hTR hbR hC hρ1
      hΘtm hΘte ci u hci x hx1 hxR i
  have hdec := decomp_tsum_gen (fun a : PositiveIndex => fun i : Fin 3 =>
      (muTM (SourcePairedInclusion.data q hq n r) a * momentTM (DynamicVolume.source ci u) a) *
        SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i +
      (muTE (SourcePairedInclusion.data q hq n r) a * momentTE (DynamicVolume.source ci u) a) *
        SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i)
    (fun a => 3 * regConst b m C a) (fun a => regConst b m C a)
    ((regConst_summable b m C).mul_left 3) (regConst_summable b m C) x hx0
    (fun a => (regular_pair_decomp b B m C ‖muTM (SourcePairedInclusion.data q hq n r) a‖
      ‖muTE (SourcePairedInclusion.data q hq n r) a‖ hb hB hm0 hC (norm_nonneg _) (norm_nonneg _) a (muTM (SourcePairedInclusion.data q hq n r) a * momentTM (DynamicVolume.source ci u) a)
      (muTE (SourcePairedInclusion.data q hq n r) a * momentTE (DynamicVolume.source ci u) a)
      (moment_mul_bound b B m hb hB hscale (DynamicVolume.source ci u) hρint hρvan hmass a
        (muTM (SourcePairedInclusion.data q hq n r) a) (muTE (SourcePairedInclusion.data q hq n r) a)).1
      (moment_mul_bound b B m hb hB hscale (DynamicVolume.source ci u) hρint hρvan hmass a
        (muTM (SourcePairedInclusion.data q hq n r) a) (muTE (SourcePairedInclusion.data q hq n r) a)).2 x hx0
      (hΘtm a ‖x‖ hx1 hxR.le) (hΘte a ‖x‖ hx1 hxR.le)).1)
  rw [hsum.tsum_eq, tsum_mul_left] at hdec
  exact hdec.2

theorem reaction_magnetic_hasSum (r : ℕ) (b B T ρ1 C m : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hT2 : 2 ≤ T)
    (hBT : 2*(B*AngularExteriorBounds.base) ≤ T) (hTR : T < (SourcePairedInclusion.data q hq n r).R)
    (hbR : b < (SourcePairedInclusion.data q hq n r).R) (hC : 0 ≤ C) (hρ1 : 0 < ρ1)
    (hΘtm : ∀ (a : PositiveIndex) (s : ℝ), ρ1 ≤ s → s ≤ (SourcePairedInclusion.data q hq n r).R →
      RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) *
        ‖muTM (SourcePairedInclusion.data q hq n r) a‖ *
        (|regular (a.1+1) s| + |regularD (a.1+1) s|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1))
    (hΘte : ∀ (a : PositiveIndex) (s : ℝ), ρ1 ≤ s → s ≤ (SourcePairedInclusion.data q hq n r).R →
      RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) *
        ‖muTE (SourcePairedInclusion.data q hq n r) a‖ *
        (|regular (a.1+1) s| + |regularD (a.1+1) s|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1))
    (ci : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (hmass : mass (DynamicVolume.source ci u) ≤ m)
    (x : Space) (hx1 : ρ1 < ‖x‖) (hxR : ‖x‖ < (SourcePairedInclusion.data q hq n r).R) (i : Fin 3) :
    HasSum (fun a : PositiveIndex =>
      (muTM (SourcePairedInclusion.data q hq n r) a * momentTM (DynamicVolume.source ci u) a) *
        SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i -
      (muTE (SourcePairedInclusion.data q hq n r) a * momentTE (DynamicVolume.source ci u) a) *
        SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i)
      (SourcePairedPlaneMagnetic.magneticReactionField (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X u x i) := by
  have hm0 : 0 ≤ m := (mass_nonneg _).trans hmass
  have hρint : ∀ j, Integrable (DynamicVolume.source ci u j) :=
    fun j => DynamicVolume.source_integrable ci u b hci j
  have hρvan : ∀ j y, y ∉ closedBall (0 : Space) b → DynamicVolume.source ci u j y = 0 := by
    intro j y hy
    simp [DynamicVolume.source, hci y hy]
  let Ω : Set Space := {y : Space | ρ1 < ‖y‖ ∧ ‖y‖ < (SourcePairedInclusion.data q hq n r).R}
  have hΩ : IsOpen Ω :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have h0 : ∀ y ∈ Ω, y ≠ 0 := by
    intro y hy h
    have hy' : ρ1 < ‖y‖ := hy.1
    rw [h, norm_zero] at hy'
    linarith
  let α : PositiveIndex → ℂ := fun a =>
    muTM (SourcePairedInclusion.data q hq n r) a * momentTM (DynamicVolume.source ci u) a
  let β : PositiveIndex → ℂ := fun a =>
    muTE (SourcePairedInclusion.data q hq n r) a * momentTE (DynamicVolume.source ci u) a
  let Eh : PositiveIndex → Field := fun a y i => α a * SolidMaxwellProfiles.electric (a.1+1) (modeP a) y i +
    β a * SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) y i
  let Hh : PositiveIndex → Field := fun a y i => α a * SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) y i -
    β a * SolidMaxwellProfiles.electric (a.1+1) (modeP a) y i
  let M : PositiveIndex → ℝ := fun a => 3 * regConst b m C a / ρ1 + regConst b m C a / ρ1^2
  have hMsum : Summable M :=
    (((regConst_summable b m C).mul_left 3).div_const ρ1).add ((regConst_summable b m C).div_const (ρ1^2))
  have hdec (a : PositiveIndex) (y : Space) (hy : y ∈ Ω) :=
    regular_pair_decomp b B m C ‖muTM (SourcePairedInclusion.data q hq n r) a‖
      ‖muTE (SourcePairedInclusion.data q hq n r) a‖ hb hB hm0 hC (norm_nonneg _) (norm_nonneg _) a (α a) (β a)
      (moment_mul_bound b B m hb hB hscale (DynamicVolume.source ci u) hρint hρvan hmass a
        (muTM (SourcePairedInclusion.data q hq n r) a) (muTE (SourcePairedInclusion.data q hq n r) a)).1
      (moment_mul_bound b B m hb hB hscale (DynamicVolume.source ci u) hρint hρvan hmass a
        (muTM (SourcePairedInclusion.data q hq n r) a) (muTE (SourcePairedInclusion.data q hq n r) a)).2 y (h0 y hy)
      (hΘtm a ‖y‖ (le_of_lt hy.1) hy.2.le) (hΘte a ‖y‖ (le_of_lt hy.1) hy.2.le)
  have hEb : ∀ a, ∀ y ∈ Ω, ∀ j, ‖Eh a y j‖ ≤ M a := fun a y hy j =>
    (norm_le_pi_norm (fun i => Eh a y i) j).trans
      (norm_le_of_decomp (hdec a y hy).1 ρ1 hρ1 (le_of_lt hy.1))
  have hHb : ∀ a, ∀ y ∈ Ω, ∀ j, ‖Hh a y j‖ ≤ M a := fun a y hy j =>
    (norm_le_pi_norm (fun i => Hh a y i) j).trans
      (norm_le_of_decomp (hdec a y hy).2 ρ1 hρ1 (le_of_lt hy.1))
  have hEc : ∀ a j, ContinuousOn (fun y => Eh a y j) Ω := fun a j =>
    (continuousOn_const.mul (SolidMaxwellProfiles.electric_smooth (a.1+1) (modeP a) j).continuous.continuousOn).add
      (continuousOn_const.mul (SolidMaxwellProfiles.magnetic_smooth (a.1+1) (modeP a) j).continuous.continuousOn)
  have hHc : ∀ a j, ContinuousOn (fun y => Hh a y j) Ω := fun a j =>
    (continuousOn_const.mul (SolidMaxwellProfiles.magnetic_smooth (a.1+1) (modeP a) j).continuous.continuousOn).sub
      (continuousOn_const.mul (SolidMaxwellProfiles.electric_smooth (a.1+1) (modeP a) j).continuous.continuousOn)
  have hw : ∀ a, WeakOn Ω (Eh a) (Hh a) := fun a =>
    weak_solid_pair (a.1+1) (modeP a) (modeP_hom a) (modeP_harm a) Ω (α a) (β a)
  have hW := weakOn_tsum hΩ Eh Hh M hMsum hEc hHc hEb hHb hw
  have hEser : ∀ y ∈ Ω, ∀ j, (∑' a, Eh a y j) =
      SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X u y j := fun y hy j =>
    (reactionField_hasSum q hq n r b B T ρ1 C hb hB hscale hT2 hBT hTR hbR hC hρ1 hΘtm hΘte ci u hci y
      (le_of_lt hy.1) hy.2 j).tsum_eq
  have hW2 : WeakOn Ω (fun y j => SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r)
        ci (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X u y j) (fun y j => ∑' a, Hh a y j) :=
    weakOn_congr hEser (fun y _ j => rfl) hW
  have hW1 := weakOn_mono (Ω := Ω)
    (fun y hy => mem_ball_zero_iff.mpr hy.2) (weak_reaction q hq n r b hbR ci hci u)
  have hcontH : ∀ j, ContinuousOn (fun y => SourcePairedPlaneMagnetic.magneticReactionField
      (SourcePairedInclusion.shell q hq n r) ci (SourcePairedInclusion.data q hq n r).X
      (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X u y j) Ω :=
    fun j y hy => (magneticReaction_continuousAt q hq n r b hbR ci hci u y hy.2 j).continuousWithinAt
  have hcontS : ∀ j, ContinuousOn (fun y => ∑' a, Hh a y j) Ω := fun j =>
    continuousOn_tsum (fun a => hHc a j) hMsum (fun a y hy => hHb a y hy j)
  have heq := weak_unique hΩ _ _ (fun y j => ∑' a, Hh a y j) hcontH hcontS hW1 hW2 x ⟨hx1, hxR⟩ i
  have hs : Summable (fun a => Hh a x i) :=
    Summable.of_norm_bounded M hMsum (fun a => hHb a x ⟨hx1, hxR⟩ i)
  rw [heq]
  exact hs.hasSum

theorem reaction_magnetic_decomp (r : ℕ) (b B T ρ1 C m : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hT2 : 2 ≤ T)
    (hBT : 2*(B*AngularExteriorBounds.base) ≤ T) (hTR : T < (SourcePairedInclusion.data q hq n r).R)
    (hbR : b < (SourcePairedInclusion.data q hq n r).R) (hC : 0 ≤ C) (hρ1 : 0 < ρ1)
    (hΘtm : ∀ (a : PositiveIndex) (s : ℝ), ρ1 ≤ s → s ≤ (SourcePairedInclusion.data q hq n r).R →
      RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) *
        ‖muTM (SourcePairedInclusion.data q hq n r) a‖ *
        (|regular (a.1+1) s| + |regularD (a.1+1) s|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1))
    (hΘte : ∀ (a : PositiveIndex) (s : ℝ), ρ1 ≤ s → s ≤ (SourcePairedInclusion.data q hq n r).R →
      RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) *
        ‖muTE (SourcePairedInclusion.data q hq n r) a‖ *
        (|regular (a.1+1) s| + |regularD (a.1+1) s|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1))
    (ci : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (hmass : mass (DynamicVolume.source ci u) ≤ m)
    (x : Space) (hx1 : ρ1 < ‖x‖) (hxR : ‖x‖ < (SourcePairedInclusion.data q hq n r).R) :
    Decomp (3 * ∑' a, regConst b m C a) (∑' a, regConst b m C a)
      (fun i => SourcePairedPlaneMagnetic.magneticReactionField (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X u x i) x := by
  have hm0 : 0 ≤ m := (mass_nonneg _).trans hmass
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx1
    linarith
  have hρint : ∀ j, Integrable (DynamicVolume.source ci u j) :=
    fun j => DynamicVolume.source_integrable ci u b hci j
  have hρvan : ∀ j y, y ∉ closedBall (0 : Space) b → DynamicVolume.source ci u j y = 0 := by
    intro j y hy
    simp [DynamicVolume.source, hci y hy]
  have hsum : HasSum (fun a : PositiveIndex => fun i : Fin 3 =>
      (muTM (SourcePairedInclusion.data q hq n r) a * momentTM (DynamicVolume.source ci u) a) *
        SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i -
      (muTE (SourcePairedInclusion.data q hq n r) a * momentTE (DynamicVolume.source ci u) a) *
        SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i)
      (fun i => SourcePairedPlaneMagnetic.magneticReactionField (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X u x i) :=
    Pi.hasSum.mpr fun i => reaction_magnetic_hasSum q hq n r b B T ρ1 C m hb hB hscale hT2 hBT hTR hbR hC hρ1
      hΘtm hΘte ci u hci hmass x hx1 hxR i
  have hdec := decomp_tsum_gen (fun a : PositiveIndex => fun i : Fin 3 =>
      (muTM (SourcePairedInclusion.data q hq n r) a * momentTM (DynamicVolume.source ci u) a) *
        SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i -
      (muTE (SourcePairedInclusion.data q hq n r) a * momentTE (DynamicVolume.source ci u) a) *
        SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i)
    (fun a => 3 * regConst b m C a) (fun a => regConst b m C a)
    ((regConst_summable b m C).mul_left 3) (regConst_summable b m C) x hx0
    (fun a => (regular_pair_decomp b B m C ‖muTM (SourcePairedInclusion.data q hq n r) a‖
      ‖muTE (SourcePairedInclusion.data q hq n r) a‖ hb hB hm0 hC (norm_nonneg _) (norm_nonneg _) a (muTM (SourcePairedInclusion.data q hq n r) a * momentTM (DynamicVolume.source ci u) a)
      (muTE (SourcePairedInclusion.data q hq n r) a * momentTE (DynamicVolume.source ci u) a)
      (moment_mul_bound b B m hb hB hscale (DynamicVolume.source ci u) hρint hρvan hmass a
        (muTM (SourcePairedInclusion.data q hq n r) a) (muTE (SourcePairedInclusion.data q hq n r) a)).1
      (moment_mul_bound b B m hb hB hscale (DynamicVolume.source ci u) hρint hρvan hmass a
        (muTM (SourcePairedInclusion.data q hq n r) a) (muTE (SourcePairedInclusion.data q hq n r) a)).2 x hx0
      (hΘtm a ‖x‖ hx1.le hxR.le) (hΘte a ‖x‖ hx1.le hxR.le)).2)
  rw [hsum.tsum_eq, tsum_mul_left] at hdec
  exact hdec.2

/-! ### The reaction field of the actual paired shells in the growing core -/

theorem base_pos : 0 < AngularExteriorBounds.base := by
  dsimp [AngularExteriorBounds.base, HarmonicSpatialMajorant.angularScale]
  positivity

/-- The degree-uniform radius threshold: the inner scale of the regular states must exceed this multiple of
the moment scale of the source. -/
def rhoMin (q b : ℝ) : ℝ :=
  max 1 (2 * (max 1 (HarmonicSpatialMajorant.degreeScale 2 b) * AngularExteriorBounds.base *
    Real.exp (8 * HankelIntermediateBounds.exponent q)))

/-- The mass constant of an inclusion carrier. -/
def massConst (ci : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData ci) : ℝ :=
  3 * (Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier))

theorem massConst_nonneg (ci : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData ci) :
    0 ≤ massConst ci d := by
  unfold massConst
  positivity

theorem mass_source_le (ci : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData ci)
    (u : VectorFourier.VectorL2) : mass (DynamicVolume.source ci u) ≤ massConst ci d * ‖u‖ := by
  unfold mass massConst
  calc ∑ j : Fin 3, ∫ y, ‖DynamicVolume.source ci u j y‖
      ≤ ∑ _j : Fin 3, (Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier)) * ‖u‖ :=
        Finset.sum_le_sum fun j _ => SourcePairedReactionField.source_mass' ci d u j
    _ = 3 * (Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier)) * ‖u‖ := by
        simp [Finset.sum_const]
        ring

/-- **The shell reaction field in the growing core.**  For an inclusion with carrier in the ball of radius `b`
and `ρ1 ≥ rhoMin q b`, there is a constant `K` (depending only on `q`, `n`, `b`, `ρ1` and the
mass constants of the carrier, not on the shell index) such that for all large shell indices `r`, every inclusion vector `u` and
every point `x` of the core with `ρ1 < |x| < R_r`, the shell electric and magnetic reaction fields of `u` split at
`x` into a part orthogonal to `x` of size `3 K ‖u‖ / |x|` and a part parallel to `x` of size `K ‖u‖ / |x|^2`. -/
theorem reaction_core_decomp (ci : StaticCoefficient.Coefficient)
    (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : 0 ≤ b) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b)
    (ρ1 : ℝ) (hρ1 : rhoMin q b ≤ ρ1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℕ in atTop, ∀ (u : VectorFourier.VectorL2) (x : Space),
      ρ1 < ‖x‖ → ‖x‖ < (SourcePairedInclusion.data q hq n r).R →
      Decomp (3 * K * ‖u‖) (K * ‖u‖)
        (fun i => SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r) ci
          (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
          (SourcePairedInclusion.data q hq n r).X u x i) x ∧
      Decomp (3 * K * ‖u‖) (K * ‖u‖)
        (fun i => SourcePairedPlaneMagnetic.magneticReactionField (SourcePairedInclusion.shell q hq n r) ci
          (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
          (SourcePairedInclusion.data q hq n r).X u x i) x := by
  have hbase := base_pos
  set B : ℝ := max 1 (HarmonicSpatialMajorant.degreeScale 2 b) with hBdef
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := by linarith
  have hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B := le_max_right _ _
  have hb0 : 0 < B * AngularExteriorBounds.base := mul_pos (by linarith) hbase
  have hρ1a : 1 ≤ ρ1 := (le_max_left _ _).trans hρ1
  have hρ1b : 2 * ((B * AngularExteriorBounds.base) * Real.exp (8 * HankelIntermediateBounds.exponent q)) ≤ ρ1 :=
    (le_max_right _ _).trans hρ1
  have hρ1pos : 0 < ρ1 := by linarith
  obtain ⟨C, hC0, hCev⟩ := shell_degree_majorant q hq n (B * AngularExteriorBounds.base) ρ1 hb0 hρ1a hρ1b
  set K0 : ℝ := ∑' a, regConst b 1 C a with hK0
  have hK00 : 0 ≤ K0 := tsum_nonneg (regConst_nonneg b 1 C hb zero_le_one hC0)
  refine ⟨massConst ci d * K0, mul_nonneg (massConst_nonneg ci d) hK00, ?_⟩
  filter_upwards [hCev, RadialPhaseLimit.radius_tendsto.eventually
    (eventually_gt_atTop (max (max 2 (2*(B * AngularExteriorBounds.base))) b))] with r hr hR
  intro u x hx1 hxR
  have hRR : max (max 2 (2*(B * AngularExteriorBounds.base))) b < (SourcePairedInclusion.data q hq n r).R := hR
  have hT2 : 2 ≤ max 2 (2*(B * AngularExteriorBounds.base)) := le_max_left _ _
  have hBT : 2*(B * AngularExteriorBounds.base) ≤ max 2 (2*(B * AngularExteriorBounds.base)) := le_max_right _ _
  have hTR : max 2 (2*(B * AngularExteriorBounds.base)) < (SourcePairedInclusion.data q hq n r).R :=
    (le_max_left _ _).trans_lt hRR
  have hbR : b < (SourcePairedInclusion.data q hq n r).R := (le_max_right _ _).trans_lt hRR
  have hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0 :=
    fun y hy => d.carrierZero y (fun hc => hy (mem_closedBall_zero_iff.mpr (hcar y hc)))
  have hmass := mass_source_le ci d u
  have hsumeq : ∑' a, regConst b (massConst ci d * ‖u‖) C a = massConst ci d * K0 * ‖u‖ := by
    have : (fun a => regConst b (massConst ci d * ‖u‖) C a) =
        fun a => (massConst ci d * ‖u‖) * regConst b 1 C a := funext fun a => by unfold regConst; ring
    rw [this, tsum_mul_left]
    ring
  have e3 : 3 * (massConst ci d * K0) * ‖u‖ = 3 * (massConst ci d * K0 * ‖u‖) := by ring
  have hΘtm := fun (a : PositiveIndex) (s : ℝ) (h1 : ρ1 ≤ s) (h2 : s ≤ (SourcePairedInclusion.data q hq n r).R) =>
    (hr a s h1 h2).1
  have hΘte := fun (a : PositiveIndex) (s : ℝ) (h1 : ρ1 ≤ s) (h2 : s ≤ (SourcePairedInclusion.data q hq n r).R) =>
    (hr a s h1 h2).2
  refine ⟨?_, ?_⟩
  · have E := reaction_electric_decomp q hq n r b B (max 2 (2*(B * AngularExteriorBounds.base))) ρ1 C
      (massConst ci d * ‖u‖) hb hB0 hscale hT2 hBT hTR hbR hC0 hρ1pos hΘtm hΘte ci u hci hmass x hx1.le hxR
    rw [hsumeq, ← e3] at E
    exact E
  · have E := reaction_magnetic_decomp q hq n r b B (max 2 (2*(B * AngularExteriorBounds.base))) ρ1 C
      (massConst ci d * ‖u‖) hb hB0 hscale hT2 hBT hTR hbR hC0 hρ1pos hΘtm hΘte ci u hci hmass x hx1 hxR
    rw [hsumeq, ← e3] at E
    exact E

end OQ14.CoreReaction

#print axioms OQ14.CoreReaction.tm_parameters
#print axioms OQ14.CoreReaction.te_parameters
#print axioms OQ14.CoreReaction.shell_degree_majorant
#print axioms OQ14.CoreReaction.term_eq'
#print axioms OQ14.CoreReaction.term_bound'
#print axioms OQ14.CoreReaction.continuous_term_y'
#print axioms OQ14.CoreReaction.unit_bound
#print axioms OQ14.CoreReaction.reactionField_hasSum
#print axioms OQ14.CoreReaction.weakOn_mono
#print axioms OQ14.CoreReaction.fieldPair_ae_congr
#print axioms OQ14.CoreReaction.weak_free_interior
#print axioms OQ14.CoreReaction.magnetic_hollow_continuousAt
#print axioms OQ14.CoreReaction.shellSource_props
#print axioms OQ14.CoreReaction.weak_reaction
#print axioms OQ14.CoreReaction.magneticReaction_continuousAt
#print axioms OQ14.CoreReaction.moment_mul_bound
#print axioms OQ14.CoreReaction.reaction_electric_decomp
#print axioms OQ14.CoreReaction.reaction_magnetic_hasSum
#print axioms OQ14.CoreReaction.reaction_magnetic_decomp
#print axioms OQ14.CoreReaction.base_pos
#print axioms OQ14.CoreReaction.massConst_nonneg
#print axioms OQ14.CoreReaction.mass_source_le
#print axioms OQ14.CoreReaction.reaction_core_decomp
