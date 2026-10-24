import SourcePairedPlaneIdentification
import OutgoingFreeDyadic
import SourceModeInverse
import SourceExteriorSmooth
import ExteriorMaterial
import RiccatiGaussianBound

/-! The mode-series representation of the field radiated by an inclusion source outside the paired
shell.  The free field of a compactly supported current density is the series over the positive degrees
and real modes of the moments of the current against the regular dyad coefficients times the vacuum
outgoing modes (with interchange of the sum and the source integral).  The shell datum of an inclusion
source is the corresponding series of the weighted shell mode data in the material Hilbert space, the
shell solution is the series of the mode solutions, and outside the shell the field of the shell
polarization is the series of the moments times the actual regular corrections of the layered modes, at
every point by continuity.  Adding the free and shell parts gives the series of the moments times the
actual layered TM electric mode and the actual layered TE electric mode of the TE chain.  Finally the
moments satisfy explicit bounds against the regular Riccati value at an inner scale. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.SourceRadiatedSeries
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.SphereHarmonicBasis
open OQ14.VectorHarmonicNormalization
open scoped Topology

/-- The transverse-magnetic moment of a current density: the pairing with the regular dyad coefficient. -/
def tmMoment (a : PositiveIndex) (ρ : Fin 3 → Space → ℂ) : ℂ :=
  ∑ j, ∫ y, FreeSourceCoefficients.tmCoefficient a y j * ρ j y

/-- The transverse-electric moment of a current density. -/
def teMoment (a : PositiveIndex) (ρ : Fin 3 → Space → ℂ) : ℂ :=
  ∑ j, ∫ y, FreeSourceCoefficients.teCoefficient a y j * ρ j y

theorem electric_coefficient_continuous (a : PositiveIndex) (j : Fin 3) :
    Continuous fun y => DebyeUnitReaction.electric a y j := by
  rw [continuous_iff_continuousAt]
  intro x
  have hf : ContDiffAt ℝ (⊤ : ℕ∞)
      (SolidScalarHelmholtz.wave (a.1+1) 1 (representative (a.1+1) a.2)) x :=
    (SolidScalarHelmholtz.wave_contDiff _ _ _).contDiffAt
  exact (ExteriorClassical.curl_smooth (DebyeCalculus.toroidal _)
    (fun k => DebyeCalculus.toroidal_smooth _ x hf k) j).continuousAt

theorem toroidal_coefficient_continuous (a : PositiveIndex) (j : Fin 3) :
    Continuous fun y => DebyeUnitReaction.toroidal a y j := by
  rw [continuous_iff_continuousAt]
  intro x
  have hf : ContDiffAt ℝ (⊤ : ℕ∞)
      (SolidScalarHelmholtz.wave (a.1+1) 1 (representative (a.1+1) a.2)) x :=
    (SolidScalarHelmholtz.wave_contDiff _ _ _).contDiffAt
  exact (DebyeCalculus.toroidal_smooth _ x hf j).continuousAt

theorem tmCoefficient_continuous (a : PositiveIndex) (j : Fin 3) :
    Continuous fun y => FreeSourceCoefficients.tmCoefficient a y j := by
  unfold FreeSourceCoefficients.tmCoefficient
  exact continuous_const.mul (electric_coefficient_continuous a j)

theorem teCoefficient_continuous (a : PositiveIndex) (j : Fin 3) :
    Continuous fun y => FreeSourceCoefficients.teCoefficient a y j := by
  unfold FreeSourceCoefficients.teCoefficient
  exact continuous_const.mul (toroidal_coefficient_continuous a j)

theorem coefficient_mul_integrable {c ρ : Space → ℂ} (hc : Continuous c)
    (hρ : Integrable ρ volume) (b : ℝ) (hsupp : ∀ y, b < ‖y‖ → ρ y = 0) :
    Integrable (fun y => c y * ρ y) volume := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Space) b).exists_bound_of_continuousOn hc.continuousOn
  refine Integrable.mono' (hρ.norm.const_mul (max C 0))
    (hc.aestronglyMeasurable.mul hρ.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  by_cases hy : ‖y‖ ≤ b
  · rw [norm_mul]
    have h1 := hC y (by simpa using hy)
    exact mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) (norm_nonneg _)
  · rw [hsupp y (not_le.mp hy)]
    simp

theorem majorant_nonneg (b R : ℝ) (hb : 0 ≤ b) (a : PositiveIndex) :
    0 ≤ OutgoingGeometricTail.majorant b R a := by
  have h := OutgoingGeometricTail.prefactor_nonnegative b R hb
  unfold OutgoingGeometricTail.majorant
  positivity

/-- The vacuum electric mode of degree `a.1+1` and the vacuum TE mode, combined with the coefficients
of the free dyad at the source point `y`, give the term of the outgoing spatial series. -/
theorem term_eq (a : PositiveIndex) (x y : Space) (i j : Fin 3) :
    OutgoingSpatialSeries.term a x y i j =
      FreeSourceCoefficients.tmCoefficient a y j * SourceUnclippedMaxwell.electric
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
      FreeSourceCoefficients.teCoefficient a y j * SourceUnclippedMaxwell.magnetic
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i := rfl

theorem term_continuous_in_source (a : PositiveIndex) (x : Space) (i j : Fin 3) :
    Continuous fun y => OutgoingSpatialSeries.term a x y i j := by
  simp only [term_eq]
  exact ((tmCoefficient_continuous a j).mul continuous_const).add
    ((teCoefficient_continuous a j).mul continuous_const)

theorem component_hasSum (b B R : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (x : Space) (hx : max R b < ‖x‖) (i j : Fin 3) :
    HasSum (fun a : PositiveIndex => ∫ y, ρ j y * OutgoingSpatialSeries.term a x y i j)
      (KernelConvolution.response (fun z => DyadicKernel.dyadic 1 z i j) (ρ j) x) := by
  have hxR : R ≤ ‖x‖ := ((le_max_left _ _).trans hx.le)
  have hxR' : R < ‖x‖ := ((le_max_left _ _).trans_lt hx)
  have hxb : b < ‖x‖ := ((le_max_right _ _).trans_lt hx)
  unfold KernelConvolution.response
  refine hasSum_integral_of_dominated_convergence
    (fun a y => ‖ρ j y‖ * OutgoingGeometricTail.majorant b R a) ?_ ?_ ?_ ?_ ?_
  · intro a
    exact (hρ j).aestronglyMeasurable.mul (term_continuous_in_source a x i j).aestronglyMeasurable
  · intro a
    refine Eventually.of_forall fun y => ?_
    by_cases hy : ‖y‖ ≤ b
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (OutgoingSpatialSeries.term_bound a b B R hb hB hscale hR hBR x y hxR hy i j) (norm_nonneg _)
    · rw [hsupp j y (not_le.mp hy)]
      simp only [zero_mul, norm_zero]
      exact mul_nonneg (norm_nonneg _) (majorant_nonneg b R hb a)
  · exact Eventually.of_forall fun y =>
      (OutgoingGeometricTail.majorant_summable b R hb).mul_left _
  · have : (fun y => ∑' a, ‖ρ j y‖ * OutgoingGeometricTail.majorant b R a) =
        fun y => ‖ρ j y‖ * ∑' a, OutgoingGeometricTail.majorant b R a := by
      funext y
      rw [tsum_mul_left]
    rw [this]
    exact (hρ j).norm.mul_const _
  · refine Eventually.of_forall fun y => ?_
    by_cases hy : ‖y‖ ≤ b
    · have hs := OutgoingSpatialSeries.term_summable b B R hb hB hscale hR hBR x y hxR hy i j
      have hd := OutgoingFreeDyadic.actual_free_dyadic b B R hb hB hscale hR hBR y hy i j x
        (max_lt hxR' (hy.trans_lt hxb))
      have : HasSum (fun a => ρ j y * OutgoingSpatialSeries.term a x y i j)
          (ρ j y * ∑' a, OutgoingSpatialSeries.term a x y i j) := hs.hasSum.mul_left _
      rw [OutgoingSpatialSeries.electric] at *
      convert this using 2
      exact hd.symm
    · rw [hsupp j y (not_le.mp hy)]
      simp only [zero_mul]
      exact hasSum_zero

theorem integral_term_split (b : ℝ) (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (a : PositiveIndex) (x : Space) (i j : Fin 3) :
    ∫ y, ρ j y * OutgoingSpatialSeries.term a x y i j =
      (∫ y, FreeSourceCoefficients.tmCoefficient a y j * ρ j y) * SourceUnclippedMaxwell.electric
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
      (∫ y, FreeSourceCoefficients.teCoefficient a y j * ρ j y) * SourceUnclippedMaxwell.magnetic
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i := by
  have h1 := coefficient_mul_integrable (tmCoefficient_continuous a j) (hρ j) b (hsupp j)
  have h2 := coefficient_mul_integrable (teCoefficient_continuous a j) (hρ j) b (hsupp j)
  have : (fun y => ρ j y * OutgoingSpatialSeries.term a x y i j) =
      fun y => (FreeSourceCoefficients.tmCoefficient a y j * ρ j y) * SourceUnclippedMaxwell.electric
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
      (FreeSourceCoefficients.teCoefficient a y j * ρ j y) * SourceUnclippedMaxwell.magnetic
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i := by
    funext y
    rw [term_eq]
    ring
  rw [this, integral_add (h1.mul_const _) (h2.mul_const _), integral_mul_const, integral_mul_const]

/-- The free field of a compactly supported integrable current density, outside the support and the
threshold radius `R`, is the sum of the vacuum mode series with the moments of the current against the
regular dyad coefficients as coefficients. -/
theorem free_field_series_outside (b B R : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (x : Space) (hx : max R b < ‖x‖) (i : Fin 3) :
    HasSum (fun a : PositiveIndex =>
      tmMoment a ρ * SourceUnclippedMaxwell.electric
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
      teMoment a ρ * SourceUnclippedMaxwell.magnetic
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i)
      (ExteriorContinuity.electric 1 ρ x i) := by
  have h := hasSum_sum (s := Finset.univ) (fun j _ => component_hasSum b B R hb hB hscale hR hBR ρ hρ
    hsupp x hx i j)
  have hfun : (fun a : PositiveIndex => ∑ j : Fin 3, ∫ y, ρ j y * OutgoingSpatialSeries.term a x y i j) =
      fun a : PositiveIndex =>
      tmMoment a ρ * SourceUnclippedMaxwell.electric
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
      teMoment a ρ * SourceUnclippedMaxwell.magnetic
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i := by
    funext a
    simp only [integral_term_split b ρ hρ hsupp a x i, Finset.sum_add_distrib, tmMoment, teMoment,
      Finset.sum_mul]
  rw [hfun] at h
  exact h

theorem free_field_series_outside_tsum (b B R : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hR : 2 ≤ R)
    (hBR : 2*(B*AngularExteriorBounds.base) ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (x : Space) (hx : max R b < ‖x‖) (i : Fin 3) :
    ExteriorContinuity.electric 1 ρ x i = ∑' a : PositiveIndex,
      (tmMoment a ρ * SourceUnclippedMaxwell.electric
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
      teMoment a ρ * SourceUnclippedMaxwell.magnetic
        (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i) :=
  (free_field_series_outside b B R hb hB hscale hR hBR ρ hρ hsupp x hx i).tsum_eq.symm

/-! ### The shell datum of an inclusion source as a series of the shell mode data -/

abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

/-- The operator-norm constant of the weighted datum map on the shell annulus. -/
def datumBound (c : Coefficient) (R X : ℝ) : ℝ :=
  ∑ i : Fin 3, ‖(DynamicConvolution.insert i).comp (WeightedAnnulusDatum.scalarMap c R X)‖

theorem datumBound_nonneg (c : Coefficient) (R X : ℝ) : 0 ≤ datumBound c R X :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem datum_norm_le (c : Coefficient) (R X : ℝ)
    (f : Fin 3 → C(WeightedAnnulusDatum.annulus R X, ℂ)) (M : ℝ) (hf : ∀ i, ‖f i‖ ≤ M) :
    ‖FreeDyadicMaterialData.datum c R X f‖ ≤ datumBound c R X * M := by
  unfold FreeDyadicMaterialData.datum datumBound
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h := ((DynamicConvolution.insert i).comp (WeightedAnnulusDatum.scalarMap c R X)).le_opNorm (f i)
  exact h.trans (mul_le_mul_of_nonneg_left (hf i) (norm_nonneg _))

theorem mode_norm_le (b B T R X : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hT : 2 ≤ T)
    (hBT : 2*(B*AngularExteriorBounds.base) ≤ T) (hR : 0 < R) (hTR : T < R)
    (a : PositiveIndex) (y : Space) (hy : ‖y‖ ≤ b) (i j : Fin 3) :
    ‖FreeDyadicMaterialData.mode R X hR a y i j‖ ≤ OutgoingGeometricTail.majorant b T a := by
  have hM := majorant_nonneg b T hb a
  rw [ContinuousMap.norm_le _ hM]
  intro x
  exact OutgoingSpatialSeries.term_bound a b B T hb hB hscale hT hBT x y
    (hTR.le.trans (FreeDyadicMaterialData.annulus_inner R X x)) hy i j

/-- The weighted dipole datum of the shell mode `a` at the source point `y`, in the form of the
polarization combination of the two incident mode data. -/
theorem mode_datum_eq (cs : Coefficient) (d : SourceRadialSystem.Data)
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (hi : ∀ x : Space, ‖x‖ ≤ d.R → cs.value (VectorFourier.coordinateMap x) = 0)
    (a : PositiveIndex) (y : Space) (j : Fin 3) :
    FreeDyadicMaterialData.datum cs d.R d.X (fun i => FreeDyadicMaterialData.mode d.R d.X d.hR a y i j) =
      FreeSourceCoefficients.tmCoefficient a y j • SourceModeDatum.tmIncident cs d hc a +
        FreeSourceCoefficients.teCoefficient a y j • SourceModeDatum.teIncident cs d hc a :=
  SourceModeDatum.mode_eq cs d hc hi a y j

theorem integral_mode_datum (cs : Coefficient) (d : SourceRadialSystem.Data)
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (b : ℝ) (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (a : PositiveIndex) :
    ∫ y, ∑ j : Fin 3, ρ j y • (FreeSourceCoefficients.tmCoefficient a y j •
          SourceModeDatum.tmIncident cs d hc a +
        FreeSourceCoefficients.teCoefficient a y j • SourceModeDatum.teIncident cs d hc a) =
      tmMoment a ρ • SourceModeDatum.tmIncident cs d hc a +
        teMoment a ρ • SourceModeDatum.teIncident cs d hc a := by
  have h1 (j : Fin 3) := coefficient_mul_integrable (tmCoefficient_continuous a j) (hρ j) b (hsupp j)
  have h2 (j : Fin 3) := coefficient_mul_integrable (teCoefficient_continuous a j) (hρ j) b (hsupp j)
  have hfun : (fun y => ∑ j : Fin 3, ρ j y • (FreeSourceCoefficients.tmCoefficient a y j •
          SourceModeDatum.tmIncident cs d hc a +
        FreeSourceCoefficients.teCoefficient a y j • SourceModeDatum.teIncident cs d hc a)) =
      fun y => (∑ j : Fin 3, FreeSourceCoefficients.tmCoefficient a y j * ρ j y) •
          SourceModeDatum.tmIncident cs d hc a +
        (∑ j : Fin 3, FreeSourceCoefficients.teCoefficient a y j * ρ j y) •
          SourceModeDatum.teIncident cs d hc a := by
    funext y
    simp only [smul_add, smul_smul, Finset.sum_add_distrib, Finset.sum_smul]
    congr 1 <;> exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  rw [hfun, integral_add, integral_smul_const, integral_smul_const]
  · congr 1
    · congr 1
      rw [integral_finset_sum _ fun j _ => h1 j]
      rfl
    · congr 1
      rw [integral_finset_sum _ fun j _ => h2 j]
      rfl
  · exact (integrable_finset_sum _ fun j _ => h1 j).smul_const _
  · exact (integrable_finset_sum _ fun j _ => h2 j).smul_const _

/-- **The shell datum of an inclusion source is the series of the mode data.**  The sandwich
`Ss T Si v` of an inclusion vector `v` equals, in `VectorL2`, the sum over the positive degrees and
real modes of the moments of the inclusion source against the free-dyad coefficients, times the weighted
data of the TM and TE vacuum modes. -/
theorem shell_datum_series (cs ci : Coefficient) (d : SourceRadialSystem.Data) (b B T : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hT : 2 ≤ T)
    (hBT : 2*(B*AngularExteriorBounds.base) ≤ T) (hTR : T < d.R) (hbR : b < d.R)
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (hi : ∀ x : Space, ‖x‖ ≤ d.R → cs.value (VectorFourier.coordinateMap x) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (v : VectorL2) :
    HasSum (fun a : PositiveIndex =>
      tmMoment a (fun j => DynamicVolume.source ci v j) • SourceModeDatum.tmIncident cs d hc a +
        teMoment a (fun j => DynamicVolume.source ci v j) • SourceModeDatum.teIncident cs d hc a)
      (StaticCoefficient.sqrtMultiplier cs
        (ShellInclusionVolume.kernel 1 d.X (StaticCoefficient.sqrtMultiplier ci v))) := by
  have hρ : ∀ j, Integrable (DynamicVolume.source ci v j) volume :=
    fun j => DynamicVolume.source_integrable ci v b hci j
  have hsupp : ∀ j y, b < ‖y‖ → DynamicVolume.source ci v j y = 0 := fun j y hy =>
    DynamicVolume.source_zero ci v b hci j y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy)
  have hRX : d.R ≤ d.X := RadialStack.chain_ordered d.chain
  have hcs : ∀ y : Space, y ∉ closedBall (0 : Space) d.X \ ball (0 : Space) d.R →
      cs.value (VectorFourier.coordinateMap y) = 0 := SourceModeDatum.annulus_support cs d hc hi
  rw [SourcePairedPlaneIdentification.freeDatum_integral cs ci b d.R d.X d.X hbR hRX le_rfl hcs hci v]
  have hmain := hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun (a : PositiveIndex) (y : Space) => ∑ j : Fin 3, DynamicVolume.source ci v j y •
      (FreeSourceCoefficients.tmCoefficient a y j • SourceModeDatum.tmIncident cs d hc a +
        FreeSourceCoefficients.teCoefficient a y j • SourceModeDatum.teIncident cs d hc a))
    (f := fun y => ∑ j : Fin 3, DynamicVolume.source ci v j y •
      ShellReactionIdentification.freeDatum cs d.R d.X y j)
    (fun a y => (∑ j : Fin 3, ‖DynamicVolume.source ci v j y‖) *
      (datumBound cs d.R d.X * OutgoingGeometricTail.majorant b T a))
    ?meas ?bound ?bsum ?bint ?lim
  · have hfun : (fun a : PositiveIndex => ∫ y, ∑ j : Fin 3, DynamicVolume.source ci v j y •
        (FreeSourceCoefficients.tmCoefficient a y j • SourceModeDatum.tmIncident cs d hc a +
          FreeSourceCoefficients.teCoefficient a y j • SourceModeDatum.teIncident cs d hc a)) =
        fun a : PositiveIndex =>
      tmMoment a (fun j => DynamicVolume.source ci v j) • SourceModeDatum.tmIncident cs d hc a +
        teMoment a (fun j => DynamicVolume.source ci v j) • SourceModeDatum.teIncident cs d hc a :=
      funext fun a => integral_mode_datum cs d hc b (fun j => DynamicVolume.source ci v j) hρ hsupp a
    rw [hfun] at hmain
    exact hmain
  case meas =>
    intro a
    refine Finset.aestronglyMeasurable_sum _ fun j _ => ?_
    exact (hρ j).aestronglyMeasurable.smul
      (((tmCoefficient_continuous a j).smul continuous_const).add
        ((teCoefficient_continuous a j).smul continuous_const)).aestronglyMeasurable
  case bound =>
    intro a
    refine Eventually.of_forall fun y => ?_
    have hCn := datumBound_nonneg cs d.R d.X
    have hMn := majorant_nonneg b T hb a
    beta_reduce
    by_cases hy : ‖y‖ ≤ b
    · refine (norm_sum_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [← mode_datum_eq cs d hc hi a y j]
      exact datum_norm_le cs d.R d.X _ _ fun i =>
        mode_norm_le b B T d.R d.X hb hB hscale hT hBT d.hR hTR a y hy i j
    · have h0 : ∀ j, DynamicVolume.source ci v j y = 0 := fun j => hsupp j y (not_le.mp hy)
      simp [h0]
  case bsum =>
    exact Eventually.of_forall fun y =>
      ((OutgoingGeometricTail.majorant_summable b T hb).mul_left (datumBound cs d.R d.X)).mul_left _
  case bint =>
    have hfun : (fun y => ∑' a : PositiveIndex, (∑ j : Fin 3, ‖DynamicVolume.source ci v j y‖) *
        (datumBound cs d.R d.X * OutgoingGeometricTail.majorant b T a)) =
        fun y => (∑ j : Fin 3, ‖DynamicVolume.source ci v j y‖) *
          (datumBound cs d.R d.X * ∑' a : PositiveIndex, OutgoingGeometricTail.majorant b T a) := by
      funext y
      rw [tsum_mul_left, tsum_mul_left]
    rw [hfun]
    exact (integrable_finset_sum _ fun j _ => (hρ j).norm).mul_const _
  case lim =>
    refine Eventually.of_forall fun y => ?_
    by_cases hy : ‖y‖ ≤ b
    · have hyR : ‖y‖ < d.R := hy.trans_lt hbR
      have hj : ∀ j : Fin 3, HasSum (fun a : PositiveIndex => DynamicVolume.source ci v j y •
          (FreeSourceCoefficients.tmCoefficient a y j • SourceModeDatum.tmIncident cs d hc a +
            FreeSourceCoefficients.teCoefficient a y j • SourceModeDatum.teIncident cs d hc a))
          (DynamicVolume.source ci v j y • ShellReactionIdentification.freeDatum cs d.R d.X y j) := by
        intro j
        have h := FreeDyadicMaterialData.datum_hasSum cs b B T d.R d.X hb hB hscale hT hBT d.hR hTR
          y hy hyR j
        simp only [mode_datum_eq cs d hc hi] at h
        have e : ShellReactionIdentification.freeDatum cs d.R d.X y j =
            FreeDyadicMaterialData.datum cs d.R d.X
              (fun i => FreeDyadicMaterialData.free d.R d.X y hyR i j) := by
          unfold ShellReactionIdentification.freeDatum
          rw [dif_pos hyR]
        rw [e]
        exact h.const_smul _
      exact hasSum_sum fun j _ => hj j
    · have h0 : ∀ j, DynamicVolume.source ci v j y = 0 := fun j => hsupp j y (not_le.mp hy)
      simp only [h0, zero_smul, Finset.sum_const_zero]
      exact hasSum_zero

/-- The shell solution driven by the shell datum of an inclusion source is the series of the shell
solutions of the TM and TE vacuum mode data. -/
theorem shell_solution_series (cs ci : Coefficient) (d : SourceRadialSystem.Data) (b B T : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hT : 2 ≤ T)
    (hBT : 2*(B*AngularExteriorBounds.base) ≤ T) (hTR : T < d.R) (hbR : b < d.R)
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (hi : ∀ x : Space, ‖x‖ ≤ d.R → cs.value (VectorFourier.coordinateMap x) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (v : VectorL2) :
    HasSum (fun a : PositiveIndex =>
      tmMoment a (fun j => DynamicVolume.source ci v j) •
          MaterialField.solution cs 1 d.X (SourceModeDatum.tmIncident cs d hc a) +
        teMoment a (fun j => DynamicVolume.source ci v j) •
          MaterialField.solution cs 1 d.X (SourceModeDatum.teIncident cs d hc a))
      (MaterialField.solution cs 1 d.X (StaticCoefficient.sqrtMultiplier cs
        (ShellInclusionVolume.kernel 1 d.X (StaticCoefficient.sqrtMultiplier ci v)))) := by
  have h := (shell_datum_series cs ci d b B T hb hB hscale hT hBT hTR hbR hc hi hci v).mapL
    (Ring.inverse (DynamicVolume.volumeBlock cs 1 d.X))
  simpa only [map_add, map_smul] using h

/-- For an observation point outside the shell the evaluation of the field of the shell polarization
is a bounded linear functional of the shell vector. -/
theorem exists_exterior_functional (cs : Coefficient) (Rin X : ℝ)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (x : Space) (hx : X < ‖x‖) (i : Fin 3) :
    ∃ Φ : VectorL2 →L[ℂ] ℂ, ∀ w : VectorL2,
      Φ w = ExteriorContinuity.electric 1 (DynamicVolume.source cs w) x i := by
  let dd := CoreMaterialEvaluation.supportData cs Rin X hcs
  have hne (y : Space) (hy : y ∈ CoreMaterialEvaluation.annulus Rin X) : x - y ≠ 0 := by
    intro h0
    have h1 : x = y := sub_eq_zero.mp h0
    have : ‖y‖ ≤ X := by simpa using hy.1
    rw [h1] at hx
    linarith
  have hcont (j : Fin 3) : ContinuousOn (fun y => DyadicKernel.dyadic 1 (x - y) i j)
      (CoreMaterialEvaluation.annulus Rin X) := fun y hy =>
    ((ExteriorContinuity.dyadic_continuousAt 1 i j (x - y) (hne y hy)).comp
      (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
  choose C hC using fun j : Fin 3 =>
    (CoreMaterialEvaluation.annulus_compact Rin X).exists_bound_of_continuousOn (hcont j)
  refine ⟨∑ j : Fin 3, SourcePairedPlaneIdentification.kernelFunctional cs dd
    (fun z => DyadicKernel.dyadic 1 z i j) (DyadicRadiation.dyadic_measurable 1 i j) x (max 0 (C j))
    (fun y hy => (hC j y hy).trans (le_max_right _ _)) (le_max_left _ _) j, ?_⟩
  intro w
  simp only [ContinuousLinearMap.sum_apply, SourcePairedPlaneIdentification.kernelFunctional_apply]
  rfl

/-- Two fields that agree almost everywhere and are continuous on the exterior of the ball of radius `X`
agree at every point of the exterior. -/
theorem eq_of_ae_exterior (X : ℝ) (f g : Space → ℂ) (hae : f =ᵐ[volume] g)
    (hf : ∀ x : Space, X < ‖x‖ → ContinuousAt f x) (hg : ∀ x : Space, X < ‖x‖ → ContinuousAt g x)
    (x : Space) (hx : X < ‖x‖) : f x = g x :=
  MeasureTheory.Measure.eqOn_open_of_ae_eq (μ := volume) (U := {z : Space | X < ‖z‖})
    (ae_restrict_of_ae hae) (isOpen_lt continuous_const continuous_norm)
    (fun z hz => (hf z hz).continuousWithinAt) (fun z hz => (hg z hz).continuousWithinAt) hx

/-- **Exterior field of a TM shell mode.**  Outside the shell the literal electric field of the
polarization of the shell solution driven by the weighted TM vacuum mode datum is the actual regular
correction (layered minus vacuum) of the TM mode, pointwise. -/
theorem exterior_tm_mode (cs : Coefficient) (d : SourceRadialSystem.Data)
    (hm : ∀ x : Space, (cs.value (VectorFourier.coordinateMap x) : ℂ) = SourceRadialSystem.sigma d ‖x‖ - 1)
    (hdisp : ∀ g ∈ d.gs, g.q^2 = g.σ) (hu : IsUnit (DynamicVolume.volumeBlock cs 1 d.X))
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (a : PositiveIndex) (x : Space) (hx : d.X < ‖x‖) (i : Fin 3) :
    ExteriorContinuity.electric 1 (DynamicVolume.source cs
      (MaterialField.solution cs 1 d.X (SourceModeDatum.tmIncident cs d hc a))) x i =
      SourceRegularCorrection.electric (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i := by
  have hw := SourceModeInverse.tm_inverse cs d hm hdisp hu hc a
  have hae := SourceMaterialResponse.scattered_actual cs (SourceDielectricModes.tmData d (a.1+1)) hm hdisp
    (representative (a.1+1) a.2) (representative_homogeneous _ _) (representative_harmonic _ _)
  rw [hw]
  have hsc := ExteriorMaterial.scattered_ae cs 1 d.X
    (SourceWeightedDatum.datum cs d.X hc (SourceDielectricModes.tmData d (a.1+1))
      (representative (a.1+1) a.2)) hc
  have hcont := fun z (hz : d.X < ‖z‖) => ExteriorMaterial.scattered_continuousAt cs 1 d.X
    (SourceWeightedDatum.datum cs d.X hc (SourceDielectricModes.tmData d (a.1+1))
      (representative (a.1+1) a.2)) hc z hz
  have h := eq_of_ae_exterior d.X (fun z => ExteriorMaterial.scattered cs 1 d.X
      (SourceWeightedDatum.datum cs d.X hc (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2)) z i)
    (fun z => SourceRegularCorrection.electric (SourceDielectricModes.tmData d (a.1+1))
      (representative (a.1+1) a.2) z i)
    ?_ (fun z hz => (continuousAt_pi.mp (hcont z hz)) i)
    (fun z hz => (SourceExteriorSmooth.correction_electric_smooth (SourceDielectricModes.tmData d (a.1+1))
      (representative (a.1+1) a.2) (representative_homogeneous _ _) (representative_harmonic _ _)
      z hz i).continuousAt) x hx
  · refine Eq.trans ?_ h
    show _ = ExteriorMaterial.scattered cs 1 d.X _ x i
    rw [ExteriorMaterial.scattered_exterior cs 1 d.X _ x hx i]
    rfl
  · filter_upwards [hsc, hae] with z h1 h2
    have := congrFun h1 i
    rw [this]
    exact congrFun h2 i

/-- **Exterior field of a TE shell mode.**  The same statement for the weighted TE vacuum mode datum:
the exterior field of the polarization of the shell solution is the actual TE regular correction. -/
theorem exterior_te_mode (cs : Coefficient) (d : SourceRadialSystem.Data)
    (hm : ∀ x : Space, (cs.value (VectorFourier.coordinateMap x) : ℂ) = SourceRadialSystem.sigma d ‖x‖ - 1)
    (hdisp : ∀ g ∈ d.gs, g.q^2 = g.σ) (hu : IsUnit (DynamicVolume.volumeBlock cs 1 d.X))
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (a : PositiveIndex) (x : Space) (hx : d.X < ‖x‖) (i : Fin 3) :
    ExteriorContinuity.electric 1 (DynamicVolume.source cs
      (MaterialField.solution cs 1 d.X (SourceModeDatum.teIncident cs d hc a))) x i =
      SourceTECorrection.electric (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i := by
  have hw := SourceModeInverse.te_inverse cs d hm hdisp hu hc a
  have hmu (z : Space) : (cs.value (VectorFourier.coordinateMap z) : ℂ) =
      SourceGeneralMaxwell.mu (SourceDielectricModes.teData d (a.1+1)) ‖z‖ - 1 := by
    rw [SourceDielectricModes.te_mu d hdisp, hm]
  have hae := SourceTEMaterialResponse.scattered_actual cs (SourceDielectricModes.teData d (a.1+1)) hmu
    (SourceDielectricModes.te_sigma d _)
    (representative (a.1+1) a.2) (representative_homogeneous _ _) (representative_harmonic _ _)
  rw [hw]
  have hsc := ExteriorMaterial.scattered_ae cs 1 d.X
    (SourceTEWeightedDatum.datum cs d.X hc (SourceDielectricModes.teData d (a.1+1))
      (representative (a.1+1) a.2)) hc
  have hcont := fun z (hz : d.X < ‖z‖) => ExteriorMaterial.scattered_continuousAt cs 1 d.X
    (SourceTEWeightedDatum.datum cs d.X hc (SourceDielectricModes.teData d (a.1+1))
      (representative (a.1+1) a.2)) hc z hz
  have h := eq_of_ae_exterior d.X (fun z => ExteriorMaterial.scattered cs 1 d.X
      (SourceTEWeightedDatum.datum cs d.X hc (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2)) z i)
    (fun z => SourceTECorrection.electric (SourceDielectricModes.teData d (a.1+1))
      (representative (a.1+1) a.2) z i)
    ?_ (fun z hz => (continuousAt_pi.mp (hcont z hz)) i)
    (fun z hz => (SourceExteriorSmooth.correction_magnetic_smooth (SourceDielectricModes.teData d (a.1+1))
      (representative (a.1+1) a.2) z hz i).continuousAt) x hx
  · refine Eq.trans ?_ h
    show _ = ExteriorMaterial.scattered cs 1 d.X _ x i
    rw [ExteriorMaterial.scattered_exterior cs 1 d.X _ x hx i]
    rfl
  · filter_upwards [hsc, hae] with z h1 h2
    have := congrFun h1 i
    rw [this]
    exact congrFun h2 i

/-- **The reaction field of the shell outside the shell as a series.**  Outside the shell, at every point
`x` with `d.X < ‖x‖`, the electric field of the polarization of the shell solution driven by the shell
datum `Ss T Si v` of an inclusion vector `v` is the sum, over the positive degrees and real modes, of the
moments of the inclusion source against the TM and TE free-dyad coefficients times the actual regular
corrections (layered mode minus vacuum mode) of the shell modes. -/
theorem shell_reaction_series_outside (cs ci : Coefficient) (d : SourceRadialSystem.Data) (b B T : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hT : 2 ≤ T)
    (hBT : 2*(B*AngularExteriorBounds.base) ≤ T) (hTR : T < d.R) (hbR : b < d.R)
    (hm : ∀ x : Space, (cs.value (VectorFourier.coordinateMap x) : ℂ) = SourceRadialSystem.sigma d ‖x‖ - 1)
    (hdisp : ∀ g ∈ d.gs, g.q^2 = g.σ) (hu : IsUnit (DynamicVolume.volumeBlock cs 1 d.X))
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (hi : ∀ x : Space, ‖x‖ ≤ d.R → cs.value (VectorFourier.coordinateMap x) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (v : VectorL2) (x : Space) (hx : d.X < ‖x‖) (i : Fin 3) :
    HasSum (fun a : PositiveIndex =>
      tmMoment a (fun j => DynamicVolume.source ci v j) *
          SourceRegularCorrection.electric (SourceDielectricModes.tmData d (a.1+1))
            (representative (a.1+1) a.2) x i +
        teMoment a (fun j => DynamicVolume.source ci v j) *
          SourceTECorrection.electric (SourceDielectricModes.teData d (a.1+1))
            (representative (a.1+1) a.2) x i)
      (ExteriorContinuity.electric 1 (DynamicVolume.source cs
        (MaterialField.solution cs 1 d.X (StaticCoefficient.sqrtMultiplier cs
          (ShellInclusionVolume.kernel 1 d.X (StaticCoefficient.sqrtMultiplier ci v))))) x i) := by
  have hcs : ∀ y : Space, y ∉ closedBall (0 : Space) d.X \ ball (0 : Space) d.R →
      cs.value (VectorFourier.coordinateMap y) = 0 := SourceModeDatum.annulus_support cs d hc hi
  obtain ⟨Φ, hΦ⟩ := exists_exterior_functional cs d.R d.X hcs x hx i
  have h := (shell_solution_series cs ci d b B T hb hB hscale hT hBT hTR hbR hc hi hci v).mapL Φ
  have h2 : HasSum (fun a : PositiveIndex =>
      tmMoment a (fun j => DynamicVolume.source ci v j) *
          SourceRegularCorrection.electric (SourceDielectricModes.tmData d (a.1+1))
            (representative (a.1+1) a.2) x i +
        teMoment a (fun j => DynamicVolume.source ci v j) *
          SourceTECorrection.electric (SourceDielectricModes.teData d (a.1+1))
            (representative (a.1+1) a.2) x i)
      (Φ (MaterialField.solution cs 1 d.X (StaticCoefficient.sqrtMultiplier cs
          (ShellInclusionVolume.kernel 1 d.X (StaticCoefficient.sqrtMultiplier ci v))))) := by
    convert h using 1
    funext a
    simp only [Function.comp_apply, map_add, map_smul, smul_eq_mul]
    rw [hΦ, hΦ, exterior_tm_mode cs d hm hdisp hu hc a x hx i,
      exterior_te_mode cs d hm hdisp hu hc a x hx i]
  rw [hΦ] at h2
  exact h2

theorem tm_total_eq (d : SourceRadialSystem.Data) (a : PositiveIndex) (x : Space) (hx : x ≠ 0)
    (i : Fin 3) :
    SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
      SourceRegularCorrection.electric (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i =
      SourceUnclippedMaxwell.electric (SourceDielectricModes.tmData d (a.1+1))
        (representative (a.1+1) a.2) x i := by
  have h1 := SourceRegularCorrection.electric_away (SourceDielectricModes.tmData d (a.1+1))
    (representative (a.1+1) a.2) (representative_homogeneous _ _) (representative_harmonic _ _) x hx
  have h2 := SourceDielectricModes.vacuum_electric (SourceDielectricModes.tmData d (a.1+1))
    (representative (a.1+1) a.2) x
  rw [h1, Pi.sub_apply, h2]
  change _ + (_ - SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data (a.1+1)) _ x i) = _
  ring

theorem te_total_eq (d : SourceRadialSystem.Data) (a : PositiveIndex) (x : Space) (hx : x ≠ 0)
    (i : Fin 3) :
    SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data (a.1+1)) (representative (a.1+1) a.2) x i +
      SourceTECorrection.electric (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i =
      SourceGeneralMaxwell.teElectric (SourceDielectricModes.teData d (a.1+1))
        (representative (a.1+1) a.2) x i := by
  have h1 := SourceTECorrection.electric_away (SourceDielectricModes.teData d (a.1+1))
    (representative (a.1+1) a.2) x hx
  have h2 := SourceDielectricModes.vacuum_magnetic (SourceDielectricModes.teData d (a.1+1))
    (representative (a.1+1) a.2) x
  rw [h1, Pi.sub_apply]
  change _ + (SourceUnclippedMaxwell.magnetic _ _ x i -
    SourceUnclippedMaxwell.magnetic (SourceCoreReaction.vacuum _) _ x i) =
    SourceUnclippedMaxwell.magnetic _ _ x i
  rw [h2]
  change _ + (_ - SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data (a.1+1)) _ x i) = _
  ring

/-- **The radiated electric field of the inclusion outside the shell as a layered mode series.**
For `x` outside the shell (`d.X < ‖x‖`), the electric field radiated by the inclusion source `v`, namely
the free field of the inclusion source plus the field of the polarization of the shell solution driven by
the shell datum `Ss T Si v`, is the sum over the positive degrees and the real modes of the TM moment
times the actual layered TM electric mode plus the TE moment times the actual layered TE electric mode.
The TM mode is `SourceUnclippedMaxwell.electric {d with l := a.1+1}` and the TE mode is
`SourceGeneralMaxwell.teElectric` of the TE data `teData d (a.1+1)` (the shell layers with `σ = 1`). -/
theorem radiated_field_series_outside (cs ci : Coefficient) (d : SourceRadialSystem.Data) (b B T : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hT : 2 ≤ T)
    (hBT : 2*(B*AngularExteriorBounds.base) ≤ T) (hTR : T < d.R) (hbR : b < d.R)
    (hm : ∀ x : Space, (cs.value (VectorFourier.coordinateMap x) : ℂ) = SourceRadialSystem.sigma d ‖x‖ - 1)
    (hdisp : ∀ g ∈ d.gs, g.q^2 = g.σ) (hu : IsUnit (DynamicVolume.volumeBlock cs 1 d.X))
    (hc : ∀ x : Space, x ∉ closedBall 0 d.X → cs.value (VectorFourier.coordinateMap x) = 0)
    (hi : ∀ x : Space, ‖x‖ ≤ d.R → cs.value (VectorFourier.coordinateMap x) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (v : VectorL2) (x : Space) (hx : d.X < ‖x‖) (i : Fin 3) :
    HasSum (fun a : PositiveIndex =>
      tmMoment a (fun j => DynamicVolume.source ci v j) *
          SourceUnclippedMaxwell.electric (SourceDielectricModes.tmData d (a.1+1))
            (representative (a.1+1) a.2) x i +
        teMoment a (fun j => DynamicVolume.source ci v j) *
          SourceGeneralMaxwell.teElectric (SourceDielectricModes.teData d (a.1+1))
            (representative (a.1+1) a.2) x i)
      (ExteriorContinuity.electric 1 (fun j => DynamicVolume.source ci v j) x i +
        ExteriorContinuity.electric 1 (DynamicVolume.source cs
          (MaterialField.solution cs 1 d.X (StaticCoefficient.sqrtMultiplier cs
            (ShellInclusionVolume.kernel 1 d.X (StaticCoefficient.sqrtMultiplier ci v))))) x i) := by
  have hRX : d.R ≤ d.X := RadialStack.chain_ordered d.chain
  have hxT : max T b < ‖x‖ := max_lt (by linarith) (by linarith)
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith [d.hR])
  have h1 := free_field_series_outside b B T hb hB hscale hT hBT
    (fun j => DynamicVolume.source ci v j) (fun j => DynamicVolume.source_integrable ci v b hci j)
    (fun j y hy => DynamicVolume.source_zero ci v b hci j y (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]; exact hy)) x hxT i
  have h2 := shell_reaction_series_outside cs ci d b B T hb hB hscale hT hBT hTR hbR hm hdisp hu hc hi hci
    v x hx i
  convert h1.add h2 using 1
  funext a
  have e1 := tm_total_eq d a x hx0 i
  have e2 := te_total_eq d a x hx0 i
  rw [← e1, ← e2]
  ring

/-! ### Moment bounds in the normalization of the barrier-degree decomposition -/

/-- The `L¹` mass of a current density. -/
def mass (ρ : Fin 3 → Space → ℂ) : ℝ := ∑ j, ∫ y, ‖ρ j y‖

theorem mass_nonneg (ρ : Fin 3 → Space → ℂ) : 0 ≤ mass ρ :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _

/-- Pointwise bound of the regular dyad coefficients of degree `a.1+1` on the ball of radius `b`. -/
def momentConst (b B : ℝ) (a : PositiveIndex) : ℝ :=
  DebyeJetBounds.scale 0 b * RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (a.1+2 : ℝ)^3 * B^(a.1+1)

theorem moment_norm_le (b B : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (a : PositiveIndex) :
    ‖tmMoment a ρ‖ ≤ momentConst b B a * mass ρ ∧ ‖teMoment a ρ‖ ≤ momentConst b B a * mass ρ := by
  have key : ∀ (c : Space → Fin 3 → ℂ) (hc : ∀ y, ‖y‖ ≤ b → ∀ j, ‖c y j‖ ≤ momentConst b B a),
      ‖∑ j, ∫ y, c y j * ρ j y‖ ≤ momentConst b B a * mass ρ := by
    intro c hc
    unfold mass
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hρ j).norm.const_mul _) (Eventually.of_forall fun y => ?_)
    by_cases hy : ‖y‖ ≤ b
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hc y hy j) (norm_nonneg _) |>.trans_eq (by ring)
    · rw [hsupp j y (not_le.mp hy)]
      simp
  constructor
  · exact key (fun y j => FreeSourceCoefficients.tmCoefficient a y j)
      (fun y hy j => (OutgoingDyadBounds.regular_coefficient_bound a b B hb hB hscale y hy j).1)
  · exact key (fun y j => FreeSourceCoefficients.teCoefficient a y j)
      (fun y hy j => (OutgoingDyadBounds.regular_coefficient_bound a b B hb hB hscale y hy j).2)

theorem cubic_geometric_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (l : ℕ) :
    ((l : ℝ)+1)^3 * r^l ≤ 6/(1-r)^4 := by
  have hn : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one 3 hn
  have h1 : (((l+3).choose 3 : ℕ) : ℝ) * r^l ≤ 1/(1-r)^(3+1) :=
    le_hasSum hs l (fun n _ => by positivity)
  have h2 : (((l+3).choose 3 : ℕ) : ℝ) * 6 = ((l : ℝ)+3)*((l : ℝ)+2)*((l : ℝ)+1) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose (l+3) 3
    simp [Nat.descFactorial_succ, Nat.factorial] at h
    have h' : (l+3).choose 3 * 6 = (l+3)*(l+2)*(l+1) := by nlinarith [h]
    exact_mod_cast h'
  have h3 : ((l : ℝ)+1)^3 ≤ 6 * (((l+3).choose 3 : ℕ) : ℝ) := by
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith [h2]
  calc ((l : ℝ)+1)^3 * r^l ≤ (6 * (((l+3).choose 3 : ℕ) : ℝ)) * r^l :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = 6 * ((((l+3).choose 3 : ℕ) : ℝ) * r^l) := by ring
    _ ≤ 6 * (1/(1-r)^(3+1)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 6/(1-r)^4 := by ring

/-- The explicit constant of the moment bound: `‖ρ‖₁ · scale₀(b) · 6 (1 - B/s₀)⁻⁴ · exp(s₀²/8) / s₀`. -/
def momentA (b B s0 : ℝ) (ρ : Fin 3 → Space → ℂ) : ℝ :=
  mass ρ * DebyeJetBounds.scale 0 b * (6/(1-B/s0)^4) * Real.exp (s0^2/8) / s0

theorem momentConst_le_regular (b B s0 : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B) (hBs : B < s0) (hs0 : 0 < s0)
    (a : PositiveIndex) (hbar : s0^2 < RiccatiBarrier.ν (a.1+1)) :
    momentConst b B a ≤ DebyeJetBounds.scale 0 b * (6/(1-B/s0)^4) * Real.exp (s0^2/8) / s0 *
      HankelRealBasis.regular (a.1+1) s0 := by
  set l := a.1+1 with hl
  have hl1 : 1 ≤ l := Nat.succ_le_succ (Nat.zero_le _)
  have hlow := RiccatiGaussianBound.regular_gaussian_lower l s0 hs0 hbar s0 ⟨hs0, le_rfl⟩
  have hγ := RiccatiLogDerivative.gamma_ge_one l s0 hbar
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl1
  have hamp := RiccatiSeriesCoefficients.amplitude_pos l 0
  have hden : (0 : ℝ) < 2*((l : ℝ)+RiccatiLogDerivative.gamma l s0+2) := by positivity
  have hexp : Real.exp (s0^2/(2*((l : ℝ)+RiccatiLogDerivative.gamma l s0+2))) ≤ Real.exp (s0^2/8) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    linarith
  have hreg0 : 0 ≤ HankelRealBasis.regular l s0 := by
    refine le_trans ?_ hlow
    positivity
  have hA : RiccatiSeriesCoefficients.amplitude l 0 * s0^(l+1) ≤
      HankelRealBasis.regular l s0 * Real.exp (s0^2/8) := by
    have h1 : RiccatiSeriesCoefficients.amplitude l 0 * s0^(l+1) =
        (RiccatiSeriesCoefficients.amplitude l 0 * s0^(l+1) *
          Real.exp (-s0^2/(2*((l : ℝ)+RiccatiLogDerivative.gamma l s0+2)))) *
        Real.exp (s0^2/(2*((l : ℝ)+RiccatiLogDerivative.gamma l s0+2))) := by
      rw [mul_assoc, ← Real.exp_add]
      have : -s0^2/(2*((l : ℝ)+RiccatiLogDerivative.gamma l s0+2)) +
          s0^2/(2*((l : ℝ)+RiccatiLogDerivative.gamma l s0+2)) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    rw [h1]
    exact mul_le_mul hlow hexp (Real.exp_pos _).le hreg0
  have hr0 : 0 ≤ B/s0 := div_nonneg hB hs0.le
  have hr1 : B/s0 < 1 := (div_lt_one hs0).mpr hBs
  have hcub := cubic_geometric_le (B/s0) hr0 hr1 l
  have hS := DebyeJetBounds.scale_nonnegative 0 b hb
  have hBl : B^l = (B/s0)^l * s0^l := by
    rw [div_pow]; field_simp
  have hpow : s0^(l+1) = s0 * s0^l := by ring
  unfold momentConst
  have hl2 : (a.1+2 : ℝ) = (l : ℝ)+1 := by rw [hl]; push_cast; ring
  rw [hl2]
  have hs0l : 0 < s0^l := pow_pos hs0 l
  calc DebyeJetBounds.scale 0 b * RiccatiSeriesCoefficients.amplitude l 0 * ((l : ℝ)+1)^3 * B^l
      = DebyeJetBounds.scale 0 b * (RiccatiSeriesCoefficients.amplitude l 0 * s0^(l+1)) / s0 *
          (((l : ℝ)+1)^3 * (B/s0)^l) := by
        rw [hBl, hpow]; field_simp; ring
    _ ≤ DebyeJetBounds.scale 0 b * (HankelRealBasis.regular l s0 * Real.exp (s0^2/8)) / s0 *
          (6/(1-B/s0)^4) := by
        apply mul_le_mul _ hcub (by positivity) (by positivity)
        apply div_le_div_of_nonneg_right _ hs0.le
        exact mul_le_mul_of_nonneg_left hA hS
    _ = _ := by ring

theorem moment_barrier_bound (b B s0 : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B) (hBs : B < s0) (hs0 : 0 < s0)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hsupp : ∀ j y, b < ‖y‖ → ρ j y = 0) (a : PositiveIndex)
    (hbar : s0^2 < RiccatiBarrier.ν (a.1+1)) :
    ‖tmMoment a ρ‖ ≤ momentA b B s0 ρ * HankelRealBasis.regular (a.1+1) s0 ∧
      ‖teMoment a ρ‖ ≤ momentA b B s0 ρ * HankelRealBasis.regular (a.1+1) s0 := by
  have hm := moment_norm_le b B hb hB hscale ρ hρ hsupp a
  have hc := momentConst_le_regular b B s0 hb hB hBs hs0 a hbar
  have hmass := mass_nonneg ρ
  have e : momentA b B s0 ρ * HankelRealBasis.regular (a.1+1) s0 =
      (DebyeJetBounds.scale 0 b * (6/(1-B/s0)^4) * Real.exp (s0^2/8) / s0 *
        HankelRealBasis.regular (a.1+1) s0) * mass ρ := by
    unfold momentA; ring
  rw [e]
  exact ⟨hm.1.trans (mul_le_mul_of_nonneg_right hc hmass),
    hm.2.trans (mul_le_mul_of_nonneg_right hc hmass)⟩

end OQ14.SourceRadiatedSeries

#print axioms OQ14.SourceRadiatedSeries.electric_coefficient_continuous
#print axioms OQ14.SourceRadiatedSeries.toroidal_coefficient_continuous
#print axioms OQ14.SourceRadiatedSeries.tmCoefficient_continuous
#print axioms OQ14.SourceRadiatedSeries.teCoefficient_continuous
#print axioms OQ14.SourceRadiatedSeries.coefficient_mul_integrable
#print axioms OQ14.SourceRadiatedSeries.majorant_nonneg
#print axioms OQ14.SourceRadiatedSeries.term_eq
#print axioms OQ14.SourceRadiatedSeries.term_continuous_in_source
#print axioms OQ14.SourceRadiatedSeries.component_hasSum
#print axioms OQ14.SourceRadiatedSeries.integral_term_split
#print axioms OQ14.SourceRadiatedSeries.free_field_series_outside
#print axioms OQ14.SourceRadiatedSeries.free_field_series_outside_tsum
#print axioms OQ14.SourceRadiatedSeries.datumBound_nonneg
#print axioms OQ14.SourceRadiatedSeries.datum_norm_le
#print axioms OQ14.SourceRadiatedSeries.mode_norm_le
#print axioms OQ14.SourceRadiatedSeries.mode_datum_eq
#print axioms OQ14.SourceRadiatedSeries.integral_mode_datum
#print axioms OQ14.SourceRadiatedSeries.shell_datum_series
#print axioms OQ14.SourceRadiatedSeries.shell_solution_series
#print axioms OQ14.SourceRadiatedSeries.exists_exterior_functional
#print axioms OQ14.SourceRadiatedSeries.eq_of_ae_exterior
#print axioms OQ14.SourceRadiatedSeries.exterior_tm_mode
#print axioms OQ14.SourceRadiatedSeries.exterior_te_mode
#print axioms OQ14.SourceRadiatedSeries.shell_reaction_series_outside
#print axioms OQ14.SourceRadiatedSeries.tm_total_eq
#print axioms OQ14.SourceRadiatedSeries.te_total_eq
#print axioms OQ14.SourceRadiatedSeries.radiated_field_series_outside
#print axioms OQ14.SourceRadiatedSeries.mass_nonneg
#print axioms OQ14.SourceRadiatedSeries.moment_norm_le
#print axioms OQ14.SourceRadiatedSeries.cubic_geometric_le
#print axioms OQ14.SourceRadiatedSeries.momentConst_le_regular
#print axioms OQ14.SourceRadiatedSeries.moment_barrier_bound
