import CoreReaction
import BackgroundFluxMajorant

/-! The inverse-cube majorant of the total field of the inclusion in the growing core, uniform in the shell index.

The assembled plane fields of the actual finite paired shell at index `r` are the incident (background) field plus
the free dyadic potential of the inclusion source plus the shell reaction field.  Outside a fixed ball the free
potential and, for every large `r`, the reaction field have plane decompositions (tangential part `O(1/|x|)`,
radial part `O(1/|x|^2)`) with constants independent of `r` and `x`, linear in the norm of the inclusion vector;
together with a decomposition of the background field this gives the inverse-cube majorant of the normal
component of `E x conj H` on the plane inside the core. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.CoreRadiatedMajorant
open MeasureTheory Filter Set Metric Complex OQ14.Maxwell OQ14.SourceRemotePlaneBand OQ14.CoreWeakSeries
  OQ14.CoreFreePotential OQ14.CoreRegularModes OQ14.CoreReaction
open OQ14.BarrierDegreeFluxConstants (decomp_mono)
open scoped Topology ComplexConjugate

/-- The lower radius for the radiated-field majorant: the reaction threshold and the free-potential radius. -/
def coreMin (q b : ℝ) : ℝ :=
  max (rhoMin q b) (max (max 2 (2 * (max 1 (HarmonicSpatialMajorant.degreeScale 2 b) *
    AngularExteriorBounds.base))) b)

theorem rhoMin_le_coreMin (q b : ℝ) : rhoMin q b ≤ coreMin q b := le_max_left _ _

theorem freeRadius_le_coreMin (q b : ℝ) :
    max (max 2 (2 * (max 1 (HarmonicSpatialMajorant.degreeScale 2 b) * AngularExteriorBounds.base))) b ≤
      coreMin q b := le_max_right _ _

theorem two_le_coreMin (q b : ℝ) : 2 ≤ coreMin q b :=
  (le_max_left (2 : ℝ) _).trans ((le_max_left _ b).trans (freeRadius_le_coreMin q b))

/-- **The free potential of an inclusion vector** (`ci` supported in the ball of radius `b`): outside the ball of
the free-potential radius the electric and magnetic free potentials decompose, with bounds linear in `‖u‖`. -/
theorem free_part_decomp (ci : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData ci)
    (b : ℝ) (hb : 0 ≤ b) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b) :
    ∃ KG : ℝ, 0 ≤ KG ∧ ∀ (u : VectorFourier.VectorL2) (x : Space),
      max (max 2 (2 * (max 1 (HarmonicSpatialMajorant.degreeScale 2 b) * AngularExteriorBounds.base))) b <
        ‖x‖ →
      Decomp (3 * KG * ‖u‖) (KG * ‖u‖) (ExteriorContinuity.electric 1 (DynamicVolume.source ci u) x) x ∧
      Decomp (3 * KG * ‖u‖) (KG * ‖u‖) (MagneticResponse.magnetic 1 (DynamicVolume.source ci u) x) x := by
  have hbase := base_pos
  set B : ℝ := max 1 (HarmonicSpatialMajorant.degreeScale 2 b) with hBdef
  have hB0 : 0 ≤ B := le_trans zero_le_one (le_max_left _ _)
  have hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B := le_max_right _ _
  set ρ2 : ℝ := max (max 2 (2 * (B * AngularExteriorBounds.base))) b with hρ2
  have hR : 2 ≤ ρ2 := (le_max_left _ _).trans (le_max_left _ _)
  have hBR : 2 * (B * AngularExteriorBounds.base) ≤ ρ2 := (le_max_right _ _).trans (le_max_left _ _)
  have hbR : b ≤ ρ2 := le_max_right _ _
  refine ⟨massConst ci d * freeConst b ρ2 1,
    mul_nonneg (massConst_nonneg ci d) (freeConst_nonneg b ρ2 1 hb zero_le_one), ?_⟩
  intro u x hx
  have hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0 :=
    fun y hy => d.carrierZero y (fun hc => hy (mem_closedBall_zero_iff.mpr (hcar y hc)))
  have hρint : ∀ j, Integrable (DynamicVolume.source ci u j) :=
    fun j => DynamicVolume.source_integrable ci u b hci j
  have hρvan : ∀ j y, y ∉ closedBall (0 : Space) b → DynamicVolume.source ci u j y = 0 := by
    intro j y hy
    simp [DynamicVolume.source, hci y hy]
  have hF : ∃ F : VectorFourier.VectorL2, ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume]
      DynamicVolume.source ci u j :=
    ⟨StaticCoefficient.sqrtMultiplier ci u, fun j => StaticNewton.material_source_ae ci u j⟩
  have h := free_potential_decomp b B ρ2 (massConst ci d * ‖u‖) hb hB0 hscale hR hBR hbR
    (DynamicVolume.source ci u) hρint hρvan hF (mass_source_le ci d u) x hx
  have hfc : freeConst b ρ2 (massConst ci d * ‖u‖) = massConst ci d * freeConst b ρ2 1 * ‖u‖ := by
    unfold freeConst
    have : (fun a => degConst b ρ2 (massConst ci d * ‖u‖) a) =
        fun a => (massConst ci d * ‖u‖) * degConst b ρ2 1 a := funext fun a => by unfold degConst; ring
    rw [this, tsum_mul_left]
    ring
  rw [hfc] at h
  have e3 : 3 * (massConst ci d * freeConst b ρ2 1) * ‖u‖ =
      3 * (massConst ci d * freeConst b ρ2 1 * ‖u‖) := by ring
  rw [← e3] at h
  exact h

variable (q : ℝ) (hq : 1 ≤ q) (n : ℕ)

/-- **Total decomposition in the growing core.**  Suppose the incident (background) fields `Einc r`, `Hinc r` of
the shell index `r` decompose at every point of the core outside the ball of radius `ρ1` with constants
independent of `r`.  Then for large shell index `r`, every inclusion vector `u` and every `x` with
`ρ1 < |x| < R_r`, the assembled electric and magnetic plane fields (background plus free potential of the
inclusion plus shell reaction field) decompose with constants `K1b + 3 K ‖u‖`, `K2b + K ‖u‖`
(respectively `L1b + 3 K ‖u‖`, `L2b + K ‖u‖`), `K` independent of `r`. -/
theorem core_total_decomp (ci : StaticCoefficient.Coefficient)
    (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : 0 ≤ b) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b)
    (ρ1 : ℝ) (hρ1 : coreMin q b ≤ ρ1) (Einc Hinc : ℕ → Maxwell.Field) (K1b K2b L1b L2b : ℝ)
    (hE : ∀ (r : ℕ) (x : Space), ρ1 < ‖x‖ → Decomp K1b K2b (Einc r x) x)
    (hH : ∀ (r : ℕ) (x : Space), ρ1 < ‖x‖ → Decomp L1b L2b (Hinc r x) x) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℕ in atTop, ∀ (u : VectorFourier.VectorL2) (x : Space),
      ρ1 < ‖x‖ → ‖x‖ < (SourcePairedInclusion.data q hq n r).R →
      Decomp (K1b + 3 * K * ‖u‖) (K2b + K * ‖u‖)
        (fun i => SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci u (Einc r) x i) x ∧
      Decomp (L1b + 3 * K * ‖u‖) (L2b + K * ‖u‖)
        (fun i => SourcePairedPlaneMagnetic.pairedPlaneMagnetic q hq n r ci u (Hinc r) x i) x := by
  obtain ⟨KG, hKG, hG⟩ := free_part_decomp ci d b hb hcar
  obtain ⟨KR, hKR, hRev⟩ := reaction_core_decomp q hq n ci d b hb hcar ρ1 ((rhoMin_le_coreMin q b).trans hρ1)
  refine ⟨KG + KR, add_nonneg hKG hKR, ?_⟩
  filter_upwards [hRev] with r hr
  intro u x hx1 hxR
  have hrpos : 0 < ‖x‖ := by
    have := two_le_coreMin q b
    linarith
  have hx0 : x ≠ 0 := norm_pos_iff.mp hrpos
  have hxfree : max (max 2 (2 * (max 1 (HarmonicSpatialMajorant.degreeScale 2 b) *
      AngularExteriorBounds.base))) b < ‖x‖ :=
    lt_of_le_of_lt ((freeRadius_le_coreMin q b).trans hρ1) hx1
  obtain ⟨hG1, hG2⟩ := hG u x hxfree
  obtain ⟨hR1, hR2⟩ := hr u x hx1 hxR
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  refine ⟨?_, ?_⟩
  · have h := decomp_add (decomp_add (hE r x hx1) hG1) hR1
    have e : (fun i => SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci u (Einc r) x i) =
        (Einc r x + ExteriorContinuity.electric 1 (DynamicVolume.source ci u) x) +
          (fun i => SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r) ci
            (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
            (SourcePairedInclusion.data q hq n r).X u x i) := by
      funext i
      simp [SourcePairedPlaneCompact.pairedPlaneElectric, add_assoc]
    rw [e]
    exact decomp_mono hx0 h (by nlinarith) (by nlinarith)
  · have h := decomp_add (decomp_add (hH r x hx1) hG2) hR2
    have e : (fun i => SourcePairedPlaneMagnetic.pairedPlaneMagnetic q hq n r ci u (Hinc r) x i) =
        (Hinc r x + MagneticResponse.magnetic 1 (DynamicVolume.source ci u) x) +
          (fun i => SourcePairedPlaneMagnetic.magneticReactionField (SourcePairedInclusion.shell q hq n r) ci
            (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
            (SourcePairedInclusion.data q hq n r).X u x i) := by
      funext i
      simp [SourcePairedPlaneMagnetic.pairedPlaneMagnetic, add_assoc]
    rw [e]
    exact decomp_mono hx0 h (by nlinarith) (by nlinarith)

/-- **The inverse-cube flux majorant in the growing core.**  Under the hypotheses of `core_total_decomp` with
nonnegative background constants, for large shell index `r`, every inclusion vector `u` with `‖u‖ ≤ U` and every
plane point `x` (`x 2 = 0`) with `ρ1 < |x| < R_r`, the normal component of `E conj H` of the assembled fields is
at most `C / |x|^3`, with `C` independent of `r`. -/
theorem core_flux_majorant (ci : StaticCoefficient.Coefficient)
    (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : 0 ≤ b) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b)
    (ρ1 : ℝ) (hρ1 : coreMin q b ≤ ρ1) (Einc Hinc : ℕ → Maxwell.Field) (K1b K2b L1b L2b : ℝ)
    (hK1 : 0 ≤ K1b) (hK2 : 0 ≤ K2b) (hL1 : 0 ≤ L1b) (hL2 : 0 ≤ L2b)
    (hE : ∀ (r : ℕ) (x : Space), ρ1 < ‖x‖ → Decomp K1b K2b (Einc r x) x)
    (hH : ∀ (r : ℕ) (x : Space), ρ1 < ‖x‖ → Decomp L1b L2b (Hinc r x) x) (U : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℕ in atTop, ∀ (u : VectorFourier.VectorL2), ‖u‖ ≤ U →
      ∀ (x : Space), x 2 = 0 → ρ1 < ‖x‖ → ‖x‖ < (SourcePairedInclusion.data q hq n r).R →
      ‖crossProduct (fun i => SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci u (Einc r) x i)
        (conjugate (fun i => SourcePairedPlaneMagnetic.pairedPlaneMagnetic q hq n r ci u (Hinc r) x i)) 2‖ ≤
        C / ‖x‖^3 := by
  obtain ⟨K, hK, hev⟩ := core_total_decomp q hq n ci d b hb hcar ρ1 hρ1 Einc Hinc K1b K2b L1b L2b hE hH
  have hU : ∀ u : VectorFourier.VectorL2, ‖u‖ ≤ U → 0 ≤ U := fun u hu => (norm_nonneg u).trans hu
  refine ⟨2 * (K2b + K * max U 0) * (L1b + 3 * K * max U 0) +
    2 * (K1b + 3 * K * max U 0) * (L2b + K * max U 0), by positivity, ?_⟩
  filter_upwards [hev] with r hr
  intro u hu x hx2 hx1 hxR
  have hrpos : 0 < ‖x‖ := by
    have := two_le_coreMin q b
    linarith
  obtain ⟨hD1, hD2⟩ := hr u x hx1 hxR
  have hflux := flux_bound_of_decomp x hx2 hrpos _ _ _ _ _ _ hD1 hD2
  refine hflux.trans ?_
  have hum : ‖u‖ ≤ max U 0 := hu.trans (le_max_left _ _)
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hk : K * ‖u‖ ≤ K * max U 0 := mul_le_mul_of_nonneg_left hum hK
  have hnum : 2 * (K2b + K * ‖u‖) * (L1b + 3 * K * ‖u‖) + 2 * (K1b + 3 * K * ‖u‖) * (L2b + K * ‖u‖) ≤
      2 * (K2b + K * max U 0) * (L1b + 3 * K * max U 0) +
        2 * (K1b + 3 * K * max U 0) * (L2b + K * max U 0) := by
    have h3 : 3 * K * ‖u‖ ≤ 3 * K * max U 0 := by nlinarith
    have a1 : 0 ≤ K2b + K * ‖u‖ := by positivity
    have a2 : 0 ≤ L1b + 3 * K * ‖u‖ := by positivity
    have a3 : 0 ≤ K1b + 3 * K * ‖u‖ := by positivity
    have a4 : 0 ≤ L2b + K * ‖u‖ := by positivity
    nlinarith [mul_le_mul (add_le_add_left hk K2b) (add_le_add_left h3 L1b) a2 (by positivity),
      mul_le_mul (add_le_add_left h3 K1b) (add_le_add_left hk L2b) a4 (by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact hnum

/-- **The inverse-cube flux majorant of the actual device in the growing core.**  For a finite TE coefficient
vector `A` (the incident field), an inclusion with carrier in the ball of radius `b`, and `U ≥ 0`, there are
`ρ1 > 0` and `C ≥ 0` such that for all large shell index `r`, every inclusion vector `u` with `‖u‖ ≤ U` and every
plane point `x` (`x 2 = 0`) with `ρ1 < |x| < R_r`, the normal component of `E conj H` of the assembled plane fields
(TE background of the shell, free potential of the inclusion, shell reaction field) is at most `C / |x|^3`. -/
theorem core_flux_majorant_te (A : SymmetricHarmonicJets.Index →₀ ℂ) (ci : StaticCoefficient.Coefficient)
    (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : 0 ≤ b) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b)
    (U : ℝ) :
    ∃ ρ1 C : ℝ, 0 < ρ1 ∧ 0 ≤ C ∧ ∀ᶠ r : ℕ in atTop, ∀ (u : VectorFourier.VectorL2), ‖u‖ ≤ U →
      ∀ (x : Space), x 2 = 0 → ρ1 < ‖x‖ → ‖x‖ < (SourcePairedInclusion.data q hq n r).R →
      ‖crossProduct (fun i => SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci u
          (OQ14.BackgroundModeTE.famBackground (OQ14.BackgroundModeTE.physicalTE q (zero_lt_one.trans_le hq) n r)
            A.support (OQ14.BackgroundModeTE.teCoeff A) (fun q => q.val.1)
            RestrictedTEIncoming.polynomial) x i)
        (conjugate (fun i => SourcePairedPlaneMagnetic.pairedPlaneMagnetic q hq n r ci u
          (OQ14.BackgroundFluxMajorant.famBackgroundH
            (OQ14.BackgroundModeTE.physicalTE q (zero_lt_one.trans_le hq) n r)
            A.support (OQ14.BackgroundModeTE.teCoeff A) (fun q => q.val.1)
            RestrictedTEIncoming.polynomial) x i)) 2‖ ≤ C / ‖x‖^3 := by
  obtain ⟨ρb, K1, L1, L2, hρb, hbg⟩ := OQ14.BackgroundFluxMajorant.background_decomp_majorant q hq n A
  have hρ1 : coreMin q b ≤ max (coreMin q b) ρb := le_max_left _ _
  have hpos : 0 < max (coreMin q b) ρb := lt_of_lt_of_le (by norm_num) ((two_le_coreMin q b).trans hρ1)
  have hx0 (x : Space) (hx : max (coreMin q b) ρb < ‖x‖) : x ≠ 0 := by
    apply norm_pos_iff.mp
    linarith
  obtain ⟨C, hC, hev⟩ := core_flux_majorant q hq n ci d b hb hcar (max (coreMin q b) ρb) hρ1
    (fun r => OQ14.BackgroundModeTE.famBackground (OQ14.BackgroundModeTE.physicalTE q (zero_lt_one.trans_le hq) n r)
      A.support (OQ14.BackgroundModeTE.teCoeff A) (fun q => q.val.1) RestrictedTEIncoming.polynomial)
    (fun r => OQ14.BackgroundFluxMajorant.famBackgroundH
      (OQ14.BackgroundModeTE.physicalTE q (zero_lt_one.trans_le hq) n r)
      A.support (OQ14.BackgroundModeTE.teCoeff A) (fun q => q.val.1) RestrictedTEIncoming.polynomial)
    (max K1 0) 0 (max L1 0) (max L2 0) (le_max_right _ _) le_rfl (le_max_right _ _) (le_max_right _ _)
    (fun r x hx => decomp_mono (hx0 x hx) (hbg r x ((le_max_right _ _).trans hx.le)).1 (le_max_left _ _) le_rfl)
    (fun r x hx => decomp_mono (hx0 x hx) (hbg r x ((le_max_right _ _).trans hx.le)).2
      (le_max_left _ _) (le_max_left _ _)) U
  exact ⟨max (coreMin q b) ρb, C, hpos, hC, hev⟩

end OQ14.CoreRadiatedMajorant

#print axioms OQ14.CoreRadiatedMajorant.rhoMin_le_coreMin
#print axioms OQ14.CoreRadiatedMajorant.freeRadius_le_coreMin
#print axioms OQ14.CoreRadiatedMajorant.two_le_coreMin
#print axioms OQ14.CoreRadiatedMajorant.free_part_decomp
#print axioms OQ14.CoreRadiatedMajorant.core_total_decomp
#print axioms OQ14.CoreRadiatedMajorant.core_flux_majorant

#print axioms OQ14.CoreRadiatedMajorant.core_flux_majorant_te
