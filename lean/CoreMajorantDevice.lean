import RestrictedTEActualPiecewise
import CoreRadiatedMajorant

/-! The core majorant of the concrete doubled device.

The channel assembly (`RestrictedTEActualPiecewise.actual_counted_subspaces_of_pieces`) consumes a structure
`CoreMajorant`: an inverse-cube majorant of the plane flux of the assembled core fields `coreE`, `coreH` of the
combined shell-plus-inclusion device on `rho1 <= |xi| < radius r`, uniform in the shell index on the unit-power
sphere of the span of every orthonormal family, for all large gain indices.  This module proves it for the
concrete doubled device.

* `teMagnetic_wave`, `magnetic_scaledCoeff_eq`, `bgFieldH_core`: on the open core the TE magnetic background
  `bgFieldH` (minus the TM-structure electric background) is the regular TE magnetic field of the vector rescaled
  degreewise by the transmissions over two (the magnetic counterpart of `shell_te_core`);
* `backgroundElectric_eq_bgFieldE`, `backgroundMagnetic_eq_bgFieldH`: at every nonzero point of the open core the
  continuous background fields of the shell solution are `bgFieldE`, `bgFieldH`;
* `coreE_eq`, `coreH_eq`: at every plane point of the open core at positive distance from the carrier the core
  fields are the background field plus the inclusion part (free potential plus shell reaction field) of the
  inclusion solution `inclSolution`, once the effective block is a unit;
* `core_majorant_general`: the uniform flux majorant for an arbitrary inclusion with carrier in a ball and at
  positive height from the plane, when the limiting effective block is a unit, from the audited decomposition of
  the free potential and of the shell reaction field (`core_total_decomp` with zero incident field), the uniform
  decomposition of the TE background on the unit sphere of a span and the uniform bound of the inclusion solution;
* `coreMajorant_of_device`, `coreMajorant_device`: the doubled device, and the structure `CoreMajorant`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.CoreMajorantDevice
open MeasureTheory Filter Topology
open OQ14.SourceRemotePlaneBand

abbrev Vec := OQ14.RestrictedTEActualCore.Vec

/-! ### The TE magnetic background on the open core -/

/-- The TE magnetic field of a regular wave is `-I` times the TM electric profile. -/
theorem teMagnetic_wave (l : ℕ) (P : HarmonicPolynomial.Poly) (x : Maxwell.Space) (i : Fin 3) :
    DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave l 1 P) x i =
      -Complex.I * SolidMaxwellProfiles.electric l P x i := by
  simp only [DebyeMaxwell.teMagnetic, SolidMaxwellProfiles.electric, DebyeMaxwell.tmElectric, div_one]

theorem coefficient_scaledCoeff (A : Vec) (τ : ℕ → ℂ) (qq : SymmetricHarmonicJets.Index) :
    RestrictedTEIncoming.coefficient (BackgroundCoreTransmission.scaledCoeff A τ) qq =
      RestrictedTEIncoming.coefficient A qq * τ qq.val.1 := by
  unfold RestrictedTEIncoming.coefficient
  rw [BackgroundCoreTransmission.scaledCoeff_apply]
  ring

/-- The regular TE magnetic field of a rescaled vector as a finite sum over the support of the vector. -/
theorem magnetic_scaledCoeff_eq (A : Vec) (τ : ℕ → ℂ) (x : Maxwell.Space) (i : Fin 3) :
    RestrictedTEPlaneLocal.magnetic (BackgroundCoreTransmission.scaledCoeff A τ) x i =
      ∑ qq ∈ A.support, RestrictedTEIncoming.coefficient A qq * τ qq.val.1 *
        DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave qq.val.1 1
          (RestrictedTEIncoming.polynomial qq)) x i := by
  change DebyeMaxwell.teMagnetic 1 (RestrictedTEFields.potential 1
    (BackgroundCoreTransmission.scaledCoeff A τ)) x i = _
  rw [RestrictedTEIncoming.magnetic_sum]
  refine (Finset.sum_subset (BackgroundCoreTransmission.scaledCoeff_support A τ) ?_).trans ?_
  · intro qq _ hqq
    have h : BackgroundCoreTransmission.scaledCoeff A τ qq = 0 := Finsupp.not_mem_support_iff.mp hqq
    simp [RestrictedTEIncoming.coefficient, h]
  · refine Finset.sum_congr rfl (fun qq _ => ?_)
    rw [coefficient_scaledCoeff]

theorem bgFieldH_apply (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (A : Vec) (x : Maxwell.Space) (i : Fin 3) :
    RestrictedTEActualPiecewise.bgFieldH q hq n r A x i =
      ∑ qq ∈ A.support, BackgroundModeTE.teCoeff A qq *
        (-(BackgroundModeMaxwell.backgroundElectric
          { BackgroundModeTE.physicalTE q (zero_lt_one.trans_le hq) n r with l := qq.val.1 }
          (RestrictedTEIncoming.polynomial qq) x i)) := by
  simp [RestrictedTEActualPiecewise.bgFieldH, BackgroundFluxMajorant.famBackgroundH, Finset.sum_apply]

/-- **The TE magnetic background on the open core.**  Away from the origin and inside the radius of the shell
index, the TE magnetic background of the physical stack is the regular TE magnetic field of the vector rescaled
degreewise by the transmissions over two. -/
theorem bgFieldH_core (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (A : Vec) (x : Maxwell.Space) (hx : x ≠ 0)
    (hR : ‖x‖ ≤ RadialPhaseLimit.radius r) (i : Fin 3) :
    RestrictedTEActualPiecewise.bgFieldH q hq n r A x i =
      RestrictedTEPlaneLocal.magnetic (BackgroundCoreTransmission.scaledCoeff A
        (RestrictedTEActualCore.trans q hq n r)) x i := by
  rw [bgFieldH_apply, magnetic_scaledCoeff_eq]
  refine Finset.sum_congr rfl (fun qq _ => ?_)
  have hc := congrFun (BackgroundModeMaxwell.backgroundElectric_core
    { BackgroundModeTE.physicalTE q (zero_lt_one.trans_le hq) n r with l := qq.val.1 }
    (RestrictedTEIncoming.polynomial qq) (BackgroundModeTE.polynomial_homogeneous qq)
    (BackgroundModeTE.polynomial_harmonic qq) x hx hR) i
  have ht := BackgroundModeTE.physicalTE_transmission q (zero_lt_one.trans_le hq) n qq.val.1 r
  simp only [Pi.smul_apply, smul_eq_mul] at hc
  rw [hc, teMagnetic_wave]
  unfold BackgroundModeTE.teCoeff RestrictedTEActualCore.trans
  dsimp only at ht ⊢
  rw [ht]
  ring

/-- The continuous electric background of the shell is the TE electric background field at every nonzero point of
the open core. -/
theorem backgroundElectric_eq_bgFieldE (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (A : Vec) (y : Maxwell.Space)
    (hy0 : y ≠ 0) (hy : ‖y‖ < (SourcePairedInclusion.data q hq n r).R) :
    SourcePairedPlaneIdentification.backgroundElectric (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.electric A)
        (RestrictedTEActualCore.fsLin q hq n r A) y =
      RestrictedTEActualPiecewise.bgFieldE q hq n r A y := by
  rw [RestrictedTEActualCore.backgroundElectric_eq_core q hq n r A y hy]
  exact (BackgroundShellCoefficient.shell_te_core q hq n r A y hy0 hy.le).symm

/-- The continuous magnetic background of the shell is the TE magnetic background field at every nonzero point of
the open core. -/
theorem backgroundMagnetic_eq_bgFieldH (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (A : Vec) (y : Maxwell.Space)
    (hy0 : y ≠ 0) (hy : ‖y‖ < (SourcePairedInclusion.data q hq n r).R) :
    SourcePairedPlaneIdentification.backgroundMagnetic (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.magnetic A)
        (RestrictedTEActualCore.fsLin q hq n r A) y =
      RestrictedTEActualPiecewise.bgFieldH q hq n r A y := by
  funext i
  rw [RestrictedTEActualCore.backgroundMagnetic_eq_core q hq n r A y hy i,
    bgFieldH_core q hq n r A y hy0 hy.le i]


/-! ### The core fields at plane points of the open core -/

/-- **The core electric field is the background plus the inclusion part.**  At a plane point of the open core, at
positive distance from the carrier, once the effective block is a unit, the assembled core electric field is the TE
background field plus the free potential and shell reaction field of the inclusion solution. -/
theorem coreE_eq (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b η : ℝ)
    (hs : RestrictedTEActualCore.CoreSetup q hq n r ci dci b η)
    (hE : IsUnit (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)) (x : Vec)
    (ξ : PlaneInverseCube.Plane) (hξ : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R)
    (hξ0 : MaxwellPlaneTail.planePoint ξ ≠ 0) :
    RestrictedTEActualCore.coreE q hq n r ci dci x ξ =
      RestrictedTEActualPiecewise.bgFieldE q hq n r x (MaxwellPlaneTail.planePoint ξ) +
        SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci
          (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x) 0
          (MaxwellPlaneTail.planePoint ξ) := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hs.hb.le hs.hci
  have hfs0 : StaticCoefficient.sqrtMultiplier ci (RestrictedTEActualCore.fsLin q hq n r x) = 0 :=
    SourcePairedPlaneIdentification.sqrtMultiplier_isDatum_zero ci (SourcePairedInclusion.shell q hq n r)
      hd.symm (RestrictedTEPlaneLocal.electric x) _ (RestrictedTEActualCore.fs_isDatum q hq n r x)
  have hfi0 : StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r)
      (RestrictedTEActualCore.fiLin ci dci x) = 0 :=
    SourcePairedPlaneIdentification.sqrtMultiplier_isDatum_zero (SourcePairedInclusion.shell q hq n r) ci hd
      (RestrictedTEPlaneLocal.electric x) _ (RestrictedTEActualCore.fi_isDatum ci dci x)
  have hxR : ‖MaxwellPlaneTail.planePoint ξ‖ < (SourcePairedInclusion.data q hq n r).R := by
    rw [MaxwellPlaneTail.planePoint_norm]
    exact hξ
  have hbg := backgroundElectric_eq_bgFieldE q hq n r x (MaxwellPlaneTail.planePoint ξ) hξ0 hxR
  funext i
  have hid := SourcePairedPlaneIdentification.combined_total_electric_eq q hq n r ci b hs.hb hs.hci dci hE
    (RestrictedTEPlaneLocal.electric x) (RestrictedTEActualCore.fsLin q hq n r x)
    (RestrictedTEActualCore.fiLin ci dci x) hfi0 hfs0 η hs.hη (MaxwellPlaneTail.planePoint ξ) hxR
    (RestrictedTEActualCore.carrier_dist hs ξ) i
  have e := congrFun hbg i
  change SourcePairedPlaneIdentification.continuousTotalElectric _ _ _ _ _ i = _
  rw [hid]
  simp only [Pi.add_apply, SourcePairedPlaneCompact.pairedPlaneElectric,
    RestrictedTEActualPiecewise.inclSolution, e, Pi.zero_apply, PiLp.zero_apply]
  ring

/-- **The core magnetic field is the background plus the inclusion part.** -/
theorem coreH_eq (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b η : ℝ)
    (hs : RestrictedTEActualCore.CoreSetup q hq n r ci dci b η)
    (hE : IsUnit (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)) (x : Vec)
    (ξ : PlaneInverseCube.Plane) (hξ : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R)
    (hξ0 : MaxwellPlaneTail.planePoint ξ ≠ 0) :
    RestrictedTEActualCore.coreH q hq n r ci dci x ξ =
      RestrictedTEActualPiecewise.bgFieldH q hq n r x (MaxwellPlaneTail.planePoint ξ) +
        SourcePairedPlaneMagnetic.pairedPlaneMagnetic q hq n r ci
          (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x) 0
          (MaxwellPlaneTail.planePoint ξ) := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hs.hb.le hs.hci
  have hfs0 : StaticCoefficient.sqrtMultiplier ci (RestrictedTEActualCore.fsLin q hq n r x) = 0 :=
    SourcePairedPlaneIdentification.sqrtMultiplier_isDatum_zero ci (SourcePairedInclusion.shell q hq n r)
      hd.symm (RestrictedTEPlaneLocal.electric x) _ (RestrictedTEActualCore.fs_isDatum q hq n r x)
  have hfi0 : StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r)
      (RestrictedTEActualCore.fiLin ci dci x) = 0 :=
    SourcePairedPlaneIdentification.sqrtMultiplier_isDatum_zero (SourcePairedInclusion.shell q hq n r) ci hd
      (RestrictedTEPlaneLocal.electric x) _ (RestrictedTEActualCore.fi_isDatum ci dci x)
  have hxR : ‖MaxwellPlaneTail.planePoint ξ‖ < (SourcePairedInclusion.data q hq n r).R := by
    rw [MaxwellPlaneTail.planePoint_norm]
    exact hξ
  have hbg := backgroundMagnetic_eq_bgFieldH q hq n r x (MaxwellPlaneTail.planePoint ξ) hξ0 hxR
  funext i
  have hid := SourcePairedPlaneIdentification.combined_total_magnetic_eq q hq n r ci b hs.hb hs.hci dci hE
    (RestrictedTEPlaneLocal.magnetic x) (RestrictedTEActualCore.fsLin q hq n r x)
    (RestrictedTEActualCore.fiLin ci dci x) hfi0 hfs0 η hs.hη (MaxwellPlaneTail.planePoint ξ) hxR
    (RestrictedTEActualCore.carrier_dist hs ξ) i
  have e := congrFun hbg i
  change SourcePairedPlaneIdentification.continuousTotalMagnetic _ _ _ _ _ i = _
  rw [hid]
  simp only [Pi.add_apply, SourcePairedPlaneMagnetic.pairedPlaneMagnetic,
    RestrictedTEActualPiecewise.inclSolution, e, Pi.zero_apply, PiLp.zero_apply]
  ring


/-! ### The uniform flux majorant -/

/-- Monotonicity of the flux constant in the norm of the inclusion solution. -/
theorem flux_arith (K a b d u U : ℝ) (hK : 0 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hu : 0 ≤ u)
    (huU : u ≤ U) :
    2 * (0 + (0 + K * u)) * (b + (0 + 3 * K * u)) + 2 * (a + (0 + 3 * K * u)) * (d + (0 + K * u)) ≤
      2 * (K * U) * (b + 3 * K * U) + 2 * (a + 3 * K * U) * (d + K * U) := by
  have hU : 0 ≤ U := hu.trans huU
  have hKu : K * u ≤ K * U := mul_le_mul_of_nonneg_left huU hK
  have h3 : 3 * K * u ≤ 3 * K * U := by nlinarith
  have h1 : 0 ≤ K * u := mul_nonneg hK hu
  have h2 : 0 ≤ b + 3 * K * u := by positivity
  have h4 : 0 ≤ a + 3 * K * u := by positivity
  have h5 : 0 ≤ d + K * u := by positivity
  have h6 : 0 ≤ K * U := mul_nonneg hK hU
  have h7 : 0 ≤ b + 3 * K * U := by positivity
  nlinarith [mul_le_mul hKu (add_le_add_left h3 b) h2 h6,
    mul_le_mul (add_le_add_left h3 a) (add_le_add_left hKu d) h5 (by positivity)]

/-- **The uniform inverse-cube flux majorant of the core fields (general inclusion).**  Let `ci` be an inclusion
with support data `dci` whose carrier lies in the ball of radius `b` and at height at least `η > 0` from the plane,
and suppose the limiting effective block is a unit.  Then for every orthonormal family `B`, there are `C1`, `ρ1`
and `r1` such that for all shell indices `r ≥ r1`, every unit-power vector `x` of the span of `B` and every plane
point `ξ` with `ρ1 ≤ ‖ξ‖ < radius r`, the normal component of `coreE x ξ × conj (coreH x ξ)` is at most
`C1 / ‖ξ‖³`. -/
theorem core_majorant_general (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b η : ℝ) (hb0 : 0 < b)
    (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b) (hη : 0 < η) (hgap : ∀ y ∈ dci.carrier, η ≤ |y 2|)
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci dci b hb0))
    (N : Nat) (B : Fin N → Vec) (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (B k))) :
    ∃ (C1 ρ1 : ℝ) (r1 : ℕ), ∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range B),
      RestrictedTEIncoming.physicalPower x = 1 →
        ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ → ‖ξ‖ < RadialPhaseLimit.radius r →
          ‖crossProduct (RestrictedTEActualCore.coreE q hq n r ci dci x ξ)
            (Maxwell.conjugate (RestrictedTEActualCore.coreH q hq n r ci dci x ξ)) 2‖ ≤ C1 / ‖ξ‖ ^ 3 := by
  obtain ⟨ρb, K1, L1, L2, hρb, hbg⟩ :=
    RestrictedTEActualPiecewise.background_decomp_unit_sphere q hq n B horth
  obtain ⟨U, r0, hU⟩ :=
    RestrictedTEActualPiecewise.solution_bounded_on_sphere q hq n ci dci b hb0 hcar hL B horth
  have hρ1c : CoreRadiatedMajorant.coreMin q b ≤ max (CoreRadiatedMajorant.coreMin q b) ρb := le_max_left _ _
  have hρ1b : ρb ≤ max (CoreRadiatedMajorant.coreMin q b) ρb := le_max_right _ _
  have hρ2 : 2 ≤ max (CoreRadiatedMajorant.coreMin q b) ρb :=
    (CoreRadiatedMajorant.two_le_coreMin q b).trans hρ1c
  obtain ⟨K, hK, hev⟩ := CoreRadiatedMajorant.core_total_decomp q hq n ci dci b hb0.le hcar
    (max (CoreRadiatedMajorant.coreMin q b) ρb) hρ1c (fun _ => 0) (fun _ => 0) 0 0 0 0
    (fun r x _ => decomp_zero x) (fun r x _ => decomp_zero x)
  obtain ⟨ra, hra⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨rb, hrb⟩ := Filter.eventually_atTop.mp (SourcePairedReduction.eventually_inner_radius q hq n b)
  obtain ⟨rc, hrc⟩ := Filter.eventually_atTop.mp
    (SourcePairedReduction.eventually_effective_isUnit q hq n ci dci b hb0 hcar hL)
  refine ⟨2 * (K * max U 0) * (max L1 0 + 3 * K * max U 0) +
      2 * (max K1 0 + 3 * K * max U 0) * (max L2 0 + K * max U 0),
    max (CoreRadiatedMajorant.coreMin q b) ρb + 1, max (max ra rb) (max rc r0), ?_⟩
  intro r hr x hx hp ξ hξ1 hξ2
  have hra1 : ra ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hr)
  have hrb1 : rb ≤ r := (le_max_right _ _).trans ((le_max_left _ _).trans hr)
  have hrc1 : rc ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hr)
  have hr01 : r0 ≤ r := (le_max_right _ _).trans ((le_max_right _ _).trans hr)
  have hyn : ‖MaxwellPlaneTail.planePoint ξ‖ = ‖ξ‖ := MaxwellPlaneTail.planePoint_norm ξ
  have hy2 : MaxwellPlaneTail.planePoint ξ 2 = 0 := SourceRemotePlaneTail.planePoint_two ξ
  have hξpos : 0 < ‖ξ‖ := by linarith
  have hypos : 0 < ‖MaxwellPlaneTail.planePoint ξ‖ := by rw [hyn]; exact hξpos
  have hy0 : MaxwellPlaneTail.planePoint ξ ≠ 0 := norm_pos_iff.mp hypos
  have hlt1 : max (CoreRadiatedMajorant.coreMin q b) ρb < ‖MaxwellPlaneTail.planePoint ξ‖ := by
    rw [hyn]; linarith
  have hltb : ρb ≤ ‖MaxwellPlaneTail.planePoint ξ‖ := by rw [hyn]; linarith
  have hxR : ‖MaxwellPlaneTail.planePoint ξ‖ < (SourcePairedInclusion.data q hq n r).R := by
    rw [hyn]; exact hξ2
  have hs : RestrictedTEActualCore.CoreSetup q hq n r ci dci b η :=
    ⟨hrb r hrb1, SourcePairedReduction.inclusion_vanish ci dci b hcar, hη, hgap⟩
  have hEu := hrc r hrc1
  rw [coreE_eq q hq n r ci dci b η hs hEu x ξ hξ2 hy0, coreH_eq q hq n r ci dci b η hs hEu x ξ hξ2 hy0]
  have hu : ‖RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x‖ ≤ U := hU r hr01 x hx hp
  obtain ⟨hDE0, hDH0⟩ := hra r hra1 (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x)
    (MaxwellPlaneTail.planePoint ξ) hlt1 hxR
  obtain ⟨hbgE, hbgH⟩ := hbg r x hx hp (MaxwellPlaneTail.planePoint ξ) hltb
  have hbgE1 := OQ14.BarrierDegreeFluxConstants.decomp_mono hy0 hbgE (le_max_left K1 0) le_rfl
  have hbgH1 := OQ14.BarrierDegreeFluxConstants.decomp_mono hy0 hbgH (le_max_left L1 0) (le_max_left L2 0)
  have hDE := decomp_add hbgE1 hDE0
  have hDH := decomp_add hbgH1 hDH0
  refine (flux_bound_of_decomp _ hy2 hypos _ _ _ _ _ _ hDE hDH).trans ?_
  rw [hyn]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hu0 : 0 ≤ ‖RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x‖ := norm_nonneg _
  have hfa := flux_arith K (max K1 0) (max L1 0) (max L2 0)
    ‖RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x‖ (max U 0) hK (le_max_right _ _)
    (le_max_right _ _) (le_max_right _ _) hu0 (hu.trans (le_max_left _ _))
  linarith


/-! ### The doubled device -/

section Device

/-- **The core majorant of the doubled device.**  For a device `p` (radius `ρ`, contrast `χ`, ball of radius `R`,
height `γ`), `q > 1`, and any enclosing radius `b ≥ R`, for all large gain indices the inverse-cube majorant of the
plane flux of the core fields `coreE`, `coreH` holds on the unit-power sphere of the span of every orthonormal
family, for `ρ1 ≤ ‖ξ‖ < radius r` and all large shell index `r`. -/
theorem coreMajorant_of_device {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℝ → ι → OQ14.RestrictedTEActualCore.Sp} {ρ χ R γ : ℝ}
    (hd : OQ14.RestrictedTEActualCore.Device p ρ χ R γ) {q : ℝ} (hq : 1 < q) {b : ℝ} (hb0 : 0 < b)
    (hRb : R ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∀ (N : Nat) (B : Fin N → Vec),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (C1 ρ1 : ℝ) (r1 : ℕ),
        ∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
          ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ → ‖ξ‖ < RadialPhaseLimit.radius r →
            ‖crossProduct
                (RestrictedTEActualCore.coreE q hq.le n r
                  (RestrictedTEPartnerSmallness.deviceCoeff p ρ χ hd.hχ q n)
                  (RestrictedTEPartnerSmallness.deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) x ξ)
                (Maxwell.conjugate (RestrictedTEActualCore.coreH q hq.le n r
                  (RestrictedTEPartnerSmallness.deviceCoeff p ρ χ hd.hχ q n)
                  (RestrictedTEPartnerSmallness.deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) x ξ)) 2‖ ≤
              C1 / ‖ξ‖ ^ 3 := by
  filter_upwards [RestrictedTEPartnerSmallness.partner_limitEffective_isUnit p ρ χ R b hd.hρ hd.hχ hb0 hRb
    hd.hi q hq] with n hL
  intro N B horth
  exact core_majorant_general q hq.le n _ _ b (γ * RestrictedTEPartnerSmallness.scale q n) hb0
    (RestrictedTEActualCounting.device_carrier_le p ρ χ R b hd.hρ hd.hχ hRb hd.hi q hq n)
    (mul_pos hd.hγ (RestrictedTEPartnerSmallness.scale_pos hq n))
    (RestrictedTEActualCore.device_carrier_gap hd hq n) hL N B horth

/-- **The core majorant of the concrete doubled device** (the structure consumed by
`RestrictedTEActualPiecewise.actual_counted_subspaces_of_pieces`), with the enclosing radius `max R 1`. -/
theorem coreMajorant_device {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ) (hρh : ρ < h)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    RestrictedTEActualPiecewise.CoreMajorant r0 y ρ χ h R hρ hχ hi q hq :=
  ⟨coreMajorant_of_device (RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi) hq
    (b := max R 1) (lt_of_lt_of_le one_pos (le_max_right R 1)) (le_max_left R 1)⟩

end Device

end OQ14.CoreMajorantDevice

#print axioms OQ14.CoreMajorantDevice.teMagnetic_wave
#print axioms OQ14.CoreMajorantDevice.coefficient_scaledCoeff
#print axioms OQ14.CoreMajorantDevice.magnetic_scaledCoeff_eq
#print axioms OQ14.CoreMajorantDevice.bgFieldH_apply
#print axioms OQ14.CoreMajorantDevice.bgFieldH_core
#print axioms OQ14.CoreMajorantDevice.backgroundElectric_eq_bgFieldE
#print axioms OQ14.CoreMajorantDevice.backgroundMagnetic_eq_bgFieldH
#print axioms OQ14.CoreMajorantDevice.coreE_eq
#print axioms OQ14.CoreMajorantDevice.coreH_eq
#print axioms OQ14.CoreMajorantDevice.flux_arith
#print axioms OQ14.CoreMajorantDevice.core_majorant_general
#print axioms OQ14.CoreMajorantDevice.coreMajorant_of_device
#print axioms OQ14.CoreMajorantDevice.coreMajorant_device
