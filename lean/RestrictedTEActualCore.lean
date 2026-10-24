import RestrictedTEActualFields
import SourcePairedPlaneIdentification
import BackgroundShellCoefficient
import BackgroundCoreTransmission
import RestrictedTEEvenDatum
import RestrictedTEPartnerTransfer

/-! The inside-core actual plane fields of the paired-shell device, their convergence to the parity device, and
the counted-subspace theorem for fields converging to the twisted parity fields.

Data.  For the paired shell `cs = SourcePairedInclusion.shell q hq n r` and an inclusion `ci` with support data
`dci` (the doubled device at gain index `n`), the weighted data of a finite restricted TE coefficient vector `x`
are `fsLin x` (shell) and `fiLin x` (inclusion), linear in `x` and weighted data of the incident electric field
(`fs_isDatum`, `fi_isDatum`).  The combined solution is `MaterialField.solution (add cs ci) 1 X (fsLin x + fiLin x)`
and the assembled plane fields are
  `coreE x ξ = continuousTotalElectric (add cs ci) X (electric x) (fsLin x + fiLin x) (planePoint ξ)`,
  `coreH x ξ = continuousTotalMagnetic (add cs ci) X (magnetic x) (fsLin x + fiLin x) (planePoint ξ)`.

Core.  On the open core `‖ξ‖ < Rin` (inner shell radius) the scattered fields are bounded linear functionals of the
solution (`scatteredE_clm`, `scatteredH_clm`: the shell part through the core evaluation functional, the inclusion
part through the kernel functional at positive distance from the carrier), so the fields are linear in `x`
(`coreE_comb`) and continuous in `ξ` (`coreE_continuousOn`).  At the points of the shell itself the literal kernel
integrals carry no such structure, so the `FieldMap` versions `coreEMap`, `coreHMap` are cut off outside the core;
this does not affect any statement on a fixed disk, which lies in the core for large `r`.

Background.  The continuous electric background of the shell equals, at every point of the open core, the regular
TE field of the vector rescaled degreewise by the transmissions over two (`backgroundElectric_eq_core`: the total
field of the shell solution is a.e. the background field of the family of modes, both sides continuous); the
magnetic background equals the regular TE magnetic field (`backgroundMagnetic_eq_core`: the weak first Maxwell
equation determines a continuous magnetic field from the electric one).  The backgrounds converge uniformly on
balls (`backgroundElectric_conv`, `backgroundMagnetic_conv`), the effective datum is the datum of the rescaled
vector and converges (`effectiveDatum_conv`), and the assembled fields converge uniformly on every disk to the raw
limit, the total fields of the parity device with the datum of the vector rescaled by the limiting transmissions
(`coreE_conv_raw`, `coreH_conv_raw`, eventually in `n`: `core_conv_raw_eventually`).

Twist.  If the vector rescaled degreewise by the limiting transmissions over two is `q^n` times `w`, the raw limit
is the parity total field at scale `(q^n)⁻¹` and input `w` (`rawLimitE_eq_parity`, `rawLimitH_eq_parity`: gain
`1/a = q^n`, incident field `electric ((a⁻¹) w) = electric (q^n w)`, no further factor).  `ActualFieldEstimatesTwisted`
collects the three estimates against `twist x`; for a unitary twist the fields composed with the inverse twist
satisfy the audited estimates (`untwist_estimates`), which gives `actual_counted_subspaces_of_fields_twisted` for
the family `A_k = twist⁻¹ B_k`, and `actual_counted_subspaces_of_core` assembles it from the core identification. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEActualCore
open MeasureTheory Filter Topology Metric Set
open scoped ComplexConjugate

abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev Sp := FourierL2.Space
abbrev Vec := SymmetricHarmonicJets.Index →₀ ℂ

/-! ### Data -/

section Data
variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ)

/-- The shell datum of a coefficient vector, linear in the vector. -/
def fsLin : Vec →ₗ[ℂ] VectorL2 :=
  RestrictedTEDatumLinear.datumMap (SourcePairedInclusion.shell q hq n r)
    (BackgroundShellCoefficient.shellSupport q hq n r)

/-- The inclusion datum of a coefficient vector, linear in the vector. -/
def fiLin (ci : Coefficient) (dci : BoundedMaterialKernel.SupportData ci) : Vec →ₗ[ℂ] VectorL2 :=
  RestrictedTEDatumLinear.datumMap ci dci

theorem fsLin_apply (x : Vec) : fsLin q hq n r x =
    RestrictedTEMaterial.datum (SourcePairedInclusion.shell q hq n r)
      (BackgroundShellCoefficient.shellSupport q hq n r) x := rfl

theorem fiLin_apply (ci : Coefficient) (dci : BoundedMaterialKernel.SupportData ci) (x : Vec) :
    fiLin ci dci x = RestrictedTEMaterial.datum ci dci x := rfl

theorem fs_isDatum (x : Vec) :
    SourcePairedPlaneIdentification.IsDatum (SourcePairedInclusion.shell q hq n r)
      (RestrictedTEPlaneLocal.electric x) (fsLin q hq n r x) :=
  fun i => RestrictedTEMaterial.datum_actual _ _ x i

theorem fi_isDatum (ci : Coefficient) (dci : BoundedMaterialKernel.SupportData ci) (x : Vec) :
    SourcePairedPlaneIdentification.IsDatum ci (RestrictedTEPlaneLocal.electric x) (fiLin ci dci x) :=
  fun i => RestrictedTEMaterial.datum_actual _ _ x i

end Data

/-! ### The setting of the core -/

/-- The core setting: the inclusion `ci` (support data `dci`) vanishes outside the ball of radius `b`, which lies
inside the inner radius of the shell, and its carrier stays at height at least `η > 0` from the plane. -/
structure CoreSetup (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b η : ℝ) : Prop where
  hb : b < (SourcePairedInclusion.data q hq n r).R
  hci : ∀ y : Sp, y ∉ closedBall (0 : Sp) b → ci.value (VectorFourier.coordinateMap y) = 0
  hη : 0 < η
  hgap : ∀ y ∈ dci.carrier, η ≤ |y 2|

section Core
variable {q : ℝ} {hq : 1 ≤ q} {n r : ℕ} {ci : Coefficient} {dci : BoundedMaterialKernel.SupportData ci}
  {b η : ℝ}

/-- Plane points at height `≥ η` from the plane carrier are at distance `≥ η` from every plane point. -/
theorem carrier_dist (hs : CoreSetup q hq n r ci dci b η) (ξ : PlaneInverseCube.Plane) :
    ∀ y ∈ dci.carrier, η ≤ ‖MaxwellPlaneTail.planePoint ξ - y‖ :=
  fun y hy => PlaneSourceKernel.gap_distance η ξ y (hs.hgap y hy)

theorem incl_admissible (hs : CoreSetup q hq n r ci dci b η) (u : VectorL2) :
    PlaneSourceKernel.Admissible b η (DynamicVolume.source ci u) := by
  refine ⟨fun j => DynamicVolume.source_integrable ci u b hs.hci j,
    fun j y hy => DynamicVolume.source_zero ci u b hs.hci j y hy, ?_⟩
  intro j y hy
  apply hs.hgap
  by_contra hn
  apply hy
  unfold DynamicVolume.source
  rw [dci.carrierZero y hn]
  simp

theorem shell_hcs' (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) :
    ∀ y : Sp, y ∉ closedBall (0 : Sp) (SourcePairedInclusion.data q hq n r).X \
        ball (0 : Sp) (SourcePairedInclusion.data q hq n r).R →
      (SourcePairedInclusion.shell q hq n r).value (VectorFourier.coordinateMap y) = 0 :=
  SourcePairedPlaneIdentification.shell_hcs q hq n r

/-- The scattered electric field of the combined source splits into the shell and inclusion parts at every point of
the core at distance at least `η` from the carrier of the inclusion. -/
theorem electric_split (hs : CoreSetup q hq n r ci dci b η) (u : VectorL2) (x : Sp)
    (hx : ‖x‖ < (SourcePairedInclusion.data q hq n r).R) (hxη : ∀ y ∈ dci.carrier, η ≤ ‖x - y‖)
    (i : Fin 3) :
    ExteriorContinuity.electric 1
        (DynamicVolume.source (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) u) x i =
      ExteriorContinuity.electric 1 (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) u) x i +
        ExteriorContinuity.electric 1 (DynamicVolume.source ci u) x i := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hs.hb.le hs.hci
  have hcs := shell_hcs' q hq n r
  have hsplit := SourcePairedPlaneIdentification.response_sum_split (fun j z => DyadicKernel.dyadic 1 z i j) x
    (SourcePairedInclusion.shell q hq n r) ci (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci)
    u u u
    (fun j => Eventually.of_forall (fun y => SourcePairedPlaneIdentification.source_add_disjoint
      (SourcePairedInclusion.shell q hq n r) ci hd u j y))
    (fun j => CoreMaterialEvaluation.actual_integrand_integrable (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx i j u)
    (fun j => SourcePairedPlaneIdentification.response_integrand_integrable ci dci
      (fun z => DyadicKernel.dyadic 1 z i j) (PlaneSourceKernel.dyadic_measurable 1 i j) x
      (|NewtonStripMaxwell.electricBound 1 (2 * η)|)
      (fun y hy => (NewtonStripMaxwell.electric_bound 1 (2 * η) (by linarith [hs.hη]) (x - y)
        (by have := hxη y hy; linarith) i j).trans (le_abs_self _)) u j)
  exact hsplit

/-- The scattered magnetic field of the combined source splits into the shell and inclusion parts. -/
theorem magnetic_split (hs : CoreSetup q hq n r ci dci b η) (u : VectorL2) (x : Sp)
    (hx : ‖x‖ < (SourcePairedInclusion.data q hq n r).R) (hxη : ∀ y ∈ dci.carrier, η ≤ ‖x - y‖)
    (i : Fin 3) :
    MagneticResponse.magnetic 1
        (DynamicVolume.source (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) u) x i =
      MagneticResponse.magnetic 1 (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) u) x i +
        MagneticResponse.magnetic 1 (DynamicVolume.source ci u) x i := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hs.hb.le hs.hci
  have hcs := shell_hcs' q hq n r
  have hB1 := SourcePairedPlaneIdentification.magnetic_annulus_bound (SourcePairedInclusion.shell q hq n r)
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx
  have hsplit := SourcePairedPlaneIdentification.response_sum_split
    (fun j z => SphereMagneticKernel.magneticDyadic 1 z i j) x
    (SourcePairedInclusion.shell q hq n r) ci (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci)
    u u u
    (fun j => Eventually.of_forall (fun y => SourcePairedPlaneIdentification.source_add_disjoint
      (SourcePairedInclusion.shell q hq n r) ci hd u j y))
    (fun j => SourcePairedPlaneIdentification.response_integrand_integrable (SourcePairedInclusion.shell q hq n r)
      (CoreMaterialEvaluation.supportData (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs)
      (fun z => SphereMagneticKernel.magneticDyadic 1 z i j)
      (SourcePairedPlaneIdentification.measurable_magneticDyadic i j) x _
      (fun y hy => hB1 y hy i j) u j)
    (fun j => SourcePairedPlaneIdentification.response_integrand_integrable ci dci
      (fun z => SphereMagneticKernel.magneticDyadic 1 z i j)
      (SourcePairedPlaneIdentification.measurable_magneticDyadic i j) x
      (2 * NewtonStripMaxwell.gradientBound 1 (2 * η))
      (fun y hy => SourcePairedPlaneIdentification.magneticDyadic_bound (x - y) (2 * η)
        (by linarith [hs.hη]) (by have := hxη y hy; linarith) i j) u j)
  rw [SourcePairedPlaneMagnetic.magnetic_eq_sum, SourcePairedPlaneMagnetic.magnetic_eq_sum,
    SourcePairedPlaneMagnetic.magnetic_eq_sum]
  exact hsplit

/-- The scattered electric field of the combined source at such a point is a bounded linear functional of the
solution. -/
theorem scatteredE_clm (hs : CoreSetup q hq n r ci dci b η) (x : Sp)
    (hx : ‖x‖ < (SourcePairedInclusion.data q hq n r).R) (hxη : ∀ y ∈ dci.carrier, η ≤ ‖x - y‖)
    (i : Fin 3) :
    ∃ L : VectorL2 →L[ℂ] ℂ, ∀ u : VectorL2, L u = ExteriorContinuity.electric 1
      (DynamicVolume.source (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) u) x i := by
  have hcs := shell_hcs' q hq n r
  refine ⟨CoreMaterialEvaluation.evaluation (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx i +
    ∑ j : Fin 3, SourcePairedPlaneIdentification.kernelFunctional ci dci
      (fun z => DyadicKernel.dyadic 1 z i j) (PlaneSourceKernel.dyadic_measurable 1 i j) x
      (|NewtonStripMaxwell.electricBound 1 (2 * η)|)
      (fun y hy => (NewtonStripMaxwell.electric_bound 1 (2 * η) (by linarith [hs.hη]) (x - y)
        (by have := hxη y hy; linarith) i j).trans (le_abs_self _)) (abs_nonneg _) j, ?_⟩
  intro u
  rw [electric_split hs u x hx hxη i, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
  simp only [SourcePairedPlaneIdentification.kernelFunctional_apply]
  rw [CoreMaterialEvaluation.evaluation_actual]
  rfl

/-- The scattered magnetic field of the combined source at such a point is a bounded linear functional of the
solution. -/
theorem scatteredH_clm (hs : CoreSetup q hq n r ci dci b η) (x : Sp)
    (hx : ‖x‖ < (SourcePairedInclusion.data q hq n r).R) (hxη : ∀ y ∈ dci.carrier, η ≤ ‖x - y‖)
    (i : Fin 3) :
    ∃ L : VectorL2 →L[ℂ] ℂ, ∀ u : VectorL2, L u = MagneticResponse.magnetic 1
      (DynamicVolume.source (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) u) x i := by
  have hcs := shell_hcs' q hq n r
  have hB1 := SourcePairedPlaneIdentification.magnetic_annulus_bound (SourcePairedInclusion.shell q hq n r)
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx
  have hB10 := SourcePairedPlaneIdentification.magnetic_annulus_bound_nonneg
    (SourcePairedInclusion.data q hq n r).R x hx
  refine ⟨SourcePairedPlaneIdentification.magneticEvaluation (SourcePairedInclusion.shell q hq n r)
      (CoreMaterialEvaluation.supportData (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs) x _ hB10 hB1 i +
    ∑ j : Fin 3, SourcePairedPlaneIdentification.kernelFunctional ci dci
      (fun z => SphereMagneticKernel.magneticDyadic 1 z i j)
      (SourcePairedPlaneIdentification.measurable_magneticDyadic i j) x
      (|2 * NewtonStripMaxwell.gradientBound 1 (2 * η)|)
      (fun y hy => (SourcePairedPlaneIdentification.magneticDyadic_bound (x - y) (2 * η)
        (by linarith [hs.hη]) (by have := hxη y hy; linarith) i j).trans (le_abs_self _)) (abs_nonneg _) j, ?_⟩
  intro u
  rw [magnetic_split hs u x hx hxη i, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    SourcePairedPlaneIdentification.magneticEvaluation_apply]
  simp only [SourcePairedPlaneIdentification.kernelFunctional_apply]
  rw [SourcePairedPlaneMagnetic.magnetic_eq_sum 1 (DynamicVolume.source ci u) x i]
  rfl

end Core

/-! ### The shell source in the core -/

section ShellCore
variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ)

theorem shell_vanish_outer (y : Sp) (hy : y ∉ closedBall (0 : Sp) (SourcePairedInclusion.data q hq n r).X) :
    (SourcePairedInclusion.shell q hq n r).value (VectorFourier.coordinateMap y) = 0 :=
  SourcePairedInclusion.shell_support q hq n r y hy

theorem shell_source_vanish_inner (u : VectorL2) (j : Fin 3) (y : Sp)
    (hy : y ∈ ball (0 : Sp) (SourcePairedInclusion.data q hq n r).R) :
    DynamicVolume.source (SourcePairedInclusion.shell q hq n r) u j y = 0 := by
  unfold DynamicVolume.source
  rw [shell_hcs' q hq n r y (fun h => h.2 hy)]
  simp

/-- The electric field of the shell polarization is smooth in the core. -/
theorem shell_electric_contDiffAt (u : VectorL2) (x : Sp)
    (hx : ‖x‖ < (SourcePairedInclusion.data q hq n r).R) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ExteriorContinuity.electric 1
      (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) u) y i) x :=
  ConicalInteriorResponse.electric_smooth_interior 1 (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) u)
    (fun j => DynamicVolume.source_integrable _ u (SourcePairedInclusion.data q hq n r).X
      (shell_vanish_outer q hq n r) j)
    (fun j => MaterialField.source_compact _ u (SourcePairedInclusion.data q hq n r).X
      (shell_vanish_outer q hq n r) j)
    (SourcePairedInclusion.data q hq n r).R (fun j y hy => shell_source_vanish_inner q hq n r u j y hy) i x
    (mem_ball_zero_iff.mpr hx)

/-- The magnetic field of the shell polarization is smooth in the core. -/
theorem shell_magnetic_contDiffAt (u : VectorL2) (x : Sp)
    (hx : ‖x‖ < (SourcePairedInclusion.data q hq n r).R) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => MagneticResponse.magnetic 1
      (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) u) y i) x := by
  have hρ := fun j => DynamicVolume.source_integrable (SourcePairedInclusion.shell q hq n r) u
    (SourcePairedInclusion.data q hq n r).X (shell_vanish_outer q hq n r) j
  have hc := fun j => MaterialField.source_compact (SourcePairedInclusion.shell q hq n r) u
    (SourcePairedInclusion.data q hq n r).X (shell_vanish_outer q hq n r) j
  have hxb : x ∈ ball (0 : Sp) (SourcePairedInclusion.data q hq n r).R := mem_ball_zero_iff.mpr hx
  have hex (j : Fin 3) : x ∉ tsupport (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) u j) :=
    ConicalInteriorResponse.source_excluded _ _ (fun y hy => shell_source_vanish_inner q hq n r u j y hy) x hxb
  exact contDiffAt_const.mul
    ((CompactResponseSmooth.response_contDiffAt _ _
      (ExteriorSmooth.gradient_contDiffAt 1 (WeakCurl.next i)) (hρ (WeakCurl.previous i))
      (hc (WeakCurl.previous i)) x (hex (WeakCurl.previous i))).sub
    (CompactResponseSmooth.response_contDiffAt _ _
      (ExteriorSmooth.gradient_contDiffAt 1 (WeakCurl.previous i)) (hρ (WeakCurl.next i))
      (hc (WeakCurl.next i)) x (hex (WeakCurl.next i))))

end ShellCore

/-! ### The core fields -/

section Fields
variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (dci : BoundedMaterialKernel.SupportData ci)

/-- The combined solution for the input `x`. -/
def coreSol (x : Vec) : VectorL2 :=
  MaterialField.solution (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
    (SourcePairedInclusion.data q hq n r).X (fsLin q hq n r x + fiLin ci dci x)

/-- The assembled electric plane field of the combined shell-plus-inclusion solution. -/
def coreE (x : Vec) (ξ : PlaneInverseCube.Plane) : Maxwell.Vector :=
  SourcePairedPlaneIdentification.continuousTotalElectric
    (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci)
    (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.electric x)
    (fsLin q hq n r x + fiLin ci dci x) (MaxwellPlaneTail.planePoint ξ)

/-- The assembled magnetic plane field of the combined shell-plus-inclusion solution. -/
def coreH (x : Vec) (ξ : PlaneInverseCube.Plane) : Maxwell.Vector :=
  SourcePairedPlaneIdentification.continuousTotalMagnetic
    (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci)
    (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.magnetic x)
    (fsLin q hq n r x + fiLin ci dci x) (MaxwellPlaneTail.planePoint ξ)

theorem coreE_apply (x : Vec) (ξ : PlaneInverseCube.Plane) (i : Fin 3) :
    coreE q hq n r ci dci x ξ i = RestrictedTEPlaneLocal.electric x (MaxwellPlaneTail.planePoint ξ) i +
      ExteriorContinuity.electric 1 (DynamicVolume.source
        (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) (coreSol q hq n r ci dci x))
        (MaxwellPlaneTail.planePoint ξ) i := rfl

theorem coreH_apply (x : Vec) (ξ : PlaneInverseCube.Plane) (i : Fin 3) :
    coreH q hq n r ci dci x ξ i = RestrictedTEPlaneLocal.magnetic x (MaxwellPlaneTail.planePoint ξ) i +
      MagneticResponse.magnetic 1 (DynamicVolume.source
        (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) (coreSol q hq n r ci dci x))
        (MaxwellPlaneTail.planePoint ξ) i := rfl

theorem coreSol_comb (x w : Vec) (z : ℂ) :
    coreSol q hq n r ci dci (x + z • w) = coreSol q hq n r ci dci x + z • coreSol q hq n r ci dci w := by
  have h : fsLin q hq n r (x + z • w) + fiLin ci dci (x + z • w) =
      (fsLin q hq n r x + fiLin ci dci x) + z • (fsLin q hq n r w + fiLin ci dci w) := by
    simp only [map_add, map_smul, smul_add]
    abel
  unfold coreSol MaterialField.solution
  rw [h, map_add, map_smul]

theorem electric_comb' (x w : Vec) (z : ℂ) :
    RestrictedTEPlaneLocal.electric (x + z • w) =
      RestrictedTEPlaneLocal.electric x + z • RestrictedTEPlaneLocal.electric w := by
  rw [← RestrictedTEFieldLinear.electricMap_apply, map_add, map_smul, RestrictedTEFieldLinear.electricMap_apply,
    RestrictedTEFieldLinear.electricMap_apply]

theorem magnetic_comb' (x w : Vec) (z : ℂ) :
    RestrictedTEPlaneLocal.magnetic (x + z • w) =
      RestrictedTEPlaneLocal.magnetic x + z • RestrictedTEPlaneLocal.magnetic w := by
  rw [← RestrictedTEFieldLinear.magneticMap_apply, map_add, map_smul, RestrictedTEFieldLinear.magneticMap_apply,
    RestrictedTEFieldLinear.magneticMap_apply]

variable {q} {hq} {n} {r} {ci} {dci} {b η : ℝ}

/-- On the open core the assembled electric field is linear in the input (in the combination form). -/
theorem coreE_comb (hs : CoreSetup q hq n r ci dci b η) (ξ : PlaneInverseCube.Plane)
    (hξ : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R) (x w : Vec) (z : ℂ) :
    coreE q hq n r ci dci (x + z • w) ξ = coreE q hq n r ci dci x ξ + z • coreE q hq n r ci dci w ξ := by
  funext i
  obtain ⟨L, hL⟩ := scatteredE_clm hs (MaxwellPlaneTail.planePoint ξ)
    (by rwa [MaxwellPlaneTail.planePoint_norm]) (carrier_dist hs ξ) i
  rw [Pi.add_apply, Pi.smul_apply, coreE_apply, coreE_apply, coreE_apply, ← hL, ← hL, ← hL, coreSol_comb, map_add,
    map_smul, electric_comb']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem coreH_comb (hs : CoreSetup q hq n r ci dci b η) (ξ : PlaneInverseCube.Plane)
    (hξ : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R) (x w : Vec) (z : ℂ) :
    coreH q hq n r ci dci (x + z • w) ξ = coreH q hq n r ci dci x ξ + z • coreH q hq n r ci dci w ξ := by
  funext i
  obtain ⟨L, hL⟩ := scatteredH_clm hs (MaxwellPlaneTail.planePoint ξ)
    (by rwa [MaxwellPlaneTail.planePoint_norm]) (carrier_dist hs ξ) i
  rw [Pi.add_apply, Pi.smul_apply, coreH_apply, coreH_apply, coreH_apply, ← hL, ← hL, ← hL, coreSol_comb, map_add,
    map_smul, magnetic_comb']
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem coreE_zero (hs : CoreSetup q hq n r ci dci b η) (ξ : PlaneInverseCube.Plane)
    (hξ : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R) : coreE q hq n r ci dci 0 ξ = 0 := by
  funext i
  obtain ⟨L, hL⟩ := scatteredE_clm hs (MaxwellPlaneTail.planePoint ξ)
    (by rwa [MaxwellPlaneTail.planePoint_norm]) (carrier_dist hs ξ) i
  have h0 : coreSol q hq n r ci dci 0 = 0 := by
    unfold coreSol MaterialField.solution
    simp
  rw [coreE_apply, ← hL, h0, map_zero]
  have he : RestrictedTEPlaneLocal.electric (0 : Vec) = 0 := by
    rw [← RestrictedTEFieldLinear.electricMap_apply, map_zero]
  rw [he]
  simp

theorem coreH_zero (hs : CoreSetup q hq n r ci dci b η) (ξ : PlaneInverseCube.Plane)
    (hξ : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R) : coreH q hq n r ci dci 0 ξ = 0 := by
  funext i
  obtain ⟨L, hL⟩ := scatteredH_clm hs (MaxwellPlaneTail.planePoint ξ)
    (by rwa [MaxwellPlaneTail.planePoint_norm]) (carrier_dist hs ξ) i
  have h0 : coreSol q hq n r ci dci 0 = 0 := by
    unfold coreSol MaterialField.solution
    simp
  rw [coreH_apply, ← hL, h0, map_zero]
  have he : RestrictedTEPlaneLocal.magnetic (0 : Vec) = 0 := by
    rw [← RestrictedTEFieldLinear.magneticMap_apply, map_zero]
  rw [he]
  simp

/-- The electric core field, cut off outside the core, as a linear field family. -/
def coreEMap (hs : CoreSetup q hq n r ci dci b η) : RestrictedTEActualFields.FieldMap where
  toFun x ξ := if ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R then coreE q hq n r ci dci x ξ else 0
  map_add' x w := by
    funext ξ
    by_cases h : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R
    · simp only [h, if_true, Pi.add_apply]
      have := coreE_comb hs ξ h x w 1
      simpa using this
    · simp [h]
  map_smul' z x := by
    funext ξ
    by_cases h : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R
    · simp only [h, if_true, Pi.smul_apply, RingHom.id_apply]
      have := coreE_comb hs ξ h 0 x z
      rwa [zero_add, coreE_zero hs ξ h, zero_add] at this
    · simp [h]

/-- The magnetic core field, cut off outside the core, as a linear field family. -/
def coreHMap (hs : CoreSetup q hq n r ci dci b η) : RestrictedTEActualFields.FieldMap where
  toFun x ξ := if ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R then coreH q hq n r ci dci x ξ else 0
  map_add' x w := by
    funext ξ
    by_cases h : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R
    · simp only [h, if_true, Pi.add_apply]
      have := coreH_comb hs ξ h x w 1
      simpa using this
    · simp [h]
  map_smul' z x := by
    funext ξ
    by_cases h : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R
    · simp only [h, if_true, Pi.smul_apply, RingHom.id_apply]
      have := coreH_comb hs ξ h 0 x z
      rwa [zero_add, coreH_zero hs ξ h, zero_add] at this
    · simp [h]

theorem coreEMap_apply (hs : CoreSetup q hq n r ci dci b η) (x : Vec) (ξ : PlaneInverseCube.Plane)
    (hξ : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R) :
    coreEMap hs x ξ = coreE q hq n r ci dci x ξ := by
  change (if ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R then coreE q hq n r ci dci x ξ else 0) = _
  rw [if_pos hξ]

theorem coreHMap_apply (hs : CoreSetup q hq n r ci dci b η) (x : Vec) (ξ : PlaneInverseCube.Plane)
    (hξ : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R) :
    coreHMap hs x ξ = coreH q hq n r ci dci x ξ := by
  change (if ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R then coreH q hq n r ci dci x ξ else 0) = _
  rw [if_pos hξ]

end Fields

/-! ### Continuity and measurability on the core -/

section Continuity
variable {q : ℝ} {hq : 1 ≤ q} {n r : ℕ} {ci : Coefficient} {dci : BoundedMaterialKernel.SupportData ci}
  {b η : ℝ}

theorem coreE_continuousOn (hs : CoreSetup q hq n r ci dci b η) (x : Vec) (i : Fin 3) :
    ContinuousOn (fun ξ => coreE q hq n r ci dci x ξ i)
      {ξ : PlaneInverseCube.Plane | ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R} := by
  set u := coreSol q hq n r ci dci x with hu
  have hsplit : ∀ ξ ∈ {ξ : PlaneInverseCube.Plane | ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R},
      coreE q hq n r ci dci x ξ i =
        (RestrictedTEPlaneLocal.electric x (MaxwellPlaneTail.planePoint ξ) i +
          ExteriorContinuity.electric 1 (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) u)
            (MaxwellPlaneTail.planePoint ξ) i) +
        ExteriorContinuity.electric 1 (DynamicVolume.source ci u) (MaxwellPlaneTail.planePoint ξ) i := by
    intro ξ hξ
    rw [coreE_apply, electric_split hs u (MaxwellPlaneTail.planePoint ξ)
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact hξ) (carrier_dist hs ξ) i]
    ring
  have h1 : Continuous fun ξ : PlaneInverseCube.Plane =>
      RestrictedTEPlaneLocal.electric x (MaxwellPlaneTail.planePoint ξ) i :=
    (RestrictedTEPlaneJets.electric_continuous x i).comp MaxwellPlaneTail.planePoint_continuous
  have h3 : Continuous fun ξ : PlaneInverseCube.Plane =>
      ExteriorContinuity.electric 1 (DynamicVolume.source ci u) (MaxwellPlaneTail.planePoint ξ) i :=
    PlaneSourceKernel.electric_plane_continuous 1 b η hs.hη (DynamicVolume.source ci u)
      (incl_admissible hs u) i
  have h2 : ContinuousOn (fun ξ : PlaneInverseCube.Plane =>
      ExteriorContinuity.electric 1 (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) u)
        (MaxwellPlaneTail.planePoint ξ) i)
      {ξ : PlaneInverseCube.Plane | ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R} := by
    intro ξ hξ
    have hx : ‖MaxwellPlaneTail.planePoint ξ‖ < (SourcePairedInclusion.data q hq n r).R := by
      rw [MaxwellPlaneTail.planePoint_norm]
      exact hξ
    exact ((shell_electric_contDiffAt q hq n r u (MaxwellPlaneTail.planePoint ξ) hx i).continuousAt.comp
      MaxwellPlaneTail.planePoint_continuous.continuousAt).continuousWithinAt
  exact ((h1.continuousOn.add h2).add h3.continuousOn).congr hsplit

theorem coreH_continuousOn (hs : CoreSetup q hq n r ci dci b η) (x : Vec) (i : Fin 3) :
    ContinuousOn (fun ξ => coreH q hq n r ci dci x ξ i)
      {ξ : PlaneInverseCube.Plane | ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R} := by
  set u := coreSol q hq n r ci dci x with hu
  have hsplit : ∀ ξ ∈ {ξ : PlaneInverseCube.Plane | ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R},
      coreH q hq n r ci dci x ξ i =
        (RestrictedTEPlaneLocal.magnetic x (MaxwellPlaneTail.planePoint ξ) i +
          MagneticResponse.magnetic 1 (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) u)
            (MaxwellPlaneTail.planePoint ξ) i) +
        MagneticResponse.magnetic 1 (DynamicVolume.source ci u) (MaxwellPlaneTail.planePoint ξ) i := by
    intro ξ hξ
    rw [coreH_apply, magnetic_split hs u (MaxwellPlaneTail.planePoint ξ)
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact hξ) (carrier_dist hs ξ) i]
    ring
  have h1 : Continuous fun ξ : PlaneInverseCube.Plane =>
      RestrictedTEPlaneLocal.magnetic x (MaxwellPlaneTail.planePoint ξ) i :=
    (RestrictedTEMagnetic.magnetic_continuous x i).comp MaxwellPlaneTail.planePoint_continuous
  have h3 : Continuous fun ξ : PlaneInverseCube.Plane =>
      MagneticResponse.magnetic 1 (DynamicVolume.source ci u) (MaxwellPlaneTail.planePoint ξ) i :=
    PlaneSourceKernel.magnetic_plane_continuous 1 b η hs.hη (DynamicVolume.source ci u)
      (incl_admissible hs u) i
  have h2 : ContinuousOn (fun ξ : PlaneInverseCube.Plane =>
      MagneticResponse.magnetic 1 (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) u)
        (MaxwellPlaneTail.planePoint ξ) i)
      {ξ : PlaneInverseCube.Plane | ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R} := by
    intro ξ hξ
    have hx : ‖MaxwellPlaneTail.planePoint ξ‖ < (SourcePairedInclusion.data q hq n r).R := by
      rw [MaxwellPlaneTail.planePoint_norm]
      exact hξ
    exact ((shell_magnetic_contDiffAt q hq n r u (MaxwellPlaneTail.planePoint ξ) hx i).continuousAt.comp
      MaxwellPlaneTail.planePoint_continuous.continuousAt).continuousWithinAt
  exact ((h1.continuousOn.add h2).add h3.continuousOn).congr hsplit

theorem core_set_measurable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) :
    MeasurableSet {ξ : PlaneInverseCube.Plane | ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R} :=
  (isOpen_lt continuous_norm continuous_const).measurableSet

/-- The coordinates of the cut-off electric core field are a.e.-strongly measurable on the plane. -/
theorem coreEMap_meas (hs : CoreSetup q hq n r ci dci b η) (x : Vec) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ => coreEMap hs x ξ i) volume := by
  have heq : (fun ξ => coreEMap hs x ξ i) =
      Set.indicator {ξ : PlaneInverseCube.Plane | ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R}
        (fun ξ => coreE q hq n r ci dci x ξ i) := by
    funext ξ
    by_cases h : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R
    · rw [Set.indicator_of_mem (show ξ ∈ {ξ : PlaneInverseCube.Plane |
        ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R} from h), coreEMap_apply hs x ξ h]
    · rw [Set.indicator_of_not_mem (show ξ ∉ {ξ : PlaneInverseCube.Plane |
        ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R} from h)]
      change (if ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R then coreE q hq n r ci dci x ξ else 0) i = 0
      rw [if_neg h]
      rfl
  rw [heq]
  exact (aestronglyMeasurable_indicator_iff (core_set_measurable q hq n r)).mpr
    ((coreE_continuousOn hs x i).aestronglyMeasurable (core_set_measurable q hq n r))

/-- The coordinates of the cut-off magnetic core field are a.e.-strongly measurable on the plane. -/
theorem coreHMap_meas (hs : CoreSetup q hq n r ci dci b η) (x : Vec) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ => coreHMap hs x ξ i) volume := by
  have heq : (fun ξ => coreHMap hs x ξ i) =
      Set.indicator {ξ : PlaneInverseCube.Plane | ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R}
        (fun ξ => coreH q hq n r ci dci x ξ i) := by
    funext ξ
    by_cases h : ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R
    · rw [Set.indicator_of_mem (show ξ ∈ {ξ : PlaneInverseCube.Plane |
        ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R} from h), coreHMap_apply hs x ξ h]
    · rw [Set.indicator_of_not_mem (show ξ ∉ {ξ : PlaneInverseCube.Plane |
        ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R} from h)]
      change (if ‖ξ‖ < (SourcePairedInclusion.data q hq n r).R then coreH q hq n r ci dci x ξ else 0) i = 0
      rw [if_neg h]
      rfl
  rw [heq]
  exact (aestronglyMeasurable_indicator_iff (core_set_measurable q hq n r)).mpr
    ((coreH_continuousOn hs x i).aestronglyMeasurable (core_set_measurable q hq n r))

end Continuity

/-! ### Uniqueness of a continuous magnetic field from the weak first Maxwell equation -/

section WeakUnique

/-- The weak first Maxwell equation `curl E = I H` against Schwartz tests supported in `Ω`. -/
def WeakOn (Ω : Set Sp) (E H : Maxwell.Field) : Prop :=
  ∀ (i : Fin 3) (f : DynamicSource.Test), tsupport (f.val : Sp → ℂ) ⊆ Ω →
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair E) i f = Complex.I * MaterialMaxwell.fieldPair H i f

theorem tsupport_dcoord_subset' (f : Sp → ℂ) (i : Fin 3) :
    tsupport (fun x => Maxwell.dcoord f x i) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  exact hx (by simp only [Maxwell.dcoord, fderiv_of_not_mem_tsupport ℝ hn, ContinuousLinearMap.zero_apply])

theorem tsupport_testPartial_subset' (i : Fin 3) (f : DynamicSource.Test) :
    tsupport ((DynamicSource.testPartial i f).val : Sp → ℂ) ⊆ tsupport (f.val : Sp → ℂ) :=
  tsupport_dcoord_subset' f.val i

theorem integrable_mul_test' {Ω : Set Sp} (g : Sp → ℂ) (hg : ContinuousOn g Ω)
    (f : DynamicSource.Test) (hf : tsupport (f.val : Sp → ℂ) ⊆ Ω) :
    Integrable (fun x => g x * f.val x) := by
  have hK : IsCompact (tsupport (f.val : Sp → ℂ)) := f.property.isCompact
  have hc : ContinuousOn (fun x => g x * f.val x) (tsupport (f.val : Sp → ℂ)) :=
    (hg.mono hf).mul f.val.continuous.continuousOn
  have hi : IntegrableOn (fun x => g x * f.val x) (tsupport (f.val : Sp → ℂ)) volume :=
    hc.integrableOn_compact hK
  apply hi.integrable_of_forall_not_mem_eq_zero
  intro x hx
  simp [image_eq_zero_of_nmem_tsupport hx]

/-- Two continuous magnetic fields with the same electric field and the weak first Maxwell equation on an open
set agree on it. -/
theorem weak_unique {Ω : Set Sp} (hΩ : IsOpen Ω) (E H H2 : Maxwell.Field)
    (hH : ∀ i, ContinuousOn (fun x => H x i) Ω) (hH2 : ∀ i, ContinuousOn (fun x => H2 x i) Ω)
    (h1 : WeakOn Ω E H) (h2 : WeakOn Ω E H2) : ∀ x ∈ Ω, ∀ i, H x i = H2 x i := by
  have hcomb : ∀ i, EqOn (fun x => H x i) (fun x => H2 x i) Ω := by
    intro i
    have hg : ContinuousOn (fun x => H x i - H2 x i) Ω := (hH i).sub (hH2 i)
    have hloc : LocallyIntegrableOn (fun x => H x i - H2 x i) Ω volume :=
      hg.locallyIntegrableOn hΩ.measurableSet
    have hz := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (by
      intro φ hφ hφc hφΩ
      have hφc2 : HasCompactSupport (fun x => (φ x : ℂ)) :=
        hφc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
      let f : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz
        (fun x => (φ x : ℂ)) (Complex.ofRealCLM.contDiff.comp hφ) hφc2, hφc2⟩
      have hs : tsupport (f.val : Sp → ℂ) = tsupport φ := by
        change closure (Function.support (fun x => (φ x : ℂ))) = closure (Function.support φ)
        ext x
        simp [Function.support]
      have hfΩ : tsupport (f.val : Sp → ℂ) ⊆ Ω := hs ▸ hφΩ
      have hp : MaterialMaxwell.fieldPair H i f = MaterialMaxwell.fieldPair H2 i f := by
        have := (h1 i f hfΩ).symm.trans (h2 i f hfΩ)
        exact mul_left_cancel₀ Complex.I_ne_zero this
      have iH := integrable_mul_test' (fun x => H x i) (hH i) f hfΩ
      have iH2 := integrable_mul_test' (fun x => H2 x i) (hH2 i) f hfΩ
      have he : (∫ x, (H x i * f.val x - H2 x i * f.val x)) = 0 := by
        rw [integral_sub iH iH2]
        exact sub_eq_zero.mpr hp
      convert he using 1
      apply integral_congr_ae
      filter_upwards with x
      change (φ x : ℂ) * (H x i - H2 x i) = H x i * (φ x : ℂ) - H2 x i * (φ x : ℂ)
      ring)
    have hae : (fun x => H x i) =ᵐ[volume.restrict Ω] (fun x => H2 x i) :=
      (ae_restrict_iff' hΩ.measurableSet).mpr (hz.mono fun x hx hxΩ => sub_eq_zero.mp (hx hxΩ))
    exact Measure.eqOn_open_of_ae_eq hae hΩ (hH i) (hH2 i)
  intro x hx i
  exact hcomb i hx

end WeakUnique

/-! ### The background of the shell in the core -/

section Background
variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ)

/-- The degreewise transmissions of the stack at shell index `r`, over two. -/
def trans : ℕ → ℂ := fun l =>
  BackgroundCoreTransmission.stackTransmission l (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n)
    (RadialPhaseLimit.radius r) (RadialPhaseLimit.radius_pos r) / 2

/-- The limiting degreewise transmissions over two. -/
def transInf : ℕ → ℂ := fun l =>
  BackgroundCoreTransmission.limitingTransmission l (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n) / 2

theorem trans_tendsto (l : ℕ) : Tendsto (fun r : ℕ => trans q hq n r l) atTop (𝓝 (transInf q hq n l)) :=
  (BackgroundCoreTransmission.transmission_limit l (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n)).div_const 2

/-- Almost everywhere on the core the total field of the shell solution is the continuous background field. -/
theorem total_eq_background_ae (A : Vec) :
    ∀ᵐ y : Sp, y ∈ ball (0 : Sp) (SourcePairedInclusion.data q hq n r).R →
      MaterialField.total (SourcePairedInclusion.shell q hq n r) 1
        (MaterialField.solution (SourcePairedInclusion.shell q hq n r) 1 (SourcePairedInclusion.data q hq n r).X
          (fsLin q hq n r A)) (RestrictedTEPlaneLocal.electric A) y =
      SourcePairedPlaneIdentification.backgroundElectric (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.electric A) (fsLin q hq n r A) y := by
  have hcsX := shell_vanish_outer q hq n r
  have h := ConicalInteriorResponse.electric_ae_interior 1
    (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r)
      (MaterialField.solution (SourcePairedInclusion.shell q hq n r) 1 (SourcePairedInclusion.data q hq n r).X
        (fsLin q hq n r A)))
    (DynamicVolume.source (SourcePairedInclusion.shell q hq n r)
      (MaterialField.solution (SourcePairedInclusion.shell q hq n r) 1 (SourcePairedInclusion.data q hq n r).X
        (fsLin q hq n r A)))
    (fun j => DynamicVolume.source_integrable _ _ (SourcePairedInclusion.data q hq n r).X hcsX j)
    (StaticNewton.material_source_ae _ _) (SourcePairedInclusion.data q hq n r).R
    (SourcePairedInclusion.data q hq n r).X (fun j y hy => DynamicVolume.source_zero _ _ _ hcsX j y hy)
    (fun j y hy => shell_source_vanish_inner q hq n r _ j y hy)
  filter_upwards [h] with y hy hyb
  funext i
  have hi := congrFun (hy hyb) i
  change RestrictedTEPlaneLocal.electric A y i + FieldResponse.electric 1 _ _ y i =
    RestrictedTEPlaneLocal.electric A y i + ExteriorContinuity.electric 1 _ y i
  rw [hi]
  rfl

/-- On the open core the continuous electric background of the shell is the regular TE field of the vector
rescaled degreewise by the transmissions over two. -/
theorem backgroundElectric_eq_core (A : Vec) (y : Sp) (hy : ‖y‖ < (SourcePairedInclusion.data q hq n r).R) :
    SourcePairedPlaneIdentification.backgroundElectric (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.electric A) (fsLin q hq n r A) y =
      RestrictedTEPlaneLocal.electric (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r)) y := by
  have hae2 := BackgroundShellCoefficient.shell_te_response q hq n r A
  have hae3 : ∀ᵐ y : Sp, y ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : Sp))
  have hae : (fun y => SourcePairedPlaneIdentification.backgroundElectric (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.electric A) (fsLin q hq n r A) y)
      =ᵐ[volume.restrict (ball (0 : Sp) (SourcePairedInclusion.data q hq n r).R)]
      (fun y => RestrictedTEPlaneLocal.electric (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r)) y) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball]
    filter_upwards [total_eq_background_ae q hq n r A, hae2, hae3] with y h1 h2 h3 hyb
    rw [← h1 hyb]
    change MaterialField.total (SourcePairedInclusion.shell q hq n r) 1
      (MaterialField.solution (SourcePairedInclusion.shell q hq n r) 1 (SourcePairedInclusion.data q hq n r).X
        (RestrictedTEMaterial.datum (SourcePairedInclusion.shell q hq n r)
          (BackgroundShellCoefficient.shellSupport q hq n r) A)) (RestrictedTEPlaneLocal.electric A) y = _
    rw [h2]
    exact BackgroundShellCoefficient.shell_te_core q hq n r A y h3 (mem_ball_zero_iff.mp hyb).le
  have hf : ContinuousOn (fun y => SourcePairedPlaneIdentification.backgroundElectric
      (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
      (RestrictedTEPlaneLocal.electric A) (fsLin q hq n r A) y) (ball (0 : Sp) (SourcePairedInclusion.data q hq n r).R) := by
    refine continuousOn_pi.mpr (fun i => ?_)
    have h1 := (RestrictedTEPlaneJets.electric_continuous A i).continuousOn
      (s := ball (0 : Sp) (SourcePairedInclusion.data q hq n r).R)
    have h2 : ContinuousOn (fun y => ExteriorContinuity.electric 1 (DynamicVolume.source
        (SourcePairedInclusion.shell q hq n r) (MaterialField.solution (SourcePairedInclusion.shell q hq n r) 1
          (SourcePairedInclusion.data q hq n r).X (fsLin q hq n r A))) y i)
        (ball (0 : Sp) (SourcePairedInclusion.data q hq n r).R) := fun y hy =>
      (shell_electric_contDiffAt q hq n r _ y (mem_ball_zero_iff.mp hy) i).continuousAt.continuousWithinAt
    exact h1.add h2
  have hg : ContinuousOn (fun y => RestrictedTEPlaneLocal.electric
      (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r)) y)
      (ball (0 : Sp) (SourcePairedInclusion.data q hq n r).R) :=
    continuousOn_pi.mpr (fun i => (RestrictedTEPlaneJets.electric_continuous _ i).continuousOn)
  exact Measure.eqOn_open_of_ae_eq hae isOpen_ball hf hg (mem_ball_zero_iff.mpr hy)

/-- On the open core the continuous magnetic background of the shell is the regular TE magnetic field of the
rescaled vector (by the weak first Maxwell equation, since the electric fields agree). -/
theorem backgroundMagnetic_eq_core (A : Vec) (y : Sp) (hy : ‖y‖ < (SourcePairedInclusion.data q hq n r).R)
    (i : Fin 3) :
    SourcePairedPlaneIdentification.backgroundMagnetic (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.magnetic A) (fsLin q hq n r A) y i =
      RestrictedTEPlaneLocal.magnetic (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r)) y i := by
  set Rin := (SourcePairedInclusion.data q hq n r).R with hRin
  set u := MaterialField.solution (SourcePairedInclusion.shell q hq n r) 1
    (SourcePairedInclusion.data q hq n r).X (fsLin q hq n r A) with hu
  have hcsX := shell_vanish_outer q hq n r
  have hsol : DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
      (SourcePairedInclusion.data q hq n r).X u = fsLin q hq n r A :=
    congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (fsLin q hq n r A))
      (Ring.mul_inverse_cancel _ (SourcePairedInclusion.shell_isUnit q hq n r))
  have hglob := MaterialMaxwell.volume_solution_testMaxwell (SourcePairedInclusion.shell q hq n r) 1
    (SourcePairedInclusion.data q hq n r).X u (fsLin q hq n r A) (RestrictedTEPlaneLocal.electric A)
    (RestrictedTEPlaneLocal.magnetic A) hcsX (fun i => RestrictedTEMaterial.datum_actual _ _ A i) hsol
    (fun i => (RestrictedTEMaterial.electric_smooth A i).continuous.locallyIntegrable)
    (fun i => (RestrictedTEMaterial.magnetic_smooth A i).continuous.locallyIntegrable)
    (RestrictedTEMaterial.testMaxwell A)
  have hscaled := RestrictedTEMaterial.testMaxwell
    (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r))
  -- the electric fields agree almost everywhere on the core
  have hEae : ∀ᵐ x : Sp, x ∈ ball (0 : Sp) Rin →
      MaterialField.total (SourcePairedInclusion.shell q hq n r) 1 u (RestrictedTEPlaneLocal.electric A) x =
        RestrictedTEPlaneLocal.electric (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r)) x := by
    filter_upwards [total_eq_background_ae q hq n r A] with x hx hxb
    rw [hx hxb]
    exact backgroundElectric_eq_core q hq n r A x (mem_ball_zero_iff.mp hxb)
  have hpair : ∀ (E E' : Maxwell.Field), (∀ᵐ x : Sp, x ∈ ball (0 : Sp) Rin → E x = E' x) →
      ∀ (j : Fin 3) (g : DynamicSource.Test), tsupport (g.val : Sp → ℂ) ⊆ ball (0 : Sp) Rin →
        MaterialMaxwell.fieldPair E j g = MaterialMaxwell.fieldPair E' j g := by
    intro E E' hE j g hg
    unfold MaterialMaxwell.fieldPair
    apply integral_congr_ae
    filter_upwards [hE] with x hx
    by_cases hxb : x ∈ ball (0 : Sp) Rin
    · rw [hx hxb]
    · have : (g.val : Sp → ℂ) x = 0 := image_eq_zero_of_nmem_tsupport (fun h => hxb (hg h))
      rw [this]
      ring
  have hW1 : WeakOn (ball (0 : Sp) Rin)
      (RestrictedTEPlaneLocal.electric (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r)))
      (SourcePairedPlaneIdentification.backgroundMagnetic (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.magnetic A) (fsLin q hq n r A)) := by
    intro i f hf
    have h1 := (hglob i f).1
    simp only [Complex.ofReal_one, mul_one] at h1
    have e : MagneticResponse.curlPair (MaterialMaxwell.fieldPair
        (RestrictedTEPlaneLocal.electric (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r)))) i f =
        MagneticResponse.curlPair (MaterialMaxwell.fieldPair
          (MaterialField.total (SourcePairedInclusion.shell q hq n r) 1 u (RestrictedTEPlaneLocal.electric A))) i f := by
      unfold MagneticResponse.curlPair
      rw [hpair _ _ (hEae.mono fun x hx hxb => (hx hxb).symm) _ _
        ((tsupport_testPartial_subset' _ f).trans hf),
        hpair _ _ (hEae.mono fun x hx hxb => (hx hxb).symm) _ _
        ((tsupport_testPartial_subset' _ f).trans hf)]
    rw [e, h1]
    rfl
  have hW2 : WeakOn (ball (0 : Sp) Rin)
      (RestrictedTEPlaneLocal.electric (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r)))
      (RestrictedTEPlaneLocal.magnetic (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r))) := by
    intro j f _
    have h1 := (hscaled j f).1
    simp only [Complex.ofReal_one, mul_one] at h1
    exact h1
  have hcont1 : ∀ i, ContinuousOn (fun x => SourcePairedPlaneIdentification.backgroundMagnetic
      (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
      (RestrictedTEPlaneLocal.magnetic A) (fsLin q hq n r A) x i) (ball (0 : Sp) Rin) := by
    intro i
    have h1 := (RestrictedTEMagnetic.magnetic_continuous A i).continuousOn (s := ball (0 : Sp) Rin)
    have h2 : ContinuousOn (fun x => MagneticResponse.magnetic 1 (DynamicVolume.source
        (SourcePairedInclusion.shell q hq n r) u) x i) (ball (0 : Sp) Rin) := fun x hx =>
      (shell_magnetic_contDiffAt q hq n r u x (mem_ball_zero_iff.mp hx) i).continuousAt.continuousWithinAt
    exact h1.add h2
  have hcont2 : ∀ i, ContinuousOn (fun x => RestrictedTEPlaneLocal.magnetic
      (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r)) x i) (ball (0 : Sp) Rin) :=
    fun i => (RestrictedTEMagnetic.magnetic_continuous _ i).continuousOn
  exact weak_unique isOpen_ball _ _ _ hcont1 hcont2 hW1 hW2 y (mem_ball_zero_iff.mpr hy) i

end Background

/-! ### Uniform convergence of the background, the effective datum and the total fields -/

section Convergence

theorem bounded_on_ball (f : Sp → Maxwell.Vector) (hf : ∀ i, Continuous (fun y => f y i)) (ρ0 : ℝ) :
    ∃ B : ℝ, ∀ y : Sp, ‖y‖ ≤ ρ0 → ∀ i, ‖f y i‖ ≤ B := by
  have hb := fun i => (isCompact_closedBall (0 : Sp) ρ0).exists_bound_of_continuousOn (hf i).continuousOn
  choose C hC using hb
  refine ⟨∑ i, |C i|, fun y hy i => ?_⟩
  have h1 : ‖f y i‖ ≤ C i := hC i y (by simpa using hy)
  exact h1.trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))

/-- A linear function of a finite coefficient vector rescaled degreewise by convergent factors converges
uniformly on balls, when the images of the basis vectors are continuous. -/
theorem scaled_uniform (L : Vec →ₗ[ℂ] Maxwell.Field)
    (hL : ∀ (a : SymmetricHarmonicJets.Index) (i : Fin 3), Continuous (fun y => L (Finsupp.single a 1) y i))
    (A : Vec) (t : ℕ → ℕ → ℂ) (t0 : ℕ → ℂ)
    (ht : ∀ l, Tendsto (fun r => t r l) atTop (𝓝 (t0 l))) (ρ0 ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ y : Sp, ‖y‖ ≤ ρ0 → ∀ i,
      ‖L (BackgroundCoreTransmission.scaledCoeff A (t r)) y i -
        L (BackgroundCoreTransmission.scaledCoeff A t0) y i‖ ≤ ε := by
  classical
  choose B hB using fun a : SymmetricHarmonicJets.Index =>
    bounded_on_ball (L (Finsupp.single a 1)) (hL a) ρ0
  set M : ℝ := ∑ a ∈ A.support, |B a| with hMdef
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set ε' : ℝ := ε / (M + 1) with hε'def
  have hε' : 0 < ε' := by positivity
  have hev : ∀ᶠ r : ℕ in atTop, ∀ a ∈ A.support, ‖A a * (t r a.val.1 - t0 a.val.1)‖ ≤ ε' := by
    rw [Filter.eventually_all_finset]
    intro a _
    have h0 : Tendsto (fun r => A a * (t r a.val.1 - t0 a.val.1)) atTop (𝓝 0) := by
      have := ((ht a.val.1).sub_const (t0 a.val.1)).const_mul (A a)
      simpa using this
    filter_upwards [Metric.tendsto_nhds.mp h0 ε' hε'] with r hr
    simpa [dist_zero_right] using hr.le
  filter_upwards [hev] with r hr y hy i
  have e : ∀ s : ℕ → ℂ, L (BackgroundCoreTransmission.scaledCoeff A s) y i =
      ∑ a ∈ A.support, (A a * s a.val.1) * L (Finsupp.single a 1) y i := by
    intro s
    rw [BackgroundCoreTransmission.map_scaledCoeff L A s]
    simp [Finset.sum_apply]
  rw [e (t r), e t0, ← Finset.sum_sub_distrib]
  calc ‖∑ a ∈ A.support, ((A a * t r a.val.1) * L (Finsupp.single a 1) y i -
        (A a * t0 a.val.1) * L (Finsupp.single a 1) y i)‖
      ≤ ∑ a ∈ A.support, ‖(A a * t r a.val.1) * L (Finsupp.single a 1) y i -
        (A a * t0 a.val.1) * L (Finsupp.single a 1) y i‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ A.support, ε' * |B a| := Finset.sum_le_sum fun a ha => by
        have hh : (A a * t r a.val.1) * L (Finsupp.single a 1) y i -
            (A a * t0 a.val.1) * L (Finsupp.single a 1) y i =
            (A a * (t r a.val.1 - t0 a.val.1)) * L (Finsupp.single a 1) y i := by ring
        rw [hh, norm_mul]
        exact mul_le_mul (hr a ha) ((hB a y hy i).trans (le_abs_self _)) (norm_nonneg _) hε'.le
    _ = ε' * M := by rw [← Finset.mul_sum]
    _ ≤ ε := by
        rw [hε'def, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

variable (q : ℝ) (hq : 1 ≤ q) (n : ℕ)

/-- Uniform convergence on balls of the electric background of the shell to the regular TE field of the vector
rescaled by the limiting transmissions. -/
theorem backgroundElectric_conv (A : Vec) (ρ0 ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ y : Sp, ‖y‖ ≤ ρ0 → ∀ i,
      ‖SourcePairedPlaneIdentification.backgroundElectric (SourcePairedInclusion.shell q hq n r)
          (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.electric A) (fsLin q hq n r A) y i -
        RestrictedTEPlaneLocal.electric (BackgroundCoreTransmission.scaledCoeff A (transInf q hq n)) y i‖ ≤ ε := by
  have h := scaled_uniform RestrictedTEFieldLinear.electricMap
    (fun a i => by
      rw [show (fun y => RestrictedTEFieldLinear.electricMap (Finsupp.single a 1) y i) =
        fun y => RestrictedTEPlaneLocal.electric (Finsupp.single a 1) y i from by
          funext y; rw [RestrictedTEFieldLinear.electricMap_apply]]
      exact RestrictedTEPlaneJets.electric_continuous _ i)
    A (fun r => trans q hq n r) (transInf q hq n) (trans_tendsto q hq n) ρ0 ε hε
  filter_upwards [h, RadialPhaseLimit.radius_tendsto.eventually (eventually_gt_atTop ρ0)] with r h1 hρ y hy i
  rw [backgroundElectric_eq_core q hq n r A y (lt_of_le_of_lt hy hρ)]
  have := h1 y hy i
  rwa [RestrictedTEFieldLinear.electricMap_apply, RestrictedTEFieldLinear.electricMap_apply] at this

/-- Uniform convergence on balls of the magnetic background of the shell to the regular TE magnetic field of the
vector rescaled by the limiting transmissions. -/
theorem backgroundMagnetic_conv (A : Vec) (ρ0 ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ y : Sp, ‖y‖ ≤ ρ0 → ∀ i,
      ‖SourcePairedPlaneIdentification.backgroundMagnetic (SourcePairedInclusion.shell q hq n r)
          (SourcePairedInclusion.data q hq n r).X (RestrictedTEPlaneLocal.magnetic A) (fsLin q hq n r A) y i -
        RestrictedTEPlaneLocal.magnetic (BackgroundCoreTransmission.scaledCoeff A (transInf q hq n)) y i‖ ≤ ε := by
  have h := scaled_uniform RestrictedTEFieldLinear.magneticMap
    (fun a i => by
      rw [show (fun y => RestrictedTEFieldLinear.magneticMap (Finsupp.single a 1) y i) =
        fun y => RestrictedTEPlaneLocal.magnetic (Finsupp.single a 1) y i from by
          funext y; rw [RestrictedTEFieldLinear.magneticMap_apply]]
      exact RestrictedTEMagnetic.magnetic_continuous _ i)
    A (fun r => trans q hq n r) (transInf q hq n) (trans_tendsto q hq n) ρ0 ε hε
  filter_upwards [h, RadialPhaseLimit.radius_tendsto.eventually (eventually_gt_atTop ρ0)] with r h1 hρ y hy i
  rw [backgroundMagnetic_eq_core q hq n r A y (lt_of_le_of_lt hy hρ) i]
  have := h1 y hy i
  rwa [RestrictedTEFieldLinear.magneticMap_apply, RestrictedTEFieldLinear.magneticMap_apply] at this

variable (ci : Coefficient) (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ)

/-- The effective datum of the shell and inclusion data is the datum of the rescaled vector. -/
theorem effectiveDatum_eq_datum (r : ℕ) (hb : b < (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ y : Sp, y ∉ closedBall (0 : Sp) b → ci.value (VectorFourier.coordinateMap y) = 0) (A : Vec) :
    SourcePairedPlaneIdentification.effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (fsLin q hq n r A) (fiLin ci dci A) =
      RestrictedTEMaterial.datum ci dci (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r)) := by
  apply SourcePairedPlaneIdentification.IsDatum.unique
  · exact SourcePairedPlaneIdentification.effectiveDatum_isDatum (SourcePairedInclusion.shell q hq n r) ci b
      (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X
      (SourcePairedInclusion.data q hq n r).X hb (SourcePairedInclusion.radii_ordered q hq n r) le_rfl
      (shell_hcs' q hq n r) hci (RestrictedTEPlaneLocal.electric A) (fsLin q hq n r A) (fiLin ci dci A)
      (fi_isDatum ci dci A)
  · intro i
    filter_upwards [RestrictedTEMaterial.datum_actual ci dci
      (BackgroundCoreTransmission.scaledCoeff A (trans q hq n r)) i] with y hy
    rw [hy]
    by_cases hyb : y ∈ closedBall (0 : Sp) b
    · have hy' : ‖y‖ < (SourcePairedInclusion.data q hq n r).R :=
        lt_of_le_of_lt (mem_closedBall_zero_iff.mp hyb) hb
      rw [backgroundElectric_eq_core q hq n r A y hy']
    · rw [hci y hyb]
      simp

/-- The effective datum converges to the datum of the vector rescaled by the limiting transmissions. -/
theorem effectiveDatum_conv (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b) (A : Vec) :
    Tendsto (fun r : ℕ => SourcePairedPlaneIdentification.effectiveDatum (SourcePairedInclusion.shell q hq n r)
        ci (SourcePairedInclusion.data q hq n r).X (fsLin q hq n r A) (fiLin ci dci A)) atTop
      (𝓝 (RestrictedTEMaterial.datum ci dci (BackgroundCoreTransmission.scaledCoeff A (transInf q hq n)))) := by
  have h := BackgroundCoreTransmission.datum_scaledCoeff_tendsto ci dci A (fun r => trans q hq n r)
    (transInf q hq n) (trans_tendsto q hq n)
  refine h.congr' ?_
  filter_upwards [SourcePairedReduction.eventually_inner_radius q hq n b] with r hbR
  exact (effectiveDatum_eq_datum q hq n ci dci b r hbR (SourcePairedReduction.inclusion_vanish ci dci b hcar) A).symm

/-- The limiting datum. -/
def gLim (A : Vec) : VectorL2 :=
  RestrictedTEMaterial.datum ci dci (BackgroundCoreTransmission.scaledCoeff A (transInf q hq n))

/-- The limiting electric field. -/
def EinfF (A : Vec) : Maxwell.Field :=
  RestrictedTEPlaneLocal.electric (BackgroundCoreTransmission.scaledCoeff A (transInf q hq n))

/-- The limiting magnetic field. -/
def HinfF (A : Vec) : Maxwell.Field :=
  RestrictedTEPlaneLocal.magnetic (BackgroundCoreTransmission.scaledCoeff A (transInf q hq n))

theorem gLim_fixed (hsym : HalfTurnVectorAction.Symmetric ci) (A : Vec) :
    HalfTurnVectorAction.U (gLim q hq n ci dci A) = gLim q hq n ci dci A :=
  RestrictedTEEvenDatum.datum_fixed ci hsym dci _

/-- The raw limit of the assembled electric field: the total electric field of the parity device with the datum
of the rescaled vector. -/
def rawLimitE (A : Vec) (ξ : PlaneInverseCube.Plane) : Maxwell.Vector :=
  ParityPlaneFields.totalElectric 1 (q ^ n)
    (DynamicVolume.source ci (ParityMaterialField.solution dci 1 (q ^ n) (gLim q hq n ci dci A)))
    (EinfF q hq n A) (MaxwellPlaneTail.planePoint ξ)

/-- The raw limit of the assembled magnetic field. -/
def rawLimitH (A : Vec) (ξ : PlaneInverseCube.Plane) : Maxwell.Vector :=
  ParityPlaneFields.totalMagnetic 1 (q ^ n)
    (DynamicVolume.source ci (ParityMaterialField.solution dci 1 (q ^ n) (gLim q hq n ci dci A)))
    (HinfF q hq n A) (MaxwellPlaneTail.planePoint ξ)

variable (hb0 : 0 < b) (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b) (hsym : HalfTurnVectorAction.Symmetric ci)
  (η : ℝ) (hη : 0 < η) (hgap : ∀ y ∈ dci.carrier, η ≤ |y 2|)
  (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci dci b hb0))
  (hu : IsUnit (ParityMaterialField.block dci 1 (q ^ n)))
include hb0 hcar hsym hη hgap hL hu

/-- Uniform convergence on every disk of the assembled electric plane field of the combined device to the raw
limit (the total electric field of the parity device). -/
theorem coreE_conv_raw (A : Vec) (ρ0 : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i,
      ‖coreE q hq n r ci dci A ξ i - rawLimitE q hq n ci dci A ξ i‖ ≤ ε := by
  have h := SourcePairedPlaneIdentification.combined_total_electric_tendsto_uniform_canonical q hq n ci dci b hb0
    hcar hsym hL hu (RestrictedTEPlaneLocal.electric A) (fun r => fsLin q hq n r A) (fiLin ci dci A)
    (fun r => fs_isDatum q hq n r A) (fi_isDatum ci dci A) (gLim q hq n ci dci A)
    (gLim_fixed q hq n ci dci hsym A) (effectiveDatum_conv q hq n ci dci b hcar A) ρ0 η hη (EinfF q hq n A)
    (fun ε hε => (backgroundElectric_conv q hq n A ρ0 ε hε).mono fun r hr y hy _ i => hr y hy i) ε hε
  filter_upwards [h] with r hr ξ hξ i
  exact hr (MaxwellPlaneTail.planePoint ξ) (by rw [MaxwellPlaneTail.planePoint_norm]; exact hξ)
    (fun y hy => PlaneSourceKernel.gap_distance η ξ y (hgap y hy)) i

/-- The magnetic analogue. -/
theorem coreH_conv_raw (A : Vec) (ρ0 : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i,
      ‖coreH q hq n r ci dci A ξ i - rawLimitH q hq n ci dci A ξ i‖ ≤ ε := by
  have h := SourcePairedPlaneIdentification.combined_total_magnetic_tendsto_uniform_canonical q hq n ci dci b hb0
    hcar hsym hL hu (RestrictedTEPlaneLocal.electric A) (fun r => fsLin q hq n r A) (fiLin ci dci A)
    (fun r => fs_isDatum q hq n r A) (fi_isDatum ci dci A) (gLim q hq n ci dci A)
    (gLim_fixed q hq n ci dci hsym A) (effectiveDatum_conv q hq n ci dci b hcar A) ρ0 η hη
    (RestrictedTEPlaneLocal.magnetic A) (HinfF q hq n A)
    (fun ε hε => (backgroundMagnetic_conv q hq n A ρ0 ε hε).mono fun r hr y hy _ i => hr y hy i) ε hε
  filter_upwards [h] with r hr ξ hξ i
  exact hr (MaxwellPlaneTail.planePoint ξ) (by rw [MaxwellPlaneTail.planePoint_norm]; exact hξ)
    (fun y hy => PlaneSourceKernel.gap_distance η ξ y (hgap y hy)) i

end Convergence

/-! ### The doubled device -/

section Device
open OQ14.RestrictedTEPartnerSmallness OQ14.RestrictedTEPartnerBalls

/-- The hypotheses on the doubled device: positions `p a l` of the original balls (radius `ρ a`, contrast `χ`)
inside the ball of radius `R`, at height at least `(γ + ρ) a` from the plane. -/
structure Device {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ → ι → Sp) (ρ χ R γ : ℝ) : Prop where
  hρ : 0 < ρ
  hχ : 0 ≤ χ
  hγ : 0 < γ
  hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R
  hh : ∀ a, 0 < a → a ≤ 1 → ∀ l, (γ + ρ) * a ≤ |p a l 2|

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ → ι → Sp} {ρ χ R γ : ℝ}

/-- The carrier of the doubled device at scale `a_n` stays at height `γ a_n` from the plane. -/
theorem device_carrier_gap (hd : Device p ρ χ R γ) {q : ℝ} (hq : 1 < q) (n : ℕ) :
    ∀ y ∈ (RestrictedTEPartnerSmallness.deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n).carrier,
      γ * scale q n ≤ |y 2| := by
  intro y hy
  have ha := scale_pos hq n
  have ha1 := scale_le_one hq.le n
  change y ∈ ⋃ j, Metric.ball (partnerCentre (p (scale q n)) j) (partnerRadius (fun _ : ι => ρ * scale q n) j) at hy
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  obtain ⟨l, hl⟩ := partner_height (p (scale q n)) j
  have h1 : ‖y - partnerCentre (p (scale q n)) j‖ < ρ * scale q n := by
    have := mem_ball_iff_norm.mp hj
    rwa [partner_radius_const] at this
  have h2 := PiLp.norm_apply_le (y - partnerCentre (p (scale q n)) j) 2
  rw [Real.norm_eq_abs] at h2
  have h3 : (y - partnerCentre (p (scale q n)) j) 2 = y 2 - partnerCentre (p (scale q n)) j 2 := rfl
  rw [h3] at h2
  have h4 := hd.hh (scale q n) ha ha1 l
  rw [← hl] at h4
  have h5 : |partnerCentre (p (scale q n)) j 2| ≤ |y 2| + |y 2 - partnerCentre (p (scale q n)) j 2| := by
    calc |partnerCentre (p (scale q n)) j 2|
        = |y 2 - (y 2 - partnerCentre (p (scale q n)) j 2)| := by ring_nf
      _ ≤ |y 2| + |y 2 - partnerCentre (p (scale q n)) j 2| := abs_sub _ _
  nlinarith

/-- The core setting of the doubled device at gain index `n`, once the inclusion radius `b` lies inside the inner
radius of the shell. -/
theorem device_setup (hd : Device p ρ χ R γ) {q : ℝ} (hq : 1 < q) {b : ℝ} (hRb : R ≤ b) (n r : ℕ)
    (hbr : b < (SourcePairedInclusion.data q hq.le n r).R) :
    CoreSetup q hq.le n r (deviceCoeff p ρ χ hd.hχ q n)
      (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) b (γ * scale q n) where
  hb := hbr
  hci := SourcePairedReduction.inclusion_vanish _ _ b
    (RestrictedTEActualCounting.device_carrier_le p ρ χ R b hd.hρ hd.hχ hRb hd.hi q hq n)
  hη := mul_pos hd.hγ (scale_pos hq n)
  hgap := device_carrier_gap hd hq n

variable (hd : Device p ρ χ R γ) {q : ℝ} (hq : 1 < q) {b : ℝ} (hRb : R ≤ b)

/-- The electric core field of the doubled device at gain index `n`, as a linear field family (cut off outside the
core; zero while the inclusion is not yet inside the inner shell radius). -/
def deviceFieldE (n r : ℕ) : RestrictedTEActualFields.FieldMap :=
  if hbr : b < (SourcePairedInclusion.data q hq.le n r).R then coreEMap (device_setup hd hq hRb n r hbr) else 0

/-- The magnetic core field of the doubled device at gain index `n`. -/
def deviceFieldH (n r : ℕ) : RestrictedTEActualFields.FieldMap :=
  if hbr : b < (SourcePairedInclusion.data q hq.le n r).R then coreHMap (device_setup hd hq hRb n r hbr) else 0

theorem deviceFieldE_apply (n r : ℕ) (hbr : b < (SourcePairedInclusion.data q hq.le n r).R) (x : Vec)
    (ξ : PlaneInverseCube.Plane) (hξ : ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R) :
    deviceFieldE hd hq hRb n r x ξ = coreE q hq.le n r (deviceCoeff p ρ χ hd.hχ q n)
      (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) x ξ := by
  unfold deviceFieldE
  rw [dif_pos hbr]
  exact coreEMap_apply _ x ξ hξ

theorem deviceFieldH_apply (n r : ℕ) (hbr : b < (SourcePairedInclusion.data q hq.le n r).R) (x : Vec)
    (ξ : PlaneInverseCube.Plane) (hξ : ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R) :
    deviceFieldH hd hq hRb n r x ξ = coreH q hq.le n r (deviceCoeff p ρ χ hd.hχ q n)
      (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) x ξ := by
  unfold deviceFieldH
  rw [dif_pos hbr]
  exact coreHMap_apply _ x ξ hξ

/-- The coordinates of the device fields are a.e.-strongly measurable on the plane. -/
theorem deviceField_meas (n r : ℕ) (x : Vec) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ => deviceFieldE hd hq hRb n r x ξ i) volume ∧
      AEStronglyMeasurable (fun ξ => deviceFieldH hd hq hRb n r x ξ i) volume := by
  by_cases hbr : b < (SourcePairedInclusion.data q hq.le n r).R
  · constructor
    · unfold deviceFieldE
      rw [dif_pos hbr]
      exact coreEMap_meas _ x i
    · unfold deviceFieldH
      rw [dif_pos hbr]
      exact coreHMap_meas _ x i
  · constructor
    · unfold deviceFieldE
      rw [dif_neg hbr]
      exact aestronglyMeasurable_const
    · unfold deviceFieldH
      rw [dif_neg hbr]
      exact aestronglyMeasurable_const

/-- Eventually in the gain index, the assembled plane fields of the doubled device converge uniformly on every
disk, as the shell index tends to infinity, to the raw limit (the total fields of the parity device with the
datum of the vector rescaled by the limiting transmissions). -/
theorem device_conv_raw (hb0 : 0 < b) :
    ∀ᶠ n : ℕ in atTop, ∀ (A : Vec) (ρ0 : ℝ), 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop,
      ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i,
        ‖deviceFieldE hd hq hRb n r A ξ i -
          rawLimitE q hq.le n (deviceCoeff p ρ χ hd.hχ q n)
            (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A ξ i‖ ≤ ε ∧
        ‖deviceFieldH hd hq hRb n r A ξ i -
          rawLimitH q hq.le n (deviceCoeff p ρ χ hd.hχ q n)
            (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A ξ i‖ ≤ ε := by
  filter_upwards [RestrictedTEPartnerSmallness.partner_limitEffective_isUnit p ρ χ R b hd.hρ hd.hχ hb0 hRb
      hd.hi q hq,
    RestrictedTEPartnerTransfer.partner_parity_small p ρ χ R hd.hρ hd.hχ hd.hi q hq] with n hL hpar
  have hu : IsUnit (ParityMaterialField.block (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) 1 (q ^ n)) :=
    ParityReactionVolume.explicitBlock_isUnit _ 1 (q ^ n) (hpar.trans (by norm_num))
  intro A ρ0 hρ0 ε hε
  have hcar := RestrictedTEActualCounting.device_carrier_le p ρ χ R b hd.hρ hd.hχ hRb hd.hi q hq n
  have hsym := RestrictedTEPartnerBalls.partner_symmetric (p (scale q n)) (fun _ : ι => ρ * scale q n) χ hd.hχ
  have hη : 0 < γ * scale q n := mul_pos hd.hγ (scale_pos hq n)
  have hE := coreE_conv_raw q hq.le n (deviceCoeff p ρ χ hd.hχ q n)
    (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) b hb0 hcar hsym (γ * scale q n) hη
    (device_carrier_gap hd hq n) hL hu A ρ0 ε hε
  have hH := coreH_conv_raw q hq.le n (deviceCoeff p ρ χ hd.hχ q n)
    (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) b hb0 hcar hsym (γ * scale q n) hη
    (device_carrier_gap hd hq n) hL hu A ρ0 ε hε
  filter_upwards [hE, hH, SourcePairedReduction.eventually_inner_radius q hq.le n b,
    RadialPhaseLimit.radius_tendsto.eventually (eventually_gt_atTop ρ0)] with r h1 h2 hbr hρ ξ hξ i
  have hξR : ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R := lt_of_le_of_lt hξ hρ
  rw [deviceFieldE_apply hd hq hRb n r hbr A ξ hξR, deviceFieldH_apply hd hq hRb n r hbr A ξ hξR]
  exact ⟨h1 ξ hξ i, h2 ξ hξ i⟩

end Device

/-! ### The raw limit is the parity device field at the twisted input -/

section Twist
open OQ14.RestrictedTEPartnerSmallness OQ14.RestrictedTEPartnerBalls

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The parity total electric field of the doubled device with original positions `p a l`, at scale `a`
(`RestrictedTETotalLinear.totalE` with gain constant `1` and the doubled centres). -/
def parityEg (p : ℝ → ι → Sp) (ρ χ R : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (a : ℝ) (x : Vec) (ξ : PlaneInverseCube.Plane) :
    Maxwell.Vector :=
  RestrictedTETotalLinear.totalE (fun a => partnerCentre (p a)) ρ χ R 1 hρ hχ
    (RestrictedTEConcreteDoubled.partner_hi_aux p ρ R hi) a x ξ

/-- The parity total magnetic field of the doubled device with original positions `p a l`. -/
def parityHg (p : ℝ → ι → Sp) (ρ χ R : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖ + ρ ≤ R) (a : ℝ) (x : Vec) (ξ : PlaneInverseCube.Plane) :
    Maxwell.Vector :=
  RestrictedTETotalLinear.totalH (fun a => partnerCentre (p a)) ρ χ R 1 hρ hχ
    (RestrictedTEConcreteDoubled.partner_hi_aux p ρ R hi) a x ξ

/-- The concrete parity electric field of `RestrictedTEActualFields` is `parityEg` for the concrete positions. -/
theorem parityE_eq_parityEg (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (a : ℝ) (x : Vec)
    (ξ : PlaneInverseCube.Plane) :
    RestrictedTEActualFields.parityE r0 y ρ χ h R hρ hχ hi a x ξ =
      parityEg (fun a l => OQ14.RestrictedTEDipoleProfile.abovePoint
        (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)) ρ χ R hρ hχ.le hi a x ξ := rfl

theorem parityH_eq_parityHg (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (a : ℝ) (x : Vec)
    (ξ : PlaneInverseCube.Plane) :
    RestrictedTEActualFields.parityH r0 y ρ χ h R hρ hχ hi a x ξ =
      parityHg (fun a l => OQ14.RestrictedTEDipoleProfile.abovePoint
        (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)) ρ χ R hρ hχ.le hi a x ξ := rfl

/-- The coefficient of the doubled device is the finite-ball coefficient of the doubled centres with constant
radii. -/
theorem device_coeff_eq (p : ℝ → ι → Sp) (ρ χ : ℝ) (hχ : 0 ≤ χ) (q : ℝ) (n : ℕ) :
    deviceCoeff p ρ χ hχ q n =
      FiniteSphereStatic.coefficient (partnerCentre (p (scale q n))) (fun _ : ι ⊕ ι => ρ * scale q n) χ hχ := by
  unfold deviceCoeff partnerCoefficient
  have hr : partnerRadius (fun _ : ι => ρ * scale q n) = fun _ : ι ⊕ ι => ρ * scale q n :=
    funext fun j => partner_radius_const ρ (scale q n) j
  rw [hr]

/-- The parity solution depends on the support data of equal coefficients only through the radius and the
carrier. -/
theorem parity_solution_congr {c₁ c₂ : Coefficient} (h : c₁ = c₂) (d₁ : BoundedMaterialKernel.SupportData c₁)
    (d₂ : BoundedMaterialKernel.SupportData c₂) (hr : d₁.radius = d₂.radius) (hc : d₁.carrier = d₂.carrier)
    (k B : ℝ) (f : VectorL2) :
    ParityMaterialField.solution d₁ k B f = ParityMaterialField.solution d₂ k B f := by
  subst h
  have hd : d₁ = d₂ := by
    obtain ⟨r1, c1, m1, f1, b1, z1⟩ := d₁
    obtain ⟨r2, c2, m2, f2, b2, z2⟩ := d₂
    simp only at hr hc
    subst hr
    subst hc
    rfl
  rw [hd]

theorem scale_inv_cast (q : ℝ) (n : ℕ) : ((scale q n : ℝ) : ℂ)⁻¹ = ((q ^ n : ℝ) : ℂ) := by
  unfold scale
  push_cast
  rw [inv_inv]

variable {p : ℝ → ι → Sp} {ρ χ R γ : ℝ}

/-- The parity source of the doubled device at scale `a_n` and input `w` is the source of the device inclusion
with the parity solution of the datum of `q^n w`. -/
theorem parity_source_eq (hd : Device p ρ χ R γ) {q : ℝ} (hq : 1 < q) (n : ℕ) (A w : Vec)
    (hAw : BackgroundCoreTransmission.scaledCoeff A (transInf q hq.le n) = ((q ^ n : ℝ) : ℂ) • w) :
    RestrictedTESourceMass.source (fun a => partnerCentre (p a)) ρ χ R 1 hd.hρ hd.hχ
        (RestrictedTEConcreteDoubled.partner_hi_aux p ρ R hd.hi) w (scale q n) =
      DynamicVolume.source (deviceCoeff p ρ χ hd.hχ q n)
        (ParityMaterialField.solution (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) 1 (q ^ n)
          (gLim q hq.le n (deviceCoeff p ρ χ hd.hχ q n) (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A)) := by
  have ha := scale_pos hq n
  have ha1 := scale_le_one hq.le n
  have hc := device_coeff_eq p ρ χ hd.hχ q n
  rw [RestrictedTESourceMass.source_actual _ ρ χ R 1 hd.hρ hd.hχ _ w (scale q n) ha ha1]
  have hval : (deviceCoeff p ρ χ hd.hχ q n).value =
      (FiniteSphereStatic.coefficient (partnerCentre (p (scale q n))) (fun _ : ι ⊕ ι => ρ * scale q n) χ
        hd.hχ).value := congrArg (fun c => c.value) hc
  have hdata : ParityMaterialField.solution
      (FiniteSphereActualSources.data (fun a => partnerCentre (p a)) ρ χ R hd.hρ hd.hχ
        (RestrictedTEConcreteDoubled.partner_hi_aux p ρ R hd.hi) (scale q n) ha ha1) 1 (1 / scale q n)
      (RestrictedTEAsymptotics.forcing (fun a => partnerCentre (p a)) ρ χ R hd.hρ hd.hχ
        (RestrictedTEConcreteDoubled.partner_hi_aux p ρ R hd.hi) w (scale q n)) =
      ParityMaterialField.solution (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) 1 (q ^ n)
        (gLim q hq.le n (deviceCoeff p ρ χ hd.hχ q n) (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A) := by
    rw [show (1 : ℝ) / scale q n = q ^ n from scale_gain n]
    have hf : RestrictedTEAsymptotics.forcing (fun a => partnerCentre (p a)) ρ χ R hd.hρ hd.hχ
        (RestrictedTEConcreteDoubled.partner_hi_aux p ρ R hd.hi) w (scale q n) =
        gLim q hq.le n (deviceCoeff p ρ χ hd.hχ q n) (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A := by
      unfold RestrictedTEAsymptotics.forcing gLim
      rw [dif_pos ⟨ha, ha1⟩, hAw, scale_inv_cast]
      exact BackgroundShellCoefficient.datum_congr_value hval.symm _ _ _
    rw [hf]
    exact parity_solution_congr hc.symm _ _ rfl (by
      change (⋃ j, Metric.ball (partnerCentre (p (scale q n)) j) (ρ * scale q n)) =
        ⋃ j, Metric.ball (partnerCentre (p (scale q n)) j) (partnerRadius (fun _ : ι => ρ * scale q n) j)
      refine Set.iUnion_congr (fun j => ?_)
      rw [partner_radius_const]) _ _ _
  rw [hdata]
  exact (BackgroundShellCoefficient.source_congr_value hval _).symm

/-- **Twist identification (electric).**  If the vector rescaled degreewise by the limiting transmissions is `q^n`
times `w`, the raw limit of the assembled electric field is the parity total electric field of the doubled device
at scale `a_n = (q^n)⁻¹` and input `w`. -/
theorem rawLimitE_eq_parity (hd : Device p ρ χ R γ) {q : ℝ} (hq : 1 < q) (n : ℕ) (A w : Vec)
    (hAw : BackgroundCoreTransmission.scaledCoeff A (transInf q hq.le n) = ((q ^ n : ℝ) : ℂ) • w)
    (ξ : PlaneInverseCube.Plane) :
    rawLimitE q hq.le n (deviceCoeff p ρ χ hd.hχ q n) (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A ξ =
      parityEg p ρ χ R hd.hρ hd.hχ hd.hi (scale q n) w ξ := by
  unfold rawLimitE parityEg RestrictedTETotalLinear.totalE
  rw [parity_source_eq hd hq n A w hAw, show (1 : ℝ) / scale q n = q ^ n from scale_gain n]
  have hE : EinfF q hq.le n A = RestrictedTEPlaneLocal.electric (((scale q n : ℝ) : ℂ)⁻¹ • w) := by
    unfold EinfF
    rw [hAw, scale_inv_cast]
  rw [hE]

/-- **Twist identification (magnetic).** -/
theorem rawLimitH_eq_parity (hd : Device p ρ χ R γ) {q : ℝ} (hq : 1 < q) (n : ℕ) (A w : Vec)
    (hAw : BackgroundCoreTransmission.scaledCoeff A (transInf q hq.le n) = ((q ^ n : ℝ) : ℂ) • w)
    (ξ : PlaneInverseCube.Plane) :
    rawLimitH q hq.le n (deviceCoeff p ρ χ hd.hχ q n) (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A ξ =
      parityHg p ρ χ R hd.hρ hd.hχ hd.hi (scale q n) w ξ := by
  unfold rawLimitH parityHg RestrictedTETotalLinear.totalH
  rw [parity_source_eq hd hq n A w hAw, show (1 : ℝ) / scale q n = q ^ n from scale_gain n]
  have hH : HinfF q hq.le n A = RestrictedTEPlaneLocal.magnetic (((scale q n : ℝ) : ℂ)⁻¹ • w) := by
    unfold HinfF
    rw [hAw, scale_inv_cast]
  rw [hH]

end Twist

/-! ### Convergence to the twisted parity fields -/

section TwistConv
open OQ14.RestrictedTEPartnerSmallness OQ14.RestrictedTEPartnerBalls

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ → ι → Sp} {ρ χ R γ : ℝ}
  (hd : Device p ρ χ R γ) {q : ℝ} (hq : 1 < q) {b : ℝ} (hRb : R ≤ b)

/-- **Convergence of the core fields to the twisted parity fields.**  If, for all large gain indices, the input
rescaled degreewise by the limiting transmissions is `q^n` times the twisted input, the core fields of the
doubled device converge, uniformly on every disk, to the parity total fields at scale `(q^n)⁻¹` and the twisted
input. -/
theorem device_conv_twisted (hb0 : 0 < b) (twist : Vec → Vec)
    (htw : ∀ᶠ n : ℕ in atTop, ∀ x : Vec,
      BackgroundCoreTransmission.scaledCoeff x (transInf q hq.le n) = ((q ^ n : ℝ) : ℂ) • twist x) :
    ∀ᶠ n : ℕ in atTop, ∀ (x : Vec) (ρ0 : ℝ), 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop,
      ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i,
        ‖deviceFieldE hd hq hRb n r x ξ i -
          parityEg p ρ χ R hd.hρ hd.hχ hd.hi (scale q n) (twist x) ξ i‖ ≤ ε ∧
        ‖deviceFieldH hd hq hRb n r x ξ i -
          parityHg p ρ χ R hd.hρ hd.hχ hd.hi (scale q n) (twist x) ξ i‖ ≤ ε := by
  filter_upwards [device_conv_raw hd hq hRb hb0, htw] with n h htw'
  intro x ρ0 hρ0 ε hε
  filter_upwards [h x ρ0 hρ0 ε hε] with r hr ξ hξ i
  obtain ⟨h1, h2⟩ := hr ξ hξ i
  rw [rawLimitE_eq_parity hd hq n x (twist x) (htw' x) ξ] at h1
  rw [rawLimitH_eq_parity hd hq n x (twist x) (htw' x) ξ] at h2
  exact ⟨h1, h2⟩

end TwistConv

/-! ### The twisted field estimates -/

section Twisted
open scoped ComplexInnerProductSpace

/-- A twist of the input space is unitary for the physical input inner product. -/
def TwistUnitary (twist : Vec ≃ₗ[ℂ] Vec) : Prop :=
  ∀ x y : Vec, ⟪RestrictedTEInput.input (twist x), RestrictedTEInput.input (twist y)⟫ =
    ⟪RestrictedTEInput.input x, RestrictedTEInput.input y⟫

variable {twist : Vec ≃ₗ[ℂ] Vec}

theorem TwistUnitary.power (hu : TwistUnitary twist) (x : Vec) :
    RestrictedTEIncoming.physicalPower (twist x) = RestrictedTEIncoming.physicalPower x := by
  rw [← RestrictedTEInput.input_norm_sq, ← RestrictedTEInput.input_norm_sq]
  have h := hu x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

theorem TwistUnitary.power_symm (hu : TwistUnitary twist) (x : Vec) :
    RestrictedTEIncoming.physicalPower (twist.symm x) = RestrictedTEIncoming.physicalPower x := by
  have := hu.power (twist.symm x)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem TwistUnitary.inner_symm (hu : TwistUnitary twist) (x y : Vec) :
    ⟪RestrictedTEInput.input (twist.symm x), RestrictedTEInput.input (twist.symm y)⟫ =
      ⟪RestrictedTEInput.input x, RestrictedTEInput.input y⟫ := by
  have := hu (twist.symm x) (twist.symm y)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem TwistUnitary.orthonormal_symm (hu : TwistUnitary twist) {κ : Type*} [DecidableEq κ] (B : κ → Vec)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (B k))) :
    Orthonormal ℂ (fun k => RestrictedTEInput.input (twist.symm (B k))) := by
  rw [orthonormal_iff_ite] at horth ⊢
  intro i j
  rw [hu.inner_symm]
  exact horth i j

theorem span_symm_mem {κ : Type*} [Fintype κ] (B : κ → Vec) (x : Vec)
    (hx : x ∈ Submodule.span ℂ (Set.range B)) :
    twist.symm x ∈ Submodule.span ℂ (Set.range (fun k => twist.symm (B k))) := by
  obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  refine (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨cf, ?_⟩
  simp [map_sum, map_smul]

theorem span_apply_mem {κ : Type*} [Fintype κ] (B : κ → Vec) (a : Vec)
    (ha : a ∈ Submodule.span ℂ (Set.range (fun k => twist.symm (B k)))) :
    twist a ∈ Submodule.span ℂ (Set.range B) := by
  obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp ha
  refine (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨cf, ?_⟩
  simp [map_sum, map_smul]

/-- The three estimates on the actual plane fields, up to a twist of the input: the fields converge, for large gain
index, to the parity total fields at the twisted input. -/
structure ActualFieldEstimatesTwisted {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ)
    (twist : Vec ≃ₗ[ℂ] Vec) (E H : ℕ → ℕ → RestrictedTEActualFields.FieldMap) : Prop where
  meas : ∀ (n r : ℕ) (x : Vec) (i : Fin 3),
    AEStronglyMeasurable (fun ξ => E n r x ξ i) volume ∧ AEStronglyMeasurable (fun ξ => H n r x ξ i) volume
  conv : ∀ᶠ n : ℕ in atTop, ∀ x : Vec, RestrictedTEIncoming.physicalPower x = 1 →
    ∀ ρ0 : ℝ, 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 →
      ∀ i, ‖E n r x ξ i - RestrictedTEActualFields.parityE r0 y ρ χ h R hρ hχ hi
          (RestrictedTEPartnerSmallness.scale q n) (twist x) ξ i‖ ≤ ε ∧
        ‖H n r x ξ i - RestrictedTEActualFields.parityH r0 y ρ χ h R hρ hχ hi
          (RestrictedTEPartnerSmallness.scale q n) (twist x) ξ i‖ ≤ ε
  tail : ∀ᶠ n : ℕ in atTop, ∀ (N : Nat) (B : Fin N → Vec),
    Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (C ρ1 : ℝ) (r1 : ℕ),
      ∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
        ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ →
          ‖RestrictedTEActualFields.fieldFlux (E n r) (H n r) x ξ‖ ≤ C / ‖ξ‖ ^ 3

/-- Un-twisting: the fields composed with the inverse twist for gain indices `≥ n0`, the parity model below. -/
def untwistFields (n0 : ℕ) (E : ℕ → ℕ → RestrictedTEActualFields.FieldMap) (twist : Vec ≃ₗ[ℂ] Vec)
    (model : ℕ → RestrictedTEActualFields.FieldMap) : ℕ → ℕ → RestrictedTEActualFields.FieldMap :=
  fun n r => if n0 ≤ n then (E n r).comp (twist.symm : Vec →ₗ[ℂ] Vec) else model n

theorem untwistFields_apply (n0 : ℕ) (E : ℕ → ℕ → RestrictedTEActualFields.FieldMap) (twist : Vec ≃ₗ[ℂ] Vec)
    (model : ℕ → RestrictedTEActualFields.FieldMap) (n r : ℕ) (hn : n0 ≤ n) (x : Vec) :
    untwistFields n0 E twist model n r x = E n r (twist.symm x) := by
  unfold untwistFields
  rw [if_pos hn]
  rfl

theorem fieldFlux_untwist (n0 : ℕ) (E H : ℕ → ℕ → RestrictedTEActualFields.FieldMap) (twist : Vec ≃ₗ[ℂ] Vec)
    (mE mH : ℕ → RestrictedTEActualFields.FieldMap) (n r : ℕ) (hn : n0 ≤ n) (x : Vec) :
    RestrictedTEActualFields.fieldFlux (untwistFields n0 E twist mE n r) (untwistFields n0 H twist mH n r) x =
      RestrictedTEActualFields.fieldFlux (E n r) (H n r) (twist.symm x) := by
  funext ξ
  unfold RestrictedTEActualFields.fieldFlux
  rw [untwistFields_apply n0 E twist mE n r hn, untwistFields_apply n0 H twist mH n r hn]

end Twisted

/-! ### From the twisted estimates to the untwisted ones -/

section Untwist
open OQ14.RestrictedTEPartnerSmallness
open scoped ComplexInnerProductSpace

/-- The twisted estimates give the untwisted estimates for the fields composed with the inverse twist (for gain
indices from some `n0` on, the parity model below `n0`). -/
theorem untwist_estimates {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ)
    (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hR : 0 ≤ R) (hρh : ρ < h)
    (q : ℝ) (hq : 1 < q) (twist : Vec ≃ₗ[ℂ] Vec) (hu : TwistUnitary twist)
    (E H : ℕ → ℕ → RestrictedTEActualFields.FieldMap)
    (hest : ActualFieldEstimatesTwisted r0 y ρ χ h R hρ hχ hi q twist E H) :
    ∃ n0 : ℕ, RestrictedTEActualFields.ActualFieldEstimates r0 y ρ χ h R hρ hχ hi q
      (untwistFields n0 E twist (fun n => RestrictedTEActualFields.parityEMap r0 y ρ χ h R hρ hχ hi hρh
        (scale q n) (scale_pos hq n) (scale_le_one hq.le n)))
      (untwistFields n0 H twist (fun n => RestrictedTEActualFields.parityHMap r0 y ρ χ h R hρ hχ hi hρh
        (scale q n) (scale_pos hq n) (scale_le_one hq.le n))) := by
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp (hest.conv.and hest.tail)
  have hpar := RestrictedTEActualFields.ActualFieldEstimates.parity r0 y ρ χ h R hρ hχ hi hR hρh q hq
  refine ⟨n0, ?_, ?_, ?_⟩
  · intro n r x i
    by_cases hn : n0 ≤ n
    · rw [untwistFields_apply n0 E twist _ n r hn x, untwistFields_apply n0 H twist _ n r hn x]
      exact hest.meas n r (twist.symm x) i
    · have e1 : untwistFields n0 E twist (fun n => RestrictedTEActualFields.parityEMap r0 y ρ χ h R hρ hχ hi hρh
          (scale q n) (scale_pos hq n) (scale_le_one hq.le n)) n r =
          RestrictedTEActualFields.parityEMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n)
            (scale_le_one hq.le n) := by
        unfold untwistFields
        rw [if_neg hn]
      have e2 : untwistFields n0 H twist (fun n => RestrictedTEActualFields.parityHMap r0 y ρ χ h R hρ hχ hi hρh
          (scale q n) (scale_pos hq n) (scale_le_one hq.le n)) n r =
          RestrictedTEActualFields.parityHMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n)
            (scale_le_one hq.le n) := by
        unfold untwistFields
        rw [if_neg hn]
      rw [e1, e2]
      exact hpar.meas n r x i
  · intro n x hx ρ0 hρ0 ε hε
    by_cases hn : n0 ≤ n
    · have h1 := (hn0 n hn).1 (twist.symm x) (by rw [hu.power_symm]; exact hx) ρ0 hρ0 ε hε
      filter_upwards [h1] with r hr ξ hξ i
      rw [untwistFields_apply n0 E twist _ n r hn x, untwistFields_apply n0 H twist _ n r hn x]
      have := hr ξ hξ i
      rwa [LinearEquiv.apply_symm_apply] at this
    · have e1 : untwistFields n0 E twist (fun n => RestrictedTEActualFields.parityEMap r0 y ρ χ h R hρ hχ hi hρh
          (scale q n) (scale_pos hq n) (scale_le_one hq.le n)) n =
          fun r => RestrictedTEActualFields.parityEMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n)
            (scale_le_one hq.le n) := by
        funext r
        unfold untwistFields
        rw [if_neg hn]
      have e2 : untwistFields n0 H twist (fun n => RestrictedTEActualFields.parityHMap r0 y ρ χ h R hρ hχ hi hρh
          (scale q n) (scale_pos hq n) (scale_le_one hq.le n)) n =
          fun r => RestrictedTEActualFields.parityHMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n)
            (scale_le_one hq.le n) := by
        funext r
        unfold untwistFields
        rw [if_neg hn]
      filter_upwards [hpar.conv n x hx ρ0 hρ0 ε hε] with r hr ξ hξ i
      rw [e1, e2]
      exact hr ξ hξ i
  · intro N B horth n
    by_cases hn : n0 ≤ n
    · obtain ⟨C, ρ1, r1, h1⟩ := (hn0 n hn).2 N (fun k => twist.symm (B k)) (hu.orthonormal_symm B horth)
      refine ⟨C, ρ1, r1, fun r hr x hx hp ξ hξ => ?_⟩
      rw [fieldFlux_untwist n0 E H twist _ _ n r hn x]
      exact h1 r hr (twist.symm x) (span_symm_mem B x hx) (by rw [hu.power_symm]; exact hp) ξ hξ
    · have e1 : ∀ r, untwistFields n0 E twist (fun n => RestrictedTEActualFields.parityEMap r0 y ρ χ h R hρ hχ
          hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n)) n r =
          RestrictedTEActualFields.parityEMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n)
            (scale_le_one hq.le n) := fun r => by
        unfold untwistFields
        rw [if_neg hn]
      have e2 : ∀ r, untwistFields n0 H twist (fun n => RestrictedTEActualFields.parityHMap r0 y ρ χ h R hρ hχ
          hi hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n)) n r =
          RestrictedTEActualFields.parityHMap r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n)
            (scale_le_one hq.le n) := fun r => by
        unfold untwistFields
        rw [if_neg hn]
      obtain ⟨C, ρ1, r1, h1⟩ := hpar.tail N B horth n
      refine ⟨C, ρ1, r1, fun r hr x hx hp ξ hξ => ?_⟩
      rw [e1 r, e2 r]
      exact h1 r hr x hx hp ξ hξ

end Untwist

/-! ### The counted-subspace theorem with the twisted field estimates -/

section FinalTwisted
open OQ14.RestrictedTEPassageTransfer OQ14.RestrictedTEActualCounting OQ14.RestrictedTEActualWindow
  OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEConcreteDoubled OQ14.RestrictedTEPartnerBalls OQ14.RestrictedTEPlaneJets
  OQ14.RestrictedTEPartnerCount OQ14.RestrictedTEPartnerSmallness OQ14.ChannelMaterialThroughput
  OQ14.RestrictedTEActualSquare

/-- **Counted subspaces for plane fields converging to the twisted parity fields.**  Let `twist` be a unitary
linear automorphism of the finite input space.  For every `ε₊ > 1`, `N`, thresholds `0 < η < δ`, `τ ≤ 1` and
half-side `L > 0` there are the device parameters of `actual_counted_subspaces_square` and the physical family
`A_k = twist⁻¹ B_k` (`B_k` the parity interpolation family of the square theorem; orthonormal because `twist` is
unitary), spanning an `N`-dimensional subspace, such that for every family of linear plane fields `E n r`, `H n r`
with `ActualFieldEstimatesTwisted` (measurability, convergence to the parity total fields at the twisted input,
and the inverse-cube tail majorant of the flux) the span of `A` is counted through the square `Dsq L`, eventually
in `n` and then in `r`. -/
theorem actual_counted_subspaces_of_fields_twisted (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) (twist : Vec ≃ₗ[ℂ] Vec)
    (hu : TwistUnitary twist) :
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
      ∀ E H : ℕ → ℕ → RestrictedTEActualFields.FieldMap,
        ActualFieldEstimatesTwisted (-L) (ysq N L) ρ χ h R hρ hχ hi q twist E H →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dsq L) (RestrictedTEActualFields.fieldFlux (E n r) (H n r) a))
            (fun a => bypass volume (Dsq L) (RestrictedTEActualFields.fieldFlux (E n r) (H n r) a)) τ η δ := by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, B, hq2, hχε, horthB, hrankB, hperm, hcount⟩ :=
    RestrictedTEActualFields.actual_counted_subspaces_of_fields εp hεp N η δ hη hηδ τ hτ L hL
  have horthA : Orthonormal ℂ (fun k => RestrictedTEInput.input (twist.symm (B k))) :=
    hu.orthonormal_symm B horthB
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, fun k => twist.symm (B k), hq2, hχε, horthA, ?_, hperm, ?_⟩
  · have hli : LinearIndependent ℂ (fun k => twist.symm (B k)) :=
      LinearIndependent.of_comp (RestrictedTEInput.input : (SymmetricHarmonicJets.Index →₀ ℂ) →ₗ[ℂ]
        ComplexVectorSphere.Ambient) horthA.linearIndependent
    rw [finrank_span_eq_card hli]
    simp
  · intro E H hest
    obtain ⟨n0, hAFE⟩ := untwist_estimates (-L) (ysq N L) ρ χ h R hρ hχ hi hR hρh q hq twist hu E H hest
    have h1 := hcount _ _ hAFE
    have hb0 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
    have hiso := actualScatter_norm_eventually (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a))
      ρ χ R (max R 1) hρ hχ.le hb0 (le_max_left R 1) hi q hq
    filter_upwards [h1, hiso, eventually_ge_atTop n0] with n hn1 hiso' hn
    filter_upwards [hn1, hiso'] with r hr hT a ha
    have hb : twist a ∈ Submodule.span ℂ (Set.range B) := span_apply_mem B a ha
    obtain ⟨c1, c2, c3⟩ := hr (twist a) hb
    beta_reduce at c1 c2 c3
    have hflux : RestrictedTEActualFields.fieldFlux
        (untwistFields n0 E twist (fun n => RestrictedTEActualFields.parityEMap (-L) (ysq N L) ρ χ h R hρ hχ hi
          hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n)) n r)
        (untwistFields n0 H twist (fun n => RestrictedTEActualFields.parityHMap (-L) (ysq N L) ρ χ h R hρ hχ hi
          hρh (scale q n) (scale_pos hq n) (scale_le_one hq.le n)) n r) (twist a) =
        RestrictedTEActualFields.fieldFlux (E n r) (H n r) a := by
      rw [fieldFlux_untwist n0 E H twist _ _ n r hn (twist a), LinearEquiv.symm_apply_apply]
    rw [hflux] at c2 c3
    have hp := hu.power a
    have hpa := hT a
    have hpb := hT (twist a)
    rw [hp] at hpb
    beta_reduce
    refine ⟨?_, ?_, ?_⟩
    · rw [hpa]
      have := RestrictedTEIncoming.physical_power_nonnegative a
      nlinarith [mul_nonneg (sub_nonneg.mpr hτ) this]
    · rw [hpa]
      rw [hpb] at c2
      exact c2
    · rw [hp] at c3
      exact c3

end FinalTwisted

/-! ### Assembling the twisted estimates from the core fields -/

section OfCore
open OQ14.RestrictedTEPartnerSmallness OQ14.RestrictedTEPartnerBalls

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ → ι → Sp} {ρ χ R γ : ℝ}
  (hd : Device p ρ χ R γ) {q : ℝ} (hq : 1 < q) {b : ℝ} (hRb : R ≤ b)
include hRb

/-- The core fields of the doubled device converge, eventually in the gain index, uniformly on every disk to the
raw limit. -/
theorem core_conv_raw_eventually (hb0 : 0 < b) :
    ∀ᶠ n : ℕ in atTop, ∀ (A : Vec) (ρ0 : ℝ), 0 < ρ0 → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop,
      ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≤ ρ0 → ∀ i,
        ‖coreE q hq.le n r (deviceCoeff p ρ χ hd.hχ q n) (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A ξ i -
          rawLimitE q hq.le n (deviceCoeff p ρ χ hd.hχ q n)
            (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A ξ i‖ ≤ ε ∧
        ‖coreH q hq.le n r (deviceCoeff p ρ χ hd.hχ q n) (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A ξ i -
          rawLimitH q hq.le n (deviceCoeff p ρ χ hd.hχ q n)
            (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) A ξ i‖ ≤ ε := by
  filter_upwards [device_conv_raw hd hq hRb hb0] with n h
  intro A ρ0 hρ0 ε hε
  filter_upwards [h A ρ0 hρ0 ε hε, SourcePairedReduction.eventually_inner_radius q hq.le n b,
    RadialPhaseLimit.radius_tendsto.eventually (eventually_gt_atTop ρ0)] with r hr hbr hρ ξ hξ i
  have hξR : ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R := lt_of_le_of_lt hξ hρ
  have := hr ξ hξ i
  rwa [deviceFieldE_apply hd hq hRb n r hbr A ξ hξR, deviceFieldH_apply hd hq hRb n r hbr A ξ hξR] at this

/-- **Convergence of any fields agreeing with the core fields on the core.**  If the fields `E n r`, `H n r`
coincide on the open core with the assembled fields of the combined device (for large `r`) and the vector rescaled
degreewise by the limiting transmissions is `q^n` times the twisted input (for large `n`), the fields converge
uniformly on every disk to the parity total fields at the twisted input. -/
theorem core_agree_conv_twisted (hb0 : 0 < b) (twist : Vec ≃ₗ[ℂ] Vec)
    (htw : ∀ᶠ n : ℕ in atTop, ∀ x : Vec,
      BackgroundCoreTransmission.scaledCoeff x (transInf q hq.le n) = ((q ^ n : ℝ) : ℂ) • twist x)
    (E H : ℕ → ℕ → RestrictedTEActualFields.FieldMap)
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
        ‖E n r x ξ i - parityEg p ρ χ R hd.hρ hd.hχ hd.hi (scale q n) (twist x) ξ i‖ ≤ ε ∧
        ‖H n r x ξ i - parityHg p ρ χ R hd.hρ hd.hχ hd.hi (scale q n) (twist x) ξ i‖ ≤ ε := by
  filter_upwards [core_conv_raw_eventually hd hq hRb hb0, htw] with n h htw'
  intro x ρ0 hρ0 ε hε
  filter_upwards [h x ρ0 hρ0 ε hε, hE n, hH n,
    RadialPhaseLimit.radius_tendsto.eventually (eventually_gt_atTop ρ0)] with r hr hEr hHr hρ ξ hξ i
  have hξR : ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R := lt_of_le_of_lt hξ hρ
  obtain ⟨h1, h2⟩ := hr ξ hξ i
  rw [rawLimitE_eq_parity hd hq n x (twist x) (htw' x) ξ] at h1
  rw [rawLimitH_eq_parity hd hq n x (twist x) (htw' x) ξ] at h2
  rw [hEr x ξ hξR, hHr x ξ hξR]
  exact ⟨h1, h2⟩

end OfCore

section OfCoreConcrete
open OQ14.RestrictedTEPartnerSmallness

/-- The concrete doubled device (balls of radius `ρ a` at height `h a` above the points `(r0, y_l)`, with
`ρ < h`) satisfies the hypotheses of `Device` with `γ = h - ρ`. -/
theorem concrete_device {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hρh : ρ < h)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) :
    Device (fun a l => OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)) ρ χ R (h - ρ) where
  hρ := hρ
  hχ := hχ
  hγ := by linarith
  hi := hi
  hh := by
    intro a ha ha1 l
    rw [OQ14.RestrictedTEDipoleConcentration.above_normal, abs_of_pos (mul_pos (by linarith) ha)]
    linarith

/-- The agreement of the actual plane fields `E n r`, `H n r` of the paired device with the assembled core fields on
the open core, together with the two global properties of the fields (measurability, inverse-cube tail of the flux)
that the cut-off core fields cannot provide: this is what the definition of the fields outside the core must supply. -/
structure CoreAgreement {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ)
    (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q)
    (E H : ℕ → ℕ → RestrictedTEActualFields.FieldMap) : Prop where
  meas : ∀ (n r : ℕ) (x : Vec) (i : Fin 3),
    AEStronglyMeasurable (fun ξ => E n r x ξ i) volume ∧ AEStronglyMeasurable (fun ξ => H n r x ξ i) volume
  agreeE : ∀ n : ℕ, ∀ᶠ r : ℕ in atTop, ∀ (x : Vec) (ξ : PlaneInverseCube.Plane),
    ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R →
      E n r x ξ = coreE q hq.le n r
        (deviceCoeff (fun a l => OQ14.RestrictedTEDipoleProfile.abovePoint
          (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)) ρ χ hχ.le q n)
        (deviceData (fun a l => OQ14.RestrictedTEDipoleProfile.abovePoint
          (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)) ρ χ R hρ hχ.le hi q hq n) x ξ
  agreeH : ∀ n : ℕ, ∀ᶠ r : ℕ in atTop, ∀ (x : Vec) (ξ : PlaneInverseCube.Plane),
    ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R →
      H n r x ξ = coreH q hq.le n r
        (deviceCoeff (fun a l => OQ14.RestrictedTEDipoleProfile.abovePoint
          (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)) ρ χ hχ.le q n)
        (deviceData (fun a l => OQ14.RestrictedTEDipoleProfile.abovePoint
          (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)) ρ χ R hρ hχ.le hi q hq n) x ξ
  tail : ∀ᶠ n : ℕ in atTop, ∀ (N : Nat) (B : Fin N → Vec),
    Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (C ρ1 : ℝ) (r1 : ℕ),
      ∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
        ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ →
          ‖RestrictedTEActualFields.fieldFlux (E n r) (H n r) x ξ‖ ≤ C / ‖ξ‖ ^ 3

/-- **The twisted estimates from the core.**  For the concrete doubled device, fields agreeing with the assembled
core fields on the open core (for large `r`), whose coordinates are a.e.-strongly measurable and whose flux has the
inverse-cube tail majorant (`CoreAgreement`), satisfy `ActualFieldEstimatesTwisted` as soon as the vector rescaled
degreewise by the limiting transmissions is `q^n` times the twisted input for large `n`.  The convergence field is
proved here from the identification and background modules. -/
theorem ActualFieldEstimatesTwisted.of_core {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hρh : ρ < h) {q : ℝ} (hq : 1 < q)
    {b : ℝ} (hb0 : 0 < b) (hRb : R ≤ b) (twist : Vec ≃ₗ[ℂ] Vec)
    (htw : ∀ᶠ n : ℕ in atTop, ∀ x : Vec,
      BackgroundCoreTransmission.scaledCoeff x (transInf q hq.le n) = ((q ^ n : ℝ) : ℂ) • twist x)
    (E H : ℕ → ℕ → RestrictedTEActualFields.FieldMap)
    (hc : CoreAgreement r0 y ρ χ h R hρ hχ hi q hq E H) :
    ActualFieldEstimatesTwisted r0 y ρ χ h R hρ hχ hi q twist E H where
  meas := hc.meas
  conv := by
    have hd := concrete_device r0 y ρ χ h R hρ hχ.le hρh hi
    filter_upwards [core_agree_conv_twisted hd hq hRb hb0 twist htw E H hc.agreeE hc.agreeH] with n hn x _ ρ0 hρ0 ε hε
    filter_upwards [hn x ρ0 hρ0 ε hε] with r hr ξ hξ i
    exact hr ξ hξ i
  tail := hc.tail

end OfCoreConcrete

/-! ### Consistency checks and the composite theorem -/

section Composite
open OQ14.RestrictedTEPartnerSmallness
open scoped ComplexInnerProductSpace

theorem span_equiv_mem {κ : Type*} [Fintype κ] (e : Vec ≃ₗ[ℂ] Vec) (B : κ → Vec) (x : Vec)
    (hx : x ∈ Submodule.span ℂ (Set.range B)) :
    e x ∈ Submodule.span ℂ (Set.range (fun k => e (B k))) := by
  obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  refine (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨cf, ?_⟩
  simp [map_sum, map_smul]

/-- Consistency check: the parity total fields composed with a unitary twist satisfy the twisted estimates. -/
theorem ActualFieldEstimatesTwisted.parity_twist {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hR : 0 ≤ R) (hρh : ρ < h)
    (q : ℝ) (hq : 1 < q) (twist : Vec ≃ₗ[ℂ] Vec) (hu : TwistUnitary twist) :
    ActualFieldEstimatesTwisted r0 y ρ χ h R hρ hχ hi q twist
      (fun n _ => (RestrictedTEActualFields.parityEMap r0 y ρ χ h R hρ hχ hi hρh (scale q n)
        (scale_pos hq n) (scale_le_one hq.le n)).comp (twist : Vec →ₗ[ℂ] Vec))
      (fun n _ => (RestrictedTEActualFields.parityHMap r0 y ρ χ h R hρ hχ hi hρh (scale q n)
        (scale_pos hq n) (scale_le_one hq.le n)).comp (twist : Vec →ₗ[ℂ] Vec)) where
  meas := fun n r x i =>
    ⟨(RestrictedTEActualFields.parityE_continuous r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n)
      (scale_le_one hq.le n) (twist x) i).aestronglyMeasurable,
     (RestrictedTEActualFields.parityH_continuous r0 y ρ χ h R hρ hχ hi hρh (scale q n) (scale_pos hq n)
      (scale_le_one hq.le n) (twist x) i).aestronglyMeasurable⟩
  conv := by
    refine Eventually.of_forall (fun n x _ ρ0 _ ε hε => Eventually.of_forall (fun r ξ _ i => ⟨?_, ?_⟩))
    · change ‖RestrictedTEActualFields.parityE r0 y ρ χ h R hρ hχ hi (scale q n) (twist x) ξ i -
        RestrictedTEActualFields.parityE r0 y ρ χ h R hρ hχ hi (scale q n) (twist x) ξ i‖ ≤ ε
      rw [sub_self, norm_zero]
      exact hε.le
    · change ‖RestrictedTEActualFields.parityH r0 y ρ χ h R hρ hχ hi (scale q n) (twist x) ξ i -
        RestrictedTEActualFields.parityH r0 y ρ χ h R hρ hχ hi (scale q n) (twist x) ξ i‖ ≤ ε
      rw [sub_self, norm_zero]
      exact hε.le
  tail := by
    refine Eventually.of_forall (fun n N B horth => ?_)
    have horth' : Orthonormal ℂ (fun k => RestrictedTEInput.input (twist (B k))) := by
      rw [orthonormal_iff_ite] at horth ⊢
      intro i j
      rw [hu]
      exact horth i j
    obtain ⟨C, ρ1, r1, h1⟩ := (RestrictedTEActualFields.ActualFieldEstimates.parity r0 y ρ χ h R hρ hχ hi hR
      hρh q hq).tail N (fun k => twist (B k)) horth' n
    refine ⟨C, ρ1, r1, fun r hr x hx hp ξ hξ => ?_⟩
    exact h1 r hr (twist x) (span_equiv_mem twist B x hx) (by rw [hu.power]; exact hp) ξ hξ

end Composite

section CompositeFinal
open OQ14.RestrictedTEPassageTransfer OQ14.RestrictedTEActualCounting OQ14.RestrictedTEActualWindow
  OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEConcreteDoubled OQ14.RestrictedTEPartnerBalls OQ14.RestrictedTEPlaneJets
  OQ14.RestrictedTEPartnerCount OQ14.RestrictedTEPartnerSmallness OQ14.ChannelMaterialThroughput
  OQ14.RestrictedTEActualSquare

/-- **Counted subspaces from the core identification.**  Let `twist` be a unitary linear automorphism of the finite
input space such that, for every `q > 1` and all large `n`, the input rescaled degreewise by the limiting
transmissions over two is `q^n` times its twist.  Then, with the device parameters of the square theorem and the
physical family `A_k = twist⁻¹ B_k`, for every family of linear plane fields `E n r`, `H n r` that agrees with
the assembled fields of the combined device on the open core and is measurable with an inverse-cube tail majorant
of its flux (`CoreAgreement`), the span of `A` is counted through the square `Dsq L`, eventually in `n` and then in
`r`.  The convergence of the fields on every disk is proved from the identification and background modules. -/
theorem actual_counted_subspaces_of_core (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) (twist : Vec ≃ₗ[ℂ] Vec)
    (hu : TwistUnitary twist)
    (htw : ∀ (q : ℝ) (hq : 1 < q), ∀ᶠ n : ℕ in atTop, ∀ x : Vec,
      BackgroundCoreTransmission.scaledCoeff x (transInf q hq.le n) = ((q ^ n : ℝ) : ℂ) • twist x) :
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
      ∀ E H : ℕ → ℕ → RestrictedTEActualFields.FieldMap,
        CoreAgreement (-L) (ysq N L) ρ χ h R hρ hχ hi q hq E H →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dsq L) (RestrictedTEActualFields.fieldFlux (E n r) (H n r) a))
            (fun a => bypass volume (Dsq L) (RestrictedTEActualFields.fieldFlux (E n r) (H n r) a)) τ η δ := by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6⟩ :=
    actual_counted_subspaces_of_fields_twisted εp hεp N η δ hη hηδ τ hτ L hL twist hu
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, ?_⟩
  intro E H hc
  have hb0 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  exact h6 E H (ActualFieldEstimatesTwisted.of_core (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq hb0
    (le_max_left R 1) twist (htw q hq) E H hc)

end CompositeFinal

section DeviceAgree
open OQ14.RestrictedTEPartnerSmallness
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ → ι → Sp} {ρ χ R γ : ℝ}
  (hd : Device p ρ χ R γ) {q : ℝ} (hq : 1 < q) {b : ℝ} (hRb : R ≤ b)

/-- The cut-off core fields agree with the assembled fields on the open core, for large shell index. -/
theorem deviceFieldE_agree (n : ℕ) :
    ∀ᶠ r : ℕ in atTop, ∀ (x : Vec) (ξ : PlaneInverseCube.Plane),
      ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R →
        deviceFieldE hd hq hRb n r x ξ = coreE q hq.le n r (deviceCoeff p ρ χ hd.hχ q n)
          (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) x ξ := by
  filter_upwards [SourcePairedReduction.eventually_inner_radius q hq.le n b] with r hbr x ξ hξ
  exact deviceFieldE_apply hd hq hRb n r hbr x ξ hξ

theorem deviceFieldH_agree (n : ℕ) :
    ∀ᶠ r : ℕ in atTop, ∀ (x : Vec) (ξ : PlaneInverseCube.Plane),
      ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R →
        deviceFieldH hd hq hRb n r x ξ = coreH q hq.le n r (deviceCoeff p ρ χ hd.hχ q n)
          (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) x ξ := by
  filter_upwards [SourcePairedReduction.eventually_inner_radius q hq.le n b] with r hbr x ξ hξ
  exact deviceFieldH_apply hd hq hRb n r hbr x ξ hξ

end DeviceAgree

end OQ14.RestrictedTEActualCore
#print axioms OQ14.RestrictedTEActualCore.fsLin_apply
#print axioms OQ14.RestrictedTEActualCore.fiLin_apply
#print axioms OQ14.RestrictedTEActualCore.fs_isDatum
#print axioms OQ14.RestrictedTEActualCore.fi_isDatum
#print axioms OQ14.RestrictedTEActualCore.carrier_dist
#print axioms OQ14.RestrictedTEActualCore.incl_admissible
#print axioms OQ14.RestrictedTEActualCore.shell_hcs'
#print axioms OQ14.RestrictedTEActualCore.electric_split
#print axioms OQ14.RestrictedTEActualCore.magnetic_split
#print axioms OQ14.RestrictedTEActualCore.scatteredE_clm
#print axioms OQ14.RestrictedTEActualCore.scatteredH_clm
#print axioms OQ14.RestrictedTEActualCore.shell_vanish_outer
#print axioms OQ14.RestrictedTEActualCore.shell_source_vanish_inner
#print axioms OQ14.RestrictedTEActualCore.shell_electric_contDiffAt
#print axioms OQ14.RestrictedTEActualCore.shell_magnetic_contDiffAt
#print axioms OQ14.RestrictedTEActualCore.coreE_apply
#print axioms OQ14.RestrictedTEActualCore.coreH_apply
#print axioms OQ14.RestrictedTEActualCore.coreSol_comb
#print axioms OQ14.RestrictedTEActualCore.electric_comb'
#print axioms OQ14.RestrictedTEActualCore.magnetic_comb'
#print axioms OQ14.RestrictedTEActualCore.coreE_comb
#print axioms OQ14.RestrictedTEActualCore.coreH_comb
#print axioms OQ14.RestrictedTEActualCore.coreE_zero
#print axioms OQ14.RestrictedTEActualCore.coreH_zero
#print axioms OQ14.RestrictedTEActualCore.coreEMap_apply
#print axioms OQ14.RestrictedTEActualCore.coreHMap_apply
#print axioms OQ14.RestrictedTEActualCore.coreE_continuousOn
#print axioms OQ14.RestrictedTEActualCore.coreH_continuousOn
#print axioms OQ14.RestrictedTEActualCore.core_set_measurable
#print axioms OQ14.RestrictedTEActualCore.coreEMap_meas
#print axioms OQ14.RestrictedTEActualCore.coreHMap_meas
#print axioms OQ14.RestrictedTEActualCore.tsupport_dcoord_subset'
#print axioms OQ14.RestrictedTEActualCore.tsupport_testPartial_subset'
#print axioms OQ14.RestrictedTEActualCore.integrable_mul_test'
#print axioms OQ14.RestrictedTEActualCore.weak_unique
#print axioms OQ14.RestrictedTEActualCore.trans_tendsto
#print axioms OQ14.RestrictedTEActualCore.total_eq_background_ae
#print axioms OQ14.RestrictedTEActualCore.backgroundElectric_eq_core
#print axioms OQ14.RestrictedTEActualCore.backgroundMagnetic_eq_core
#print axioms OQ14.RestrictedTEActualCore.bounded_on_ball
#print axioms OQ14.RestrictedTEActualCore.scaled_uniform
#print axioms OQ14.RestrictedTEActualCore.backgroundElectric_conv
#print axioms OQ14.RestrictedTEActualCore.backgroundMagnetic_conv
#print axioms OQ14.RestrictedTEActualCore.effectiveDatum_eq_datum
#print axioms OQ14.RestrictedTEActualCore.effectiveDatum_conv
#print axioms OQ14.RestrictedTEActualCore.gLim_fixed
#print axioms OQ14.RestrictedTEActualCore.coreE_conv_raw
#print axioms OQ14.RestrictedTEActualCore.coreH_conv_raw
#print axioms OQ14.RestrictedTEActualCore.device_carrier_gap
#print axioms OQ14.RestrictedTEActualCore.device_setup
#print axioms OQ14.RestrictedTEActualCore.deviceFieldE_apply
#print axioms OQ14.RestrictedTEActualCore.deviceFieldH_apply
#print axioms OQ14.RestrictedTEActualCore.deviceField_meas
#print axioms OQ14.RestrictedTEActualCore.device_conv_raw
#print axioms OQ14.RestrictedTEActualCore.parityE_eq_parityEg
#print axioms OQ14.RestrictedTEActualCore.parityH_eq_parityHg
#print axioms OQ14.RestrictedTEActualCore.device_coeff_eq
#print axioms OQ14.RestrictedTEActualCore.parity_solution_congr
#print axioms OQ14.RestrictedTEActualCore.scale_inv_cast
#print axioms OQ14.RestrictedTEActualCore.parity_source_eq
#print axioms OQ14.RestrictedTEActualCore.rawLimitE_eq_parity
#print axioms OQ14.RestrictedTEActualCore.rawLimitH_eq_parity
#print axioms OQ14.RestrictedTEActualCore.device_conv_twisted
#print axioms OQ14.RestrictedTEActualCore.TwistUnitary.power
#print axioms OQ14.RestrictedTEActualCore.TwistUnitary.power_symm
#print axioms OQ14.RestrictedTEActualCore.TwistUnitary.inner_symm
#print axioms OQ14.RestrictedTEActualCore.TwistUnitary.orthonormal_symm
#print axioms OQ14.RestrictedTEActualCore.span_symm_mem
#print axioms OQ14.RestrictedTEActualCore.span_apply_mem
#print axioms OQ14.RestrictedTEActualCore.untwistFields_apply
#print axioms OQ14.RestrictedTEActualCore.fieldFlux_untwist
#print axioms OQ14.RestrictedTEActualCore.untwist_estimates
#print axioms OQ14.RestrictedTEActualCore.actual_counted_subspaces_of_fields_twisted
#print axioms OQ14.RestrictedTEActualCore.core_conv_raw_eventually
#print axioms OQ14.RestrictedTEActualCore.core_agree_conv_twisted
#print axioms OQ14.RestrictedTEActualCore.concrete_device
#print axioms OQ14.RestrictedTEActualCore.ActualFieldEstimatesTwisted.of_core
#print axioms OQ14.RestrictedTEActualCore.span_equiv_mem
#print axioms OQ14.RestrictedTEActualCore.ActualFieldEstimatesTwisted.parity_twist
#print axioms OQ14.RestrictedTEActualCore.actual_counted_subspaces_of_core
#print axioms OQ14.RestrictedTEActualCore.deviceFieldE_agree
#print axioms OQ14.RestrictedTEActualCore.deviceFieldH_agree
