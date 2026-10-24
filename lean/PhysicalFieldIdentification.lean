import RestrictedTEActualPiecewise
import RestrictedTEBackgroundOutside
import ExteriorMaterialOffCarrier
import SourceRadiatedFlux
import SourceRadiatedAnnulus

/-! The piecewise device fields of the assembly are the physical fields.

For the combined shell-plus-inclusion device at shell index `r` and a fixed input vector `x`, the physical fields
are the `L2` total electric field `MaterialField.total (add cs ci) 1 (coreSol x) (electric x)` (`physE`), its continuous
exterior representative `ExteriorMaterial.total` (`extE`), and the pointwise total magnetic field
`MaterialMaxwell.totalMagnetic (add cs ci) 1 (coreSol x) (magnetic x)` (`physH`).  The piecewise fields of the
assembly are the core fields `coreE`, `coreH` on the open core and the outside fields (TE background plus the radiated
mode series) beyond; their space versions are `spaceFieldE`, `spaceFieldH`.  This module identifies the physical fields
with the space versions, region by region, with no hypothesis on the shell annulus (the annulus identification of the
radiated field is the frozen `SourceRadiatedAnnulus`).

* `core_identification_electric`, `core_identification_magnetic`: on the open core the electric `L2` total field
  equals `coreE` (`coreEField`) almost everywhere off the closure of the carrier, and the magnetic total field is `coreH`
  at every point (the two expressions agree);
* `block_facts`, `exterior_split_electric`, `exterior_split_magnetic`: the combined solution is the shell response of
  the shell datum plus the shell response driven by `Ss T Si` of the inclusion part plus the inclusion part; outside
  the shell the continuous total fields split into the shell background and the field radiated by the inclusion part;
* `exterior_identification`: for all large shell index and every point outside the outer shell radius, the continuous
  exterior representative of the electric total field is `bgFieldE + radiatedE` and the total magnetic field is
  `bgFieldH + radiatedH` (the TE background and the all-degree layered mode series of the inclusion source,
  `paired_radiated_series_outside`, with the shell background identified with the TE background by
  `bgFieldE_eq_exterior` and `famBackgroundH_eq`); the bound of the inclusion solutions comes from
  `solution_bounded_of_coeffs`;
* `scattered_split3_ae`, `magnetic_split3_ae`, `annulus_identification_electric`, `annulus_identification_magnetic`:
  almost everywhere on the shell annulus, the same identifications, from the splitting of the `L2` scattered field
  and of the magnetic response of the combined source into the three parts, `famBackground_ae`,
  `famBackgroundH_eq` and the annulus identification of the radiated field `paired_annulus_electric_ae`,
  `paired_annulus_magnetic_ae`;
* `physical_identification_electric`, `physical_identification_magnetic`, `physical_identification`: eventually
  in the shell index, the physical fields are the space versions of the piecewise fields almost everywhere on the open
  core off the carrier closure, the shell annulus and the exterior (electric), at every point of the open core and of
  the exterior and almost everywhere in space (magnetic);
* `deviceFieldsE_eq_space`, `deviceFieldsH_eq_space`, `device_physical_identification`,
  `device_piecewise_identification`: the space versions at plane points are the piecewise device fields of the
  channel assembly, and the instantiation for the concrete doubled device. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.PhysicalFieldIdentification
open MeasureTheory Filter Topology Metric Set
open scoped ComplexConjugate

abbrev Vec := OQ14.RestrictedTEActualCore.Vec
abbrev VectorL2 := VectorFourier.VectorL2

/-! ### Splitting the response of a source supported in a ball, at exterior points -/

theorem response_split3 (K : Maxwell.Space → ℂ) (hK : ∀ z, z ≠ 0 → ContinuousAt K z) (X : ℝ)
    (y : Maxwell.Space) (hy : X < ‖y‖) (ρ ρ1 ρ2 ρ3 : Maxwell.Space → ℂ)
    (h : ρ =ᵐ[volume] fun z => ρ1 z + ρ2 z + ρ3 z)
    (i1 : Integrable ρ1 volume) (i2 : Integrable ρ2 volume) (i3 : Integrable ρ3 volume)
    (z1 : ∀ z, z ∉ closedBall (0 : Maxwell.Space) X → ρ1 z = 0)
    (z2 : ∀ z, z ∉ closedBall (0 : Maxwell.Space) X → ρ2 z = 0)
    (z3 : ∀ z, z ∉ closedBall (0 : Maxwell.Space) X → ρ3 z = 0) :
    KernelConvolution.response K ρ y = KernelConvolution.response K ρ1 y +
      KernelConvolution.response K ρ2 y + KernelConvolution.response K ρ3 y := by
  have a1 := NewtonExteriorResponse.source_integrand_integrable K ρ1 hK i1 X z1 y hy
  have a2 := NewtonExteriorResponse.source_integrand_integrable K ρ2 hK i2 X z2 y hy
  have a3 := NewtonExteriorResponse.source_integrand_integrable K ρ3 hK i3 X z3 y hy
  unfold KernelConvolution.response
  have a12 : Integrable (fun z => ρ1 z * K (y - z) + ρ2 z * K (y - z)) volume := a1.add a2
  rw [← integral_add a1 a2, ← integral_add a12 a3]
  apply integral_congr_ae
  filter_upwards [h] with z hz
  rw [hz]
  ring

theorem electric_split3 (X : ℝ) (y : Maxwell.Space) (hy : X < ‖y‖) (ρ ρ1 ρ2 ρ3 : Fin 3 → Maxwell.Space → ℂ)
    (h : ∀ j, ρ j =ᵐ[volume] fun z => ρ1 j z + ρ2 j z + ρ3 j z)
    (i1 : ∀ j, Integrable (ρ1 j) volume) (i2 : ∀ j, Integrable (ρ2 j) volume)
    (i3 : ∀ j, Integrable (ρ3 j) volume)
    (z1 : ∀ j z, z ∉ closedBall (0 : Maxwell.Space) X → ρ1 j z = 0)
    (z2 : ∀ j z, z ∉ closedBall (0 : Maxwell.Space) X → ρ2 j z = 0)
    (z3 : ∀ j z, z ∉ closedBall (0 : Maxwell.Space) X → ρ3 j z = 0) (i : Fin 3) :
    ExteriorContinuity.electric 1 ρ y i = ExteriorContinuity.electric 1 ρ1 y i +
      ExteriorContinuity.electric 1 ρ2 y i + ExteriorContinuity.electric 1 ρ3 y i := by
  unfold ExteriorContinuity.electric
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => response_split3 _
    (fun z hz => ExteriorContinuity.dyadic_continuousAt 1 i j z hz) X y hy _ _ _ _ (h j) (i1 j) (i2 j) (i3 j)
    (z1 j) (z2 j) (z3 j))

theorem magnetic_split3 (X : ℝ) (y : Maxwell.Space) (hy : X < ‖y‖) (ρ ρ1 ρ2 ρ3 : Fin 3 → Maxwell.Space → ℂ)
    (h : ∀ j, ρ j =ᵐ[volume] fun z => ρ1 j z + ρ2 j z + ρ3 j z)
    (i1 : ∀ j, Integrable (ρ1 j) volume) (i2 : ∀ j, Integrable (ρ2 j) volume)
    (i3 : ∀ j, Integrable (ρ3 j) volume)
    (z1 : ∀ j z, z ∉ closedBall (0 : Maxwell.Space) X → ρ1 j z = 0)
    (z2 : ∀ j z, z ∉ closedBall (0 : Maxwell.Space) X → ρ2 j z = 0)
    (z3 : ∀ j z, z ∉ closedBall (0 : Maxwell.Space) X → ρ3 j z = 0) (i : Fin 3) :
    MagneticResponse.magnetic 1 ρ y i = MagneticResponse.magnetic 1 ρ1 y i +
      MagneticResponse.magnetic 1 ρ2 y i + MagneticResponse.magnetic 1 ρ3 y i := by
  have hg (l : Fin 3) (z : Maxwell.Space) (hz : z ≠ 0) :
      ContinuousAt (fun w => GreenKernel.phiGradient 1 w l) z :=
    (KernelGradient.gradient_differentiableAt 1 l z hz).continuousAt
  unfold MagneticResponse.magnetic
  rw [response_split3 (fun w => GreenKernel.phiGradient 1 w (WeakCurl.next i)) (hg _) X y hy _ _ _ _
      (h (WeakCurl.previous i)) (i1 _) (i2 _) (i3 _) (z1 _) (z2 _) (z3 _),
    response_split3 (fun w => GreenKernel.phiGradient 1 w (WeakCurl.previous i)) (hg _) X y hy _ _ _ _
      (h (WeakCurl.next i)) (i1 _) (i2 _) (i3 _) (z1 _) (z2 _) (z3 _)]
  ring

/-! ### The block decomposition of the combined solution -/

section Blocks

/-- The inner shell radius, the outer shell radius and the shell of the paired device. -/
abbrev Rof (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) : ℝ := (SourcePairedInclusion.data q hq n r).R
abbrev Xof (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) : ℝ := (SourcePairedInclusion.data q hq n r).X
abbrev shellOf (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) : StaticCoefficient.Coefficient :=
  SourcePairedInclusion.shell q hq n r
/-- The shell response `r f` (the shell solution for the shell datum `f`). -/
abbrev shellResp (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (f : VectorL2) : VectorL2 :=
  Ring.inverse (DynamicVolume.volumeBlock (shellOf q hq n r) 1 (Xof q hq n r)) f
/-- The shell datum driven by an inclusion part `ui`: `Ss T Si ui`. -/
abbrev shellDrive (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient) (ui : VectorL2) :
    VectorL2 :=
  StaticCoefficient.sqrtMultiplier (shellOf q hq n r) (ShellInclusionVolume.kernel 1 (Xof q hq n r)
    (StaticCoefficient.sqrtMultiplier ci ui))

theorem block_facts (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient) (b : ℝ)
    (hb : b < Rof q hq n r)
    (hci : ∀ y : Maxwell.Space, y ∉ closedBall (0 : Maxwell.Space) b →
      ci.value (VectorFourier.coordinateMap y) = 0)
    (hE : IsUnit (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)) (fs fi : VectorL2)
    (hfi : StaticCoefficient.sqrtMultiplier (shellOf q hq n r) fi = 0)
    (hfs : StaticCoefficient.sqrtMultiplier ci fs = 0) (ui : VectorL2)
    (hui : ui = Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)
      (SourcePairedPlaneIdentification.effectiveDatum (shellOf q hq n r) ci (Xof q hq n r) fs fi)) :
    StaticCoefficient.sqrtMultiplier (ShellInclusionVolume.add (shellOf q hq n r) ci)
        (MaterialField.solution (ShellInclusionVolume.add (shellOf q hq n r) ci) 1 (Xof q hq n r) (fs + fi)) =
      StaticCoefficient.sqrtMultiplier (shellOf q hq n r) (shellResp q hq n r fs) +
        StaticCoefficient.sqrtMultiplier (shellOf q hq n r) (shellResp q hq n r (shellDrive q hq n r ci ui)) +
        StaticCoefficient.sqrtMultiplier ci ui ∧
    ∀ j : Fin 3, DynamicVolume.source (ShellInclusionVolume.add (shellOf q hq n r) ci)
        (MaterialField.solution (ShellInclusionVolume.add (shellOf q hq n r) ci) 1 (Xof q hq n r) (fs + fi)) j
      =ᵐ[volume] fun z => DynamicVolume.source (shellOf q hq n r) (shellResp q hq n r fs) j z +
        DynamicVolume.source (shellOf q hq n r) (shellResp q hq n r (shellDrive q hq n r ci ui)) j z +
        DynamicVolume.source ci ui j z := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hb.le hci
  have hs := SourcePairedInclusion.shell_isUnit q hq n r
  have hC := SourcePairedInclusion.combined_isUnit_of_effective q hq n r ci b hb.le hci hE
  obtain ⟨u, hu⟩ : ∃ u : VectorL2, u = MaterialField.solution (ShellInclusionVolume.add (shellOf q hq n r) ci) 1
    (Xof q hq n r) (fs + fi) := ⟨_, rfl⟩
  have hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add (shellOf q hq n r) ci) 1 (Xof q hq n r) u =
      fs + fi := by
    rw [hu]
    exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (fs + fi)) (Ring.mul_inverse_cancel _ hC)
  have hinc := SourcePairedPlaneIdentification.inclPart_eq_effective q hq n r ci b hb hci hE fs fi hfi hfs
  rw [← hu, ← hui] at hinc
  have hus := SourcePairedPlaneIdentification.shellPart_eq hd hs u fs fi hCu hfi hfs
  rw [hinc] at hus
  rw [← hu]
  refine ⟨?_, fun j => ?_⟩
  · rw [ShellInclusionVolume.sqrtMultiplier_add _ _ hd, ContinuousLinearMap.add_apply,
      SourcePairedPlaneIdentification.Ss_solution hd u fs fi hCu hfi,
      SourcePairedPlaneIdentification.Si_solution hd u fs fi hCu hfs, hus, hinc]
    simp only [map_add]
  · have hsrc := SourcePairedPlaneIdentification.combined_source_split hd u fs fi hCu hfi hfs j
    rw [hus, hinc] at hsrc
    filter_upwards [hsrc, SourcePairedPlaneIdentification.source_add_ae (shellOf q hq n r) (shellResp q hq n r fs)
      (shellResp q hq n r (shellDrive q hq n r ci ui)) j] with z h1 h2
    rw [h1, map_add, h2]

end Blocks

/-! ### The continuous total fields outside the shell split into background and radiated parts -/

theorem shell_support_X (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) :
    ∀ z : Maxwell.Space, z ∉ closedBall (0 : Maxwell.Space) (Xof q hq n r) →
      (shellOf q hq n r).value (VectorFourier.coordinateMap z) = 0 :=
  fun z hz => SourcePairedPlaneIdentification.shell_hcs q hq n r z (fun h => hz h.1)

theorem incl_support_X (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient) (b : ℝ)
    (hb : b < Rof q hq n r)
    (hci : ∀ y : Maxwell.Space, y ∉ closedBall (0 : Maxwell.Space) b →
      ci.value (VectorFourier.coordinateMap y) = 0) :
    ∀ z : Maxwell.Space, z ∉ closedBall (0 : Maxwell.Space) (Xof q hq n r) →
      ci.value (VectorFourier.coordinateMap z) = 0 :=
  fun z hz => hci z (fun h => hz (closedBall_subset_closedBall
    (hb.le.trans (SourcePairedInclusion.radii_ordered q hq n r)) h))

section ExteriorSplit

variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient) (b : ℝ)
  (hb : b < Rof q hq n r)
  (hci : ∀ y : Maxwell.Space, y ∉ closedBall (0 : Maxwell.Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
  (hE : IsUnit (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)) (inc : Maxwell.Field) (fs fi : VectorL2)
  (hfi : StaticCoefficient.sqrtMultiplier (shellOf q hq n r) fi = 0)
  (hfs : StaticCoefficient.sqrtMultiplier ci fs = 0) (ui : VectorL2)
  (hui : ui = Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)
    (SourcePairedPlaneIdentification.effectiveDatum (shellOf q hq n r) ci (Xof q hq n r) fs fi))
  (y : Maxwell.Space) (hy : Xof q hq n r < ‖y‖) (i : Fin 3)
include hb hci hE hfi hfs hui hy

/-- **Electric split outside the shell.**  For a point `y` outside the outer shell radius the continuous total
electric field of the combined solution is the shell background (incident field plus the shell response to the
shell datum) plus the field radiated by the inclusion part `ui`: its free field and the response of the shell driven
by `Ss T Si ui`. -/
theorem exterior_split_electric :
    SourcePairedPlaneIdentification.continuousTotalElectric (ShellInclusionVolume.add (shellOf q hq n r) ci)
        (Xof q hq n r) inc (fs + fi) y i =
      SourcePairedPlaneIdentification.backgroundElectric (shellOf q hq n r) (Xof q hq n r) inc fs y i +
        (ExteriorContinuity.electric 1 (DynamicVolume.source ci ui) y i +
          ExteriorContinuity.electric 1 (DynamicVolume.source (shellOf q hq n r)
            (shellResp q hq n r (shellDrive q hq n r ci ui))) y i) := by
  obtain ⟨_, hsrc⟩ := block_facts q hq n r ci b hb hci hE fs fi hfi hfs ui hui
  have hcsX := shell_support_X q hq n r
  have hciX := incl_support_X q hq n r ci b hb hci
  have h := electric_split3 (Xof q hq n r) y hy _ _ _ _ hsrc
    (fun j => DynamicVolume.source_integrable _ _ _ hcsX j) (fun j => DynamicVolume.source_integrable _ _ _ hcsX j)
    (fun j => DynamicVolume.source_integrable _ _ _ hciX j)
    (fun j z hz => DynamicVolume.source_zero _ _ _ hcsX j z hz)
    (fun j z hz => DynamicVolume.source_zero _ _ _ hcsX j z hz)
    (fun j z hz => DynamicVolume.source_zero _ _ _ hciX j z hz) i
  unfold SourcePairedPlaneIdentification.continuousTotalElectric SourcePairedPlaneIdentification.backgroundElectric
  rw [h]
  ring

/-- The magnetic analogue. -/
theorem exterior_split_magnetic :
    SourcePairedPlaneIdentification.continuousTotalMagnetic (ShellInclusionVolume.add (shellOf q hq n r) ci)
        (Xof q hq n r) inc (fs + fi) y i =
      SourcePairedPlaneIdentification.backgroundMagnetic (shellOf q hq n r) (Xof q hq n r) inc fs y i +
        (MagneticResponse.magnetic 1 (DynamicVolume.source ci ui) y i +
          MagneticResponse.magnetic 1 (DynamicVolume.source (shellOf q hq n r)
            (shellResp q hq n r (shellDrive q hq n r ci ui))) y i) := by
  obtain ⟨_, hsrc⟩ := block_facts q hq n r ci b hb hci hE fs fi hfi hfs ui hui
  have hcsX := shell_support_X q hq n r
  have hciX := incl_support_X q hq n r ci b hb hci
  have h := magnetic_split3 (Xof q hq n r) y hy _ _ _ _ hsrc
    (fun j => DynamicVolume.source_integrable _ _ _ hcsX j) (fun j => DynamicVolume.source_integrable _ _ _ hcsX j)
    (fun j => DynamicVolume.source_integrable _ _ _ hciX j)
    (fun j z hz => DynamicVolume.source_zero _ _ _ hcsX j z hz)
    (fun j z hz => DynamicVolume.source_zero _ _ _ hcsX j z hz)
    (fun j z hz => DynamicVolume.source_zero _ _ _ hciX j z hz) i
  unfold SourcePairedPlaneIdentification.continuousTotalMagnetic SourcePairedPlaneIdentification.backgroundMagnetic
  rw [h]
  ring

end ExteriorSplit

/-! ### The physical fields, the core fields and the radiated series -/

section Fields

variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
  (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (x : Vec)

/-- The physical `L2` total electric field of the combined shell-plus-inclusion solution for the input `x`. -/
abbrev physE : Maxwell.Field :=
  MaterialField.total (ShellInclusionVolume.add (shellOf q hq n r) ci) 1
    (RestrictedTEActualCore.coreSol q hq n r ci dci x) (RestrictedTEPlaneLocal.electric x)

/-- Its continuous exterior representative (valid outside the outer shell radius). -/
abbrev extE : Maxwell.Field :=
  ExteriorMaterial.total (ShellInclusionVolume.add (shellOf q hq n r) ci) 1 (Xof q hq n r)
    (RestrictedTEActualCore.coreSol q hq n r ci dci x) (RestrictedTEPlaneLocal.electric x)

/-- The pointwise total magnetic field of the combined solution. -/
abbrev physH : Maxwell.Field :=
  MaterialMaxwell.totalMagnetic (ShellInclusionVolume.add (shellOf q hq n r) ci) 1
    (RestrictedTEActualCore.coreSol q hq n r ci dci x) (RestrictedTEPlaneLocal.magnetic x)

/-- The space version of the core electric field: `coreE x ξ = coreEField x (planePoint ξ)`. -/
abbrev coreEField : Maxwell.Field :=
  SourcePairedPlaneIdentification.continuousTotalElectric (ShellInclusionVolume.add (shellOf q hq n r) ci)
    (Xof q hq n r) (RestrictedTEPlaneLocal.electric x)
    (RestrictedTEActualCore.fsLin q hq n r x + RestrictedTEActualCore.fiLin ci dci x)

/-- The space version of the core magnetic field: `coreH x ξ = coreHField x (planePoint ξ)`. -/
abbrev coreHField : Maxwell.Field :=
  SourcePairedPlaneIdentification.continuousTotalMagnetic (ShellInclusionVolume.add (shellOf q hq n r) ci)
    (Xof q hq n r) (RestrictedTEPlaneLocal.magnetic x)
    (RestrictedTEActualCore.fsLin q hq n r x + RestrictedTEActualCore.fiLin ci dci x)

theorem coreE_eq_field (ξ : PlaneInverseCube.Plane) :
    RestrictedTEActualCore.coreE q hq n r ci dci x ξ =
      coreEField q hq n r ci dci x (MaxwellPlaneTail.planePoint ξ) :=
  rfl

theorem coreH_eq_field (ξ : PlaneInverseCube.Plane) :
    RestrictedTEActualCore.coreH q hq n r ci dci x ξ =
      coreHField q hq n r ci dci x (MaxwellPlaneTail.planePoint ξ) :=
  rfl

/-- The inclusion source densities along the shell index: the weighted sources of the inclusion parts
`inclSolution` of the combined solutions (these are the moments of the radiated series). -/
def radCoeff : ℕ → Fin 3 → Maxwell.Space → ℂ :=
  fun s j => DynamicVolume.source ci (RestrictedTEActualPiecewise.inclSolution q hq n s ci dci b x) j

/-- The radiated electric series at shell index `r`: the all-degree layered TM and TE mode series with the moments
of the inclusion source of the inclusion part. -/
def radiatedE : Maxwell.Field := fun y =>
  SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q (zero_lt_one.trans_le hq) n)
    SourceRadiatedFlux.tmFlag SourceRadiatedFlux.polyFam
    (SourceRadiatedFlux.coeffFam (radCoeff q hq n ci dci b x)) r y

/-- The radiated magnetic series at shell index `r`. -/
def radiatedH : Maxwell.Field := fun y =>
  SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q (zero_lt_one.trans_le hq) n)
    SourceRadiatedFlux.tmFlag SourceRadiatedFlux.polyFam
    (SourceRadiatedFlux.coeffFam (radCoeff q hq n ci dci b x)) r y

/-- **The space version of the piecewise electric field**: the core field `coreEField` on the open core
`‖y‖ < R_r`, and the TE background plus the radiated series beyond. -/
def spaceFieldE : Maxwell.Field := fun y =>
  if ‖y‖ < Rof q hq n r then coreEField q hq n r ci dci x y
  else RestrictedTEActualPiecewise.bgFieldE q hq n r x y + radiatedE q hq n r ci dci b x y

/-- The space version of the piecewise magnetic field. -/
def spaceFieldH : Maxwell.Field := fun y =>
  if ‖y‖ < Rof q hq n r then coreHField q hq n r ci dci x y
  else RestrictedTEActualPiecewise.bgFieldH q hq n r x y + radiatedH q hq n r ci dci b x y

end Fields

/-! ### The core -/

theorem gap_of_not_mem_closure {S : Set Maxwell.Space} {y : Maxwell.Space} (h : y ∉ closure S) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ S, ε ≤ ‖y - z‖ := by
  by_contra hc
  push_neg at hc
  apply h
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨z, hz, hlt⟩ := hc ε hε
  exact ⟨z, hz, by rwa [dist_eq_norm]⟩

/-- The two vanishing conditions on the data of the shell and the inclusion. -/
theorem datum_zero (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : b < Rof q hq n r)
    (hci : ∀ y : Maxwell.Space, y ∉ closedBall (0 : Maxwell.Space) b →
      ci.value (VectorFourier.coordinateMap y) = 0) (x : Vec) :
    StaticCoefficient.sqrtMultiplier ci (RestrictedTEActualCore.fsLin q hq n r x) = 0 ∧
      StaticCoefficient.sqrtMultiplier (shellOf q hq n r) (RestrictedTEActualCore.fiLin ci dci x) = 0 := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hb.le hci
  exact ⟨SourcePairedPlaneIdentification.sqrtMultiplier_isDatum_zero ci (shellOf q hq n r) hd.symm
      (RestrictedTEPlaneLocal.electric x) _ (RestrictedTEActualCore.fs_isDatum q hq n r x),
    SourcePairedPlaneIdentification.sqrtMultiplier_isDatum_zero (shellOf q hq n r) ci hd
      (RestrictedTEPlaneLocal.electric x) _ (RestrictedTEActualCore.fi_isDatum ci dci x)⟩

/-- **Core identification, electric.**  On the open core, off the closure of the carrier, the `L2` total electric
field of the combined solution is the core field `coreE` (in its space version), almost everywhere. -/
theorem core_identification_electric (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : b < Rof q hq n r)
    (hci : ∀ y : Maxwell.Space, y ∉ closedBall (0 : Maxwell.Space) b →
      ci.value (VectorFourier.coordinateMap y) = 0)
    (hE : IsUnit (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)) (x : Vec) :
    ∀ᵐ y : Maxwell.Space, ‖y‖ < Rof q hq n r → y ∉ closure dci.carrier → ∀ i : Fin 3,
      physE q hq n r ci dci x y i = coreEField q hq n r ci dci x y i := by
  obtain ⟨hfs0, hfi0⟩ := datum_zero q hq n r ci dci b hb hci x
  have h := ExteriorMaterialOffCarrier.combined_total_electric_ae_off_carrier q hq n r ci b hb hci dci hE
    (RestrictedTEPlaneLocal.electric x) (RestrictedTEActualCore.fsLin q hq n r x)
    (RestrictedTEActualCore.fiLin ci dci x) hfi0 hfs0
  filter_upwards [h] with y hy hyR hyK i
  obtain ⟨ε, hε, hxη⟩ := gap_of_not_mem_closure hyK
  refine (hy hyR hyK i).trans ?_
  exact (SourcePairedPlaneIdentification.combined_total_electric_eq q hq n r ci b hb hci dci hE
    (RestrictedTEPlaneLocal.electric x) _ _ hfi0 hfs0 ε hε y hyR hxη i).symm

/-- **Core identification, magnetic.**  The pointwise total magnetic field of the combined solution is the core
field `coreH` at every point (the two are the same expression), in particular at every plane point. -/
theorem core_identification_magnetic (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (x : Vec) :
    (∀ (y : Maxwell.Space) (i : Fin 3), physH q hq n r ci dci x y i = coreHField q hq n r ci dci x y i) ∧
    ∀ (ξ : PlaneInverseCube.Plane) (i : Fin 3), physH q hq n r ci dci x (MaxwellPlaneTail.planePoint ξ) i =
      RestrictedTEActualCore.coreH q hq n r ci dci x ξ i :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Outside the outer shell radius the continuous exterior representative is the continuous total field. -/
theorem extE_eq_coreEField (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (x : Vec) (y : Maxwell.Space) (hy : Xof q hq n r < ‖y‖)
    (i : Fin 3) : extE q hq n r ci dci x y i = coreEField q hq n r ci dci x y i := by
  unfold extE coreEField ExteriorMaterial.total SourcePairedPlaneIdentification.continuousTotalElectric
  rw [ExteriorMaterial.scattered_exterior _ 1 _ _ y hy i]
  rfl

/-! ### Bounded inclusion solutions and the truncated sequence -/

/-- For a fixed input, the inclusion solutions are bounded for large shell index when the limiting effective block is
a unit. -/
theorem inclSolution_bounded (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb0 : 0 < b)
    (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b)
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci dci b hb0)) (x : Vec) :
    ∃ (N : ℝ) (r0 : ℕ), 0 ≤ N ∧
      ∀ r ≥ r0, ‖RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x‖ ≤ N := by
  obtain ⟨U, r0, h⟩ := RestrictedTEActualPiecewise.solution_bounded_of_coeffs q hq n ci dci b hb0 hcar hL
    (κ := Unit) (fun _ => x)
  refine ⟨max U 0, r0, le_max_right _ _, fun r hr => ?_⟩
  have := h r hr (fun _ => 1) (fun _ => by simp)
  simp only [one_smul, Finset.univ_unique, Finset.sum_singleton] at this
  exact this.trans (le_max_left _ _)

/-- The inclusion solutions, cut off to zero where their norm exceeds `N`. -/
def vSeq (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (x : Vec) (N : ℝ) : ℕ → VectorL2 := fun s =>
  if ‖RestrictedTEActualPiecewise.inclSolution q hq n s ci dci b x‖ ≤ N then
    RestrictedTEActualPiecewise.inclSolution q hq n s ci dci b x else 0

theorem vSeq_norm_le (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (x : Vec) (N : ℝ) (hN : 0 ≤ N) (s : ℕ) :
    ‖vSeq q hq n ci dci b x N s‖ ≤ N := by
  unfold vSeq
  split_ifs with h
  · exact h
  · simpa using hN

theorem vSeq_eq (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (x : Vec) (N : ℝ) (s : ℕ)
    (h : ‖RestrictedTEActualPiecewise.inclSolution q hq n s ci dci b x‖ ≤ N) :
    vSeq q hq n ci dci b x N s = RestrictedTEActualPiecewise.inclSolution q hq n s ci dci b x :=
  if_pos h

theorem coeffFam_congr (ρ ρ' : ℕ → Fin 3 → Maxwell.Space → ℂ) (s : ℕ) (h : ρ s = ρ' s) :
    SourceRadiatedFlux.coeffFam ρ s = SourceRadiatedFlux.coeffFam ρ' s := by
  funext k
  cases k <;> simp [SourceRadiatedFlux.coeffFam, h]

/-! ### The exterior -/

/-- **Exterior identification.**  For a fixed input `x` and gain index `n`, for all large shell index `r` and every
point `y` outside the outer shell radius, the continuous exterior representative of the electric total field is the
TE background electric field plus the radiated electric series, and the total magnetic field is the TE background
magnetic field plus the radiated magnetic series. -/
theorem exterior_identification (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb0 : 0 < b)
    (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b)
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci dci b hb0)) (x : Vec) :
    ∀ᶠ r : ℕ in atTop, ∀ y : Maxwell.Space, Xof q hq n r < ‖y‖ → ∀ i : Fin 3,
      extE q hq n r ci dci x y i =
        RestrictedTEActualPiecewise.bgFieldE q hq n r x y i + radiatedE q hq n r ci dci b x y i ∧
      physH q hq n r ci dci x y i =
        RestrictedTEActualPiecewise.bgFieldH q hq n r x y i + radiatedH q hq n r ci dci b x y i := by
  have hci := SourcePairedReduction.inclusion_vanish ci dci b hcar
  obtain ⟨N, r0, hN0, hbd⟩ := inclSolution_bounded q hq n ci dci b hb0 hcar hL x
  set B : ℝ := max (HarmonicSpatialMajorant.degreeScale 2 b) 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B := le_max_left _ _
  set M : ℝ := 3 * ((Real.sqrt ci.bound * Real.sqrt (volume.real (closedBall (0 : Maxwell.Space) b))) * N)
    with hMdef
  have hmass : ∀ s, SourceRadiatedSeries.mass
      (fun j => DynamicVolume.source ci (vSeq q hq n ci dci b x N s) j) ≤ M := fun s =>
    (SourceRadiatedFlux.mass_le_norm ci b hci (vSeq q hq n ci dci b x N s)).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (vSeq_norm_le q hq n ci dci b x N hN0 s)
        (by positivity)) (by norm_num))
  have hrad := SourceRadiatedFlux.paired_radiated_series_outside q hq n ci b B (B + 1) M hb0.le hB0 hscale
    (by linarith) (by linarith) (vSeq q hq n ci dci b x N) hci hmass
  filter_upwards [hrad, eventually_ge_atTop r0, SourcePairedReduction.eventually_inner_radius q hq n b,
    SourcePairedReduction.eventually_effective_isUnit q hq n ci dci b hb0 hcar hL]
    with r hr hr0 hbr hEr
  intro y hy i
  have hv := vSeq_eq q hq n ci dci b x N r (hbd r hr0)
  obtain ⟨hE1, hH1⟩ := hr y hy i
  rw [hv] at hE1 hH1
  obtain ⟨hfs0, hfi0⟩ := datum_zero q hq n r ci dci b hbr hci x
  have hρ : (fun (s : ℕ) (j : Fin 3) => DynamicVolume.source ci (vSeq q hq n ci dci b x N s) j) r =
      radCoeff q hq n ci dci b x r := by
    funext j
    show DynamicVolume.source ci (vSeq q hq n ci dci b x N r) j = _
    rw [hv]
    rfl
  have hy0 : y ≠ 0 := SourceRadiatedMagnetic.exterior_ne_zero (SourcePairedInclusion.data q hq n r) y hy
  constructor
  · rw [extE_eq_coreEField q hq n r ci dci x y hy i]
    have hs := exterior_split_electric q hq n r ci b hbr hci hEr (RestrictedTEPlaneLocal.electric x)
      (RestrictedTEActualCore.fsLin q hq n r x) (RestrictedTEActualCore.fiLin ci dci x) hfi0 hfs0
      (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x) rfl y hy i
    refine hs.trans ?_
    have hbg := congrFun (RestrictedTEBackgroundOutside.backgroundElectric_eq_bgFieldE_exterior q hq n r x y hy) i
    rw [hbg]
    congr 1
    refine hE1.trans ?_
    unfold radiatedE SourceRadiatedFlux.genElectric
    rw [coeffFam_congr _ _ r hρ]
  · have hs := exterior_split_magnetic q hq n r ci b hbr hci hEr (RestrictedTEPlaneLocal.magnetic x)
      (RestrictedTEActualCore.fsLin q hq n r x) (RestrictedTEActualCore.fiLin ci dci x) hfi0 hfs0
      (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x) rfl y hy i
    refine hs.trans ?_
    have hbg := congrFun (RestrictedTEBackgroundOutside.backgroundMagnetic_eq_bgFieldH q hq n r x y hy0) i
    rw [hbg]
    congr 1
    refine hH1.trans ?_
    unfold radiatedH SourceRadiatedFlux.genMagnetic
    rw [coeffFam_congr _ _ r hρ]

/-! ### Almost everywhere splittings on the ball containing the sources -/

theorem response_split3_of_integrable (K : Maxwell.Space → ℂ) (y : Maxwell.Space)
    (ρ ρ1 ρ2 ρ3 : Maxwell.Space → ℂ) (h : ρ =ᵐ[volume] fun z => ρ1 z + ρ2 z + ρ3 z)
    (a1 : Integrable (fun z => ρ1 z * K (y - z)) volume) (a2 : Integrable (fun z => ρ2 z * K (y - z)) volume)
    (a3 : Integrable (fun z => ρ3 z * K (y - z)) volume) :
    KernelConvolution.response K ρ y = KernelConvolution.response K ρ1 y +
      KernelConvolution.response K ρ2 y + KernelConvolution.response K ρ3 y := by
  have a12 : Integrable (fun z => ρ1 z * K (y - z) + ρ2 z * K (y - z)) volume := a1.add a2
  unfold KernelConvolution.response
  rw [← integral_add a1 a2, ← integral_add a12 a3]
  apply integral_congr_ae
  filter_upwards [h] with z hz
  rw [hz]
  ring

/-- For a locally integrable kernel and an integrable source supported in a ball, the product of the source with the
translated kernel is integrable for almost every point of any ball. -/
theorem response_integrable_ae (K : Maxwell.Space → ℂ) (hK : LocallyIntegrable K volume)
    (ρ : Maxwell.Space → ℂ) (hρ : Integrable ρ volume) (R S : ℝ)
    (hc : ∀ z, z ∉ closedBall (0 : Maxwell.Space) S → ρ z = 0) :
    ∀ᵐ y ∂(volume : Measure Maxwell.Space), y ∈ closedBall (0 : Maxwell.Space) R →
      Integrable (fun z => ρ z * K (y - z)) volume := by
  have h := hρ.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ)
    (LocalConvolution.kernel_integrable K hK (R + S))
  filter_upwards [h] with y hy hyb
  apply hy.congr
  filter_upwards with z
  exact LocalConvolution.kernel_source_eq K ρ R S hc y z hyb

theorem magnetic_split3_ae (X : ℝ) (ρ ρ1 ρ2 ρ3 : Fin 3 → Maxwell.Space → ℂ)
    (h : ∀ j, ρ j =ᵐ[volume] fun z => ρ1 j z + ρ2 j z + ρ3 j z)
    (i1 : ∀ j, Integrable (ρ1 j) volume) (i2 : ∀ j, Integrable (ρ2 j) volume)
    (i3 : ∀ j, Integrable (ρ3 j) volume)
    (z1 : ∀ j z, z ∉ closedBall (0 : Maxwell.Space) X → ρ1 j z = 0)
    (z2 : ∀ j z, z ∉ closedBall (0 : Maxwell.Space) X → ρ2 j z = 0)
    (z3 : ∀ j z, z ∉ closedBall (0 : Maxwell.Space) X → ρ3 j z = 0) :
    ∀ᵐ y ∂(volume : Measure Maxwell.Space), y ∈ closedBall (0 : Maxwell.Space) X → ∀ i : Fin 3,
      MagneticResponse.magnetic 1 ρ y i = MagneticResponse.magnetic 1 ρ1 y i +
        MagneticResponse.magnetic 1 ρ2 y i + MagneticResponse.magnetic 1 ρ3 y i := by
  have hk (l : Fin 3) : LocallyIntegrable (fun w => GreenKernel.phiGradient 1 w l) volume :=
    KernelGradient.gradient_locallyIntegrable 1 l
  have e1 : ∀ᵐ y ∂(volume : Measure Maxwell.Space), ∀ j l : Fin 3, y ∈ closedBall (0 : Maxwell.Space) X →
      Integrable (fun z => ρ1 j z * GreenKernel.phiGradient 1 (y - z) l) volume :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun l =>
      response_integrable_ae _ (hk l) (ρ1 j) (i1 j) X X (z1 j)
  have e2 : ∀ᵐ y ∂(volume : Measure Maxwell.Space), ∀ j l : Fin 3, y ∈ closedBall (0 : Maxwell.Space) X →
      Integrable (fun z => ρ2 j z * GreenKernel.phiGradient 1 (y - z) l) volume :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun l =>
      response_integrable_ae _ (hk l) (ρ2 j) (i2 j) X X (z2 j)
  have e3 : ∀ᵐ y ∂(volume : Measure Maxwell.Space), ∀ j l : Fin 3, y ∈ closedBall (0 : Maxwell.Space) X →
      Integrable (fun z => ρ3 j z * GreenKernel.phiGradient 1 (y - z) l) volume :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun l =>
      response_integrable_ae _ (hk l) (ρ3 j) (i3 j) X X (z3 j)
  filter_upwards [e1, e2, e3] with y h1 h2 h3 hy i
  unfold MagneticResponse.magnetic
  rw [response_split3_of_integrable (fun w => GreenKernel.phiGradient 1 w (WeakCurl.next i)) y _ _ _ _
      (h (WeakCurl.previous i)) (h1 _ _ hy) (h2 _ _ hy) (h3 _ _ hy),
    response_split3_of_integrable (fun w => GreenKernel.phiGradient 1 w (WeakCurl.previous i)) y _ _ _ _
      (h (WeakCurl.next i)) (h1 _ _ hy) (h2 _ _ hy) (h3 _ _ hy)]
  ring

/-- **Splitting of the `L2` scattered field.**  If the weighted vector, the weighted source of a combined solution
split into three parts supported in a ball, the scattered field splits into the three scattered fields, almost
everywhere on the ball. -/
theorem scattered_split3_ae (X : ℝ) (c c1 c2 c3 : StaticCoefficient.Coefficient) (u u1 u2 u3 : VectorL2)
    (hc1 : ∀ z : Maxwell.Space, z ∉ closedBall (0 : Maxwell.Space) X →
      c1.value (VectorFourier.coordinateMap z) = 0)
    (hc2 : ∀ z : Maxwell.Space, z ∉ closedBall (0 : Maxwell.Space) X →
      c2.value (VectorFourier.coordinateMap z) = 0)
    (hc3 : ∀ z : Maxwell.Space, z ∉ closedBall (0 : Maxwell.Space) X →
      c3.value (VectorFourier.coordinateMap z) = 0)
    (hF : StaticCoefficient.sqrtMultiplier c u = StaticCoefficient.sqrtMultiplier c1 u1 +
      StaticCoefficient.sqrtMultiplier c2 u2 + StaticCoefficient.sqrtMultiplier c3 u3)
    (hsrc : ∀ j, DynamicVolume.source c u j =ᵐ[volume] fun z => DynamicVolume.source c1 u1 j z +
      DynamicVolume.source c2 u2 j z + DynamicVolume.source c3 u3 j z) :
    ∀ᵐ y ∂(volume : Measure Maxwell.Space), y ∈ closedBall (0 : Maxwell.Space) X → ∀ i : Fin 3,
      MaterialField.scattered c 1 u y i = MaterialField.scattered c1 1 u1 y i +
        MaterialField.scattered c2 1 u2 y i + MaterialField.scattered c3 1 u3 y i := by
  have eR1 : ∀ᵐ y ∂(volume : Measure Maxwell.Space), ∀ i j : Fin 3, y ∈ closedBall (0 : Maxwell.Space) X →
      Integrable (fun z => DyadicKernel.remainder 1 (y - z) i j * DynamicVolume.source c1 u1 j z) volume :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => DynamicVolume.remainder_source_integrable_ae c1 u1 1 X hc1 i j
  have eR2 : ∀ᵐ y ∂(volume : Measure Maxwell.Space), ∀ i j : Fin 3, y ∈ closedBall (0 : Maxwell.Space) X →
      Integrable (fun z => DyadicKernel.remainder 1 (y - z) i j * DynamicVolume.source c2 u2 j z) volume :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => DynamicVolume.remainder_source_integrable_ae c2 u2 1 X hc2 i j
  have eR3 : ∀ᵐ y ∂(volume : Measure Maxwell.Space), ∀ i j : Fin 3, y ∈ closedBall (0 : Maxwell.Space) X →
      Integrable (fun z => DyadicKernel.remainder 1 (y - z) i j * DynamicVolume.source c3 u3 j z) volume :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => DynamicVolume.remainder_source_integrable_ae c3 u3 1 X hc3 i j
  have eN : ∀ i : Fin 3, ∀ᵐ y ∂(volume : Measure Maxwell.Space),
      (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u)) i :
        Maxwell.Space → ℂ) y =
      (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c1 u1)) i :
        Maxwell.Space → ℂ) y +
      (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c2 u2)) i :
        Maxwell.Space → ℂ) y +
      (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c3 u3)) i :
        Maxwell.Space → ℂ) y := by
    intro i
    have hP : NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u)) i =
        NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c1 u1)) i +
        NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c2 u2)) i +
        NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c3 u3)) i := by
      rw [hF, map_add, map_add, SourcePairedPlaneIdentification.physicalCoordinate_add,
        SourcePairedPlaneIdentification.physicalCoordinate_add]
    rw [hP]
    filter_upwards [Lp.coeFn_add (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
        (StaticCoefficient.sqrtMultiplier c1 u1)) i + NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
        (StaticCoefficient.sqrtMultiplier c2 u2)) i)
      (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c3 u3)) i),
      Lp.coeFn_add (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
        (StaticCoefficient.sqrtMultiplier c1 u1)) i)
      (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c2 u2)) i)]
      with y h1 h2
    rw [h1]
    simp only [Pi.add_apply]
    rw [h2]
    simp only [Pi.add_apply]
  have eN0 := ae_all_iff.mpr eN
  filter_upwards [eR1, eR2, eR3, eN0] with y h1 h2 h3 h4 hy i
  unfold MaterialField.scattered FieldResponse.electric
  have hsum : ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.remainder 1 z i j)
      (DynamicVolume.source c u j) y =
      (∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.remainder 1 z i j)
        (DynamicVolume.source c1 u1 j) y) +
      (∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.remainder 1 z i j)
        (DynamicVolume.source c2 u2 j) y) +
      (∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.remainder 1 z i j)
        (DynamicVolume.source c3 u3 j) y) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => response_split3_of_integrable _ y _ _ _ _ (hsrc j) ?_ ?_ ?_)
    · simpa only [mul_comm] using h1 i j hy
    · simpa only [mul_comm] using h2 i j hy
    · simpa only [mul_comm] using h3 i j hy
  rw [hsum, h4 i]
  ring

/-! ### The shell annulus -/

/-- **Annulus identification, electric.**  For a fixed input and gain index, for all large shell index, almost
everywhere on the shell annulus `R_r < ‖y‖ ≤ X_r` the `L2` total electric field of the combined solution is the TE
background electric field plus the radiated electric series.  (The shell part is the `L2` shell response of the
shell datum, identified with the TE background by `famBackground_ae`; the rest is the annulus identification of the
radiated field, `paired_annulus_electric_ae`.) -/
theorem annulus_identification_electric (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb0 : 0 < b)
    (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b)
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci dci b hb0)) (x : Vec) :
    ∀ᶠ r : ℕ in atTop, ∀ᵐ y ∂(volume : Measure Maxwell.Space), Rof q hq n r < ‖y‖ → ‖y‖ ≤ Xof q hq n r →
      ∀ i : Fin 3, physE q hq n r ci dci x y i =
        RestrictedTEActualPiecewise.bgFieldE q hq n r x y i + radiatedE q hq n r ci dci b x y i := by
  have hci := SourcePairedReduction.inclusion_vanish ci dci b hcar
  obtain ⟨N, r0, hN0, hbd⟩ := inclSolution_bounded q hq n ci dci b hb0 hcar hL x
  set B : ℝ := max (HarmonicSpatialMajorant.degreeScale 2 b) 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B := le_max_left _ _
  have hrad := SourceRadiatedAnnulus.paired_annulus_electric_ae q hq n ci b B (B + 1) N hb0.le hB0 hscale
    (by linarith) (by linarith) (vSeq q hq n ci dci b x N) hci (vSeq_norm_le q hq n ci dci b x N hN0)
  filter_upwards [hrad, eventually_ge_atTop r0, SourcePairedReduction.eventually_inner_radius q hq n b,
    SourcePairedReduction.eventually_effective_isUnit q hq n ci dci b hb0 hcar hL]
    with r hr hr0 hbr hEr
  have hv := vSeq_eq q hq n ci dci b x N r (hbd r hr0)
  obtain ⟨hfs0, hfi0⟩ := datum_zero q hq n r ci dci b hbr hci x
  obtain ⟨hF, hsrc⟩ := block_facts q hq n r ci b hbr hci hEr (RestrictedTEActualCore.fsLin q hq n r x)
    (RestrictedTEActualCore.fiLin ci dci x) hfi0 hfs0
    (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x) rfl
  have hcsX := shell_support_X q hq n r
  have hciX := incl_support_X q hq n r ci b hbr hci
  have hcore := scattered_split3_ae (Xof q hq n r) (ShellInclusionVolume.add (shellOf q hq n r) ci)
    (shellOf q hq n r) (shellOf q hq n r) ci _ _ _ _ hcsX hcsX hciX hF hsrc
  have hext := ExteriorContinuity.electric_ae_exterior 1
    (StaticCoefficient.sqrtMultiplier ci (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x))
    (DynamicVolume.source ci (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x))
    (fun j => DynamicVolume.source_integrable _ _ _ hci j)
    (StaticNewton.material_source_ae ci _) b (fun j z hz => DynamicVolume.source_zero _ _ _ hci j z hz)
  have hshell := RestrictedTEBackgroundOutside.famBackground_ae q hq n r x
  have hρ : (fun (s : ℕ) (j : Fin 3) => DynamicVolume.source ci (vSeq q hq n ci dci b x N s) j) r =
      radCoeff q hq n ci dci b x r := by
    funext j
    show DynamicVolume.source ci (vSeq q hq n ci dci b x N r) j = _
    rw [hv]
    rfl
  filter_upwards [hcore, hext, hshell, hr] with y h1 h2 h3 h4 hRy hXy i
  have hyb : b < ‖y‖ := hbr.trans hRy
  have h1' := h1 (mem_closedBall_zero_iff.mpr hXy) i
  have h2' : MaterialField.scattered ci 1
      (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x) y i =
      ExteriorContinuity.electric 1 (DynamicVolume.source ci
        (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x)) y i := congrFun (h2 hyb) i
  have h3' := congrFun h3 i
  have h4' := h4 hRy i
  rw [hv] at h4'
  have hg : SourceRadiatedFlux.genElectric (SourceRadiatedFlux.dataFam q (zero_lt_one.trans_le hq) n)
      SourceRadiatedFlux.tmFlag SourceRadiatedFlux.polyFam
      (SourceRadiatedFlux.coeffFam (fun s j => DynamicVolume.source ci (vSeq q hq n ci dci b x N s) j)) r y i =
      radiatedE q hq n r ci dci b x y i := by
    unfold radiatedE SourceRadiatedFlux.genElectric
    rw [coeffFam_congr _ _ r hρ]
  have e0 : physE q hq n r ci dci x y i = RestrictedTEPlaneLocal.electric x y i +
      MaterialField.scattered (ShellInclusionVolume.add (shellOf q hq n r) ci) 1
        (MaterialField.solution (ShellInclusionVolume.add (shellOf q hq n r) ci) 1 (Xof q hq n r)
          (RestrictedTEActualCore.fsLin q hq n r x + RestrictedTEActualCore.fiLin ci dci x)) y i := rfl
  have e1 : MaterialField.total (shellOf q hq n r) 1 (RestrictedTEBackgroundOutside.shellSol q hq n r x)
      (RestrictedTEPlaneLocal.electric x) y i = RestrictedTEPlaneLocal.electric x y i +
      MaterialField.scattered (shellOf q hq n r) 1 (shellResp q hq n r (RestrictedTEActualCore.fsLin q hq n r x))
        y i := rfl
  have hbgE : RestrictedTEPlaneLocal.electric x y i +
      MaterialField.scattered (shellOf q hq n r) 1 (shellResp q hq n r (RestrictedTEActualCore.fsLin q hq n r x))
        y i = RestrictedTEActualPiecewise.bgFieldE q hq n r x y i := e1.symm.trans h3'
  have hgen : MaterialField.scattered (shellOf q hq n r) 1
      (shellResp q hq n r (shellDrive q hq n r ci (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x)))
        y i + ExteriorContinuity.electric 1 (DynamicVolume.source ci
          (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x)) y i =
      radiatedE q hq n r ci dci b x y i := h4'.trans hg
  rw [e0, h1', h2']
  linear_combination hbgE + hgen

/-- **Annulus identification, magnetic.**  Almost everywhere on the shell annulus the total magnetic field of the
combined solution is the TE background magnetic field plus the radiated magnetic series. -/
theorem annulus_identification_magnetic (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb0 : 0 < b)
    (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b)
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci dci b hb0)) (x : Vec) :
    ∀ᶠ r : ℕ in atTop, ∀ᵐ y ∂(volume : Measure Maxwell.Space), Rof q hq n r < ‖y‖ → ‖y‖ ≤ Xof q hq n r →
      ∀ i : Fin 3, physH q hq n r ci dci x y i =
        RestrictedTEActualPiecewise.bgFieldH q hq n r x y i + radiatedH q hq n r ci dci b x y i := by
  have hci := SourcePairedReduction.inclusion_vanish ci dci b hcar
  obtain ⟨N, r0, hN0, hbd⟩ := inclSolution_bounded q hq n ci dci b hb0 hcar hL x
  set B : ℝ := max (HarmonicSpatialMajorant.degreeScale 2 b) 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hscale : HarmonicSpatialMajorant.degreeScale 2 b ≤ B := le_max_left _ _
  have hrad := SourceRadiatedAnnulus.paired_annulus_magnetic_ae q hq n ci b B (B + 1) N hb0.le hB0 hscale
    (by linarith) (by linarith) (vSeq q hq n ci dci b x N) hci (vSeq_norm_le q hq n ci dci b x N hN0)
  filter_upwards [hrad, eventually_ge_atTop r0, SourcePairedReduction.eventually_inner_radius q hq n b,
    SourcePairedReduction.eventually_effective_isUnit q hq n ci dci b hb0 hcar hL]
    with r hr hr0 hbr hEr
  have hv := vSeq_eq q hq n ci dci b x N r (hbd r hr0)
  obtain ⟨hfs0, hfi0⟩ := datum_zero q hq n r ci dci b hbr hci x
  obtain ⟨_, hsrc⟩ := block_facts q hq n r ci b hbr hci hEr (RestrictedTEActualCore.fsLin q hq n r x)
    (RestrictedTEActualCore.fiLin ci dci x) hfi0 hfs0
    (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x) rfl
  have hcsX := shell_support_X q hq n r
  have hciX := incl_support_X q hq n r ci b hbr hci
  have hcore := magnetic_split3_ae (Xof q hq n r) _ _ _ _ hsrc
    (fun j => DynamicVolume.source_integrable _ _ _ hcsX j) (fun j => DynamicVolume.source_integrable _ _ _ hcsX j)
    (fun j => DynamicVolume.source_integrable _ _ _ hciX j)
    (fun j z hz => DynamicVolume.source_zero _ _ _ hcsX j z hz)
    (fun j z hz => DynamicVolume.source_zero _ _ _ hcsX j z hz)
    (fun j z hz => DynamicVolume.source_zero _ _ _ hciX j z hz)
  have hρ : (fun (s : ℕ) (j : Fin 3) => DynamicVolume.source ci (vSeq q hq n ci dci b x N s) j) r =
      radCoeff q hq n ci dci b x r := by
    funext j
    show DynamicVolume.source ci (vSeq q hq n ci dci b x N r) j = _
    rw [hv]
    rfl
  filter_upwards [hcore, hr] with y h1 h4 hRy hXy i
  have hy0 : y ≠ 0 := norm_pos_iff.mp (lt_trans (RadialPhaseLimit.radius_pos r) hRy)
  have h1' := h1 (mem_closedBall_zero_iff.mpr hXy) i
  have h4' := h4 hRy i
  rw [hv] at h4'
  have hg : SourceRadiatedFlux.genMagnetic (SourceRadiatedFlux.dataFam q (zero_lt_one.trans_le hq) n)
      SourceRadiatedFlux.tmFlag SourceRadiatedFlux.polyFam
      (SourceRadiatedFlux.coeffFam (fun s j => DynamicVolume.source ci (vSeq q hq n ci dci b x N s) j)) r y i =
      radiatedH q hq n r ci dci b x y i := by
    unfold radiatedH SourceRadiatedFlux.genMagnetic
    rw [coeffFam_congr _ _ r hρ]
  have hbg := congrFun (RestrictedTEBackgroundOutside.backgroundMagnetic_eq_bgFieldH q hq n r x y hy0) i
  have e0 : physH q hq n r ci dci x y i = RestrictedTEPlaneLocal.magnetic x y i +
      MagneticResponse.magnetic 1 (DynamicVolume.source (ShellInclusionVolume.add (shellOf q hq n r) ci)
        (MaterialField.solution (ShellInclusionVolume.add (shellOf q hq n r) ci) 1 (Xof q hq n r)
          (RestrictedTEActualCore.fsLin q hq n r x + RestrictedTEActualCore.fiLin ci dci x))) y i := rfl
  have e1 : SourcePairedPlaneIdentification.backgroundMagnetic (shellOf q hq n r) (Xof q hq n r)
      (RestrictedTEPlaneLocal.magnetic x) (RestrictedTEActualCore.fsLin q hq n r x) y i =
      RestrictedTEPlaneLocal.magnetic x y i + MagneticResponse.magnetic 1
        (DynamicVolume.source (shellOf q hq n r) (shellResp q hq n r (RestrictedTEActualCore.fsLin q hq n r x)))
        y i := rfl
  have hbgH : RestrictedTEPlaneLocal.magnetic x y i + MagneticResponse.magnetic 1
        (DynamicVolume.source (shellOf q hq n r) (shellResp q hq n r (RestrictedTEActualCore.fsLin q hq n r x)))
        y i = RestrictedTEActualPiecewise.bgFieldH q hq n r x y i := e1.symm.trans hbg
  have hgen : MagneticResponse.magnetic 1 (DynamicVolume.source (shellOf q hq n r)
      (shellResp q hq n r (shellDrive q hq n r ci (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x))))
        y i + MagneticResponse.magnetic 1 (DynamicVolume.source ci
          (RestrictedTEActualPiecewise.inclSolution q hq n r ci dci b x)) y i =
      radiatedH q hq n r ci dci b x y i := h4'.trans hg
  rw [e0, h1']
  linear_combination hbgH + hgen

/-! ### The physical fields are the space versions of the piecewise fields -/

theorem add_support_X (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient) (b : ℝ)
    (hb : b < Rof q hq n r)
    (hci : ∀ y : Maxwell.Space, y ∉ closedBall (0 : Maxwell.Space) b →
      ci.value (VectorFourier.coordinateMap y) = 0) :
    ∀ z : Maxwell.Space, z ∉ closedBall (0 : Maxwell.Space) (Xof q hq n r) →
      (ShellInclusionVolume.add (shellOf q hq n r) ci).value (VectorFourier.coordinateMap z) = 0 := by
  intro z hz
  change (shellOf q hq n r).value (VectorFourier.coordinateMap z) + ci.value (VectorFourier.coordinateMap z) = 0
  rw [shell_support_X q hq n r z hz, incl_support_X q hq n r ci b hb hci z hz, add_zero]

/-- The region on which the electric `L2` total field is identified: the open core off the closure of the carrier,
together with everything beyond the inner shell radius. -/
def physRegion (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) {ci : StaticCoefficient.Coefficient}
    (dci : BoundedMaterialKernel.SupportData ci) : Set Maxwell.Space :=
  {y | (‖y‖ < Rof q hq n r ∧ y ∉ closure dci.carrier) ∨ Rof q hq n r < ‖y‖}

theorem measurableSet_physRegion (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) {ci : StaticCoefficient.Coefficient}
    (dci : BoundedMaterialKernel.SupportData ci) : MeasurableSet (physRegion q hq n r dci) :=
  ((measurableSet_lt measurable_norm measurable_const).inter isClosed_closure.measurableSet.compl).union
    (measurableSet_lt measurable_const measurable_norm)

section SpaceFields

variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
  (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (x : Vec) (y : Maxwell.Space) (i : Fin 3)

theorem spaceFieldE_core (hy : ‖y‖ < Rof q hq n r) :
    spaceFieldE q hq n r ci dci b x y i = coreEField q hq n r ci dci x y i := by
  unfold spaceFieldE
  rw [if_pos hy]

theorem spaceFieldE_out (hy : Rof q hq n r ≤ ‖y‖) :
    spaceFieldE q hq n r ci dci b x y i = RestrictedTEActualPiecewise.bgFieldE q hq n r x y i +
      radiatedE q hq n r ci dci b x y i := by
  unfold spaceFieldE
  rw [if_neg (not_lt.mpr hy)]
  rfl

theorem spaceFieldH_core (hy : ‖y‖ < Rof q hq n r) :
    spaceFieldH q hq n r ci dci b x y i = coreHField q hq n r ci dci x y i := by
  unfold spaceFieldH
  rw [if_pos hy]

theorem spaceFieldH_out (hy : Rof q hq n r ≤ ‖y‖) :
    spaceFieldH q hq n r ci dci b x y i = RestrictedTEActualPiecewise.bgFieldH q hq n r x y i +
      radiatedH q hq n r ci dci b x y i := by
  unfold spaceFieldH
  rw [if_neg (not_lt.mpr hy)]
  rfl

end SpaceFields

/-- **Physical identification, electric.**  For a fixed input `x` and gain index `n` with unit limiting effective
block, for all large shell index `r` the `L2` total electric field of the combined solution equals the space version
of the piecewise electric field almost everywhere on the open core off the closure of the carrier, the shell annulus
and the exterior, and its continuous exterior representative equals it at every point outside the outer shell
radius. -/
theorem physical_identification_electric (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb0 : 0 < b)
    (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b)
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci dci b hb0)) (x : Vec) :
    ∀ᶠ r : ℕ in atTop,
      (∀ i : Fin 3, (fun y => physE q hq n r ci dci x y i) =ᵐ[volume.restrict (physRegion q hq n r dci)]
          fun y => spaceFieldE q hq n r ci dci b x y i) ∧
      ∀ y : Maxwell.Space, Xof q hq n r < ‖y‖ → ∀ i : Fin 3,
        extE q hq n r ci dci x y i = spaceFieldE q hq n r ci dci b x y i := by
  have hci := SourcePairedReduction.inclusion_vanish ci dci b hcar
  filter_upwards [annulus_identification_electric q hq n ci dci b hb0 hcar hL x,
    exterior_identification q hq n ci dci b hb0 hcar hL x, SourcePairedReduction.eventually_inner_radius q hq n b,
    SourcePairedReduction.eventually_effective_isUnit q hq n ci dci b hb0 hcar hL] with r hann hext hbr hEr
  have hRX : Rof q hq n r ≤ Xof q hq n r := SourcePairedInclusion.radii_ordered q hq n r
  refine ⟨fun i => ?_, fun y hXy i => ?_⟩
  · rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_physRegion q hq n r dci)]
    have hcore := core_identification_electric q hq n r ci dci b hbr hci hEr x
    have hL2 := ExteriorMaterial.total_ae (ShellInclusionVolume.add (shellOf q hq n r) ci) 1 (Xof q hq n r)
      (RestrictedTEActualCore.coreSol q hq n r ci dci x) (RestrictedTEPlaneLocal.electric x)
      (add_support_X q hq n r ci b hbr hci)
    filter_upwards [hcore, hann, hL2] with y h1 h2 h3 hy
    rcases hy with ⟨hyR, hyK⟩ | hRy
    · rw [h1 hyR hyK i, spaceFieldE_core q hq n r ci dci b x y i hyR]
    · by_cases hXy : ‖y‖ ≤ Xof q hq n r
      · rw [h2 hRy hXy i, spaceFieldE_out q hq n r ci dci b x y i hRy.le]
      · have hXy' : Xof q hq n r < ‖y‖ := not_le.mp hXy
        have h4 : physE q hq n r ci dci x y i = extE q hq n r ci dci x y i := (congrFun h3 i).symm
        rw [h4, (hext y hXy' i).1, spaceFieldE_out q hq n r ci dci b x y i (hRX.trans hXy'.le)]
  · rw [(hext y hXy i).1, spaceFieldE_out q hq n r ci dci b x y i (hRX.trans hXy.le)]

/-- **Physical identification, magnetic.**  For all large shell index `r` the pointwise total magnetic field of the
combined solution equals the space version of the piecewise magnetic field at every point of the open core and at
every point outside the outer shell radius, and almost everywhere in space (the shell annulus included). -/
theorem physical_identification_magnetic (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb0 : 0 < b)
    (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b)
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci dci b hb0)) (x : Vec) :
    ∀ᶠ r : ℕ in atTop,
      (∀ y : Maxwell.Space, ‖y‖ < Rof q hq n r → ∀ i : Fin 3,
        physH q hq n r ci dci x y i = spaceFieldH q hq n r ci dci b x y i) ∧
      (∀ y : Maxwell.Space, Xof q hq n r < ‖y‖ → ∀ i : Fin 3,
        physH q hq n r ci dci x y i = spaceFieldH q hq n r ci dci b x y i) ∧
      ∀ i : Fin 3, (fun y => physH q hq n r ci dci x y i) =ᵐ[volume]
        fun y => spaceFieldH q hq n r ci dci b x y i := by
  filter_upwards [annulus_identification_magnetic q hq n ci dci b hb0 hcar hL x,
    exterior_identification q hq n ci dci b hb0 hcar hL x] with r hann hext
  have hRX : Rof q hq n r ≤ Xof q hq n r := SourcePairedInclusion.radii_ordered q hq n r
  have hcore : ∀ y : Maxwell.Space, ‖y‖ < Rof q hq n r → ∀ i : Fin 3,
      physH q hq n r ci dci x y i = spaceFieldH q hq n r ci dci b x y i := fun y hy i =>
    (spaceFieldH_core q hq n r ci dci b x y i hy).symm
  have hextH : ∀ y : Maxwell.Space, Xof q hq n r < ‖y‖ → ∀ i : Fin 3,
      physH q hq n r ci dci x y i = spaceFieldH q hq n r ci dci b x y i := fun y hy i => by
    rw [(hext y hy i).2, spaceFieldH_out q hq n r ci dci b x y i (hRX.trans hy.le)]
  refine ⟨hcore, hextH, fun i => ?_⟩
  have hnull : ∀ᵐ y ∂(volume : Measure Maxwell.Space), ¬ (‖y‖ = Rof q hq n r) := by
    apply ae_iff.mpr
    have h0 : (volume : Measure Maxwell.Space) {y : Maxwell.Space | ‖y‖ = Rof q hq n r} = 0 := by
      have : {y : Maxwell.Space | ‖y‖ = Rof q hq n r} = sphere 0 (Rof q hq n r) := by
        ext u
        simp [mem_sphere_iff_norm]
      rw [this]
      exact Measure.addHaar_sphere volume 0 _
    simpa using h0
  filter_upwards [hann, hnull] with y h1 h2
  by_cases hyR : ‖y‖ < Rof q hq n r
  · exact hcore y hyR i
  · have hRy : Rof q hq n r < ‖y‖ := lt_of_le_of_ne (not_lt.mp hyR) (fun h => h2 h.symm)
    by_cases hXy : ‖y‖ ≤ Xof q hq n r
    · rw [h1 hRy hXy i, spaceFieldH_out q hq n r ci dci b x y i hRy.le]
    · exact hextH y (not_le.mp hXy) i

/-- The combined statement of the physical identification for a fixed input and gain index. -/
def PhysicallyIdentified (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (x : Vec) : Prop :=
  ((∀ i : Fin 3, (fun y => physE q hq n r ci dci x y i) =ᵐ[volume.restrict (physRegion q hq n r dci)]
      fun y => spaceFieldE q hq n r ci dci b x y i) ∧
    ∀ y : Maxwell.Space, Xof q hq n r < ‖y‖ → ∀ i : Fin 3,
      extE q hq n r ci dci x y i = spaceFieldE q hq n r ci dci b x y i) ∧
  ((∀ y : Maxwell.Space, ‖y‖ < Rof q hq n r → ∀ i : Fin 3,
      physH q hq n r ci dci x y i = spaceFieldH q hq n r ci dci b x y i) ∧
    (∀ y : Maxwell.Space, Xof q hq n r < ‖y‖ → ∀ i : Fin 3,
      physH q hq n r ci dci x y i = spaceFieldH q hq n r ci dci b x y i) ∧
    ∀ i : Fin 3, (fun y => physH q hq n r ci dci x y i) =ᵐ[volume]
      fun y => spaceFieldH q hq n r ci dci b x y i)

/-- **Physical identification.**  For a fixed input `x` and gain index `n` whose limiting effective inclusion block
is a unit, eventually in the shell index the physical fields of the combined shell-plus-inclusion device (the `L2`
total electric field with its continuous exterior representative, and the total magnetic field) are the space
versions of the piecewise fields of the assembly (core fields on the open core, TE background plus the radiated mode
series beyond), with no hypothesis on the shell annulus. -/
theorem physical_identification (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb0 : 0 < b)
    (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b)
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci dci b hb0)) (x : Vec) :
    ∀ᶠ r : ℕ in atTop, PhysicallyIdentified q hq n r ci dci b x :=
  (physical_identification_electric q hq n ci dci b hb0 hcar hL x).and
    (physical_identification_magnetic q hq n ci dci b hb0 hcar hL x)

/-! ### The concrete doubled device -/

section Device

/-- The positions of the concrete doubled device. -/
abbrev devPos {ι : Type*} (r0 : ℝ) (y : ι → ℝ) (h : ℝ) : ℝ → ι → FourierL2.Space :=
  fun a l => OQ14.RestrictedTEDipoleProfile.abovePoint (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)

/-- The inclusion coefficient of the concrete doubled device at gain index `n`. -/
abbrev devCoeff {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h : ℝ) (hχ : 0 < χ) (q : ℝ) (n : ℕ) :
    StaticCoefficient.Coefficient :=
  RestrictedTEPartnerSmallness.deviceCoeff (devPos r0 y h) ρ χ hχ.le q n

/-- The support data of the inclusion of the concrete doubled device at gain index `n`. -/
abbrev devData {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) (n : ℕ) :
    BoundedMaterialKernel.SupportData (devCoeff r0 y ρ χ h hχ q n) :=
  RestrictedTEPartnerSmallness.deviceData (devPos r0 y h) ρ χ R hρ hχ.le hi q hq n

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
  (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
    (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hρh : ρ < h)
  {q : ℝ} (hq : 1 < q) {b : ℝ} (hRb : R ≤ b) (n r : ℕ) (hbr : b < Rof q hq.le n r)
  (x : Vec) (ξ : PlaneInverseCube.Plane)
include hbr

/-- **The piecewise electric device field is the space version at plane points.**  With the outside field
`outFieldE` (TE background plus a radiated field `radE` that is the radiated series at plane points), the piecewise
device field of the assembly at the plane point `ξ` is `spaceFieldE` at `planePoint ξ`. -/
theorem deviceFieldsE_eq_space (radE : ℕ → ℕ → RestrictedTEActualPiecewise.FieldMap)
    (hrad : ∀ (x : Vec) (ξ : PlaneInverseCube.Plane), radE n r x ξ =
      radiatedE q hq.le n r (devCoeff r0 y ρ χ h hχ q n) (devData r0 y ρ χ h R hρ hχ hi q hq n) b x
        (MaxwellPlaneTail.planePoint ξ)) :
    RestrictedTEActualPiecewise.deviceFieldsE r0 y ρ χ h R hρ hχ hi hρh hq hRb
        (RestrictedTEBackgroundOutside.outFieldE q hq.le radE) n r x ξ =
      spaceFieldE q hq.le n r (devCoeff r0 y ρ χ h hχ q n) (devData r0 y ρ χ h R hρ hχ hi q hq n) b x
        (MaxwellPlaneTail.planePoint ξ) := by
  have hd := RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi
  unfold RestrictedTEActualPiecewise.deviceFieldsE
  funext i
  by_cases hξ : ‖ξ‖ < RadialPhaseLimit.radius r
  · rw [RestrictedTEActualPiecewise.piecewiseE_apply_lt (fun r => RadialPhaseLimit.radius r) _ _ n r x ξ hξ,
      RestrictedTEActualCore.deviceFieldE_apply hd hq hRb n r hbr x ξ hξ,
      spaceFieldE_core q hq.le n r _ _ b x _ i (by rw [MaxwellPlaneTail.planePoint_norm]; exact hξ)]
    rfl
  · rw [RestrictedTEActualPiecewise.piecewiseE_apply_ge (fun r => RadialPhaseLimit.radius r) _ _ n r x ξ
      (not_lt.mp hξ), spaceFieldE_out q hq.le n r _ _ b x _ i
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact not_lt.mp hξ)]
    have e : RestrictedTEBackgroundOutside.outFieldE q hq.le radE n r x ξ i =
        RestrictedTEActualPiecewise.bgFieldE q hq.le n r x (MaxwellPlaneTail.planePoint ξ) i +
          radE n r x ξ i := rfl
    rw [e, hrad x ξ]


/-- The magnetic analogue. -/
theorem deviceFieldsH_eq_space (radH : ℕ → ℕ → RestrictedTEActualPiecewise.FieldMap)
    (hrad : ∀ (x : Vec) (ξ : PlaneInverseCube.Plane), radH n r x ξ =
      radiatedH q hq.le n r (devCoeff r0 y ρ χ h hχ q n) (devData r0 y ρ χ h R hρ hχ hi q hq n) b x
        (MaxwellPlaneTail.planePoint ξ)) :
    RestrictedTEActualPiecewise.deviceFieldsH r0 y ρ χ h R hρ hχ hi hρh hq hRb
        (RestrictedTEBackgroundOutside.outFieldH q hq.le radH) n r x ξ =
      spaceFieldH q hq.le n r (devCoeff r0 y ρ χ h hχ q n) (devData r0 y ρ χ h R hρ hχ hi q hq n) b x
        (MaxwellPlaneTail.planePoint ξ) := by
  have hd := RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi
  unfold RestrictedTEActualPiecewise.deviceFieldsH
  funext i
  by_cases hξ : ‖ξ‖ < RadialPhaseLimit.radius r
  · rw [RestrictedTEActualPiecewise.piecewiseE_apply_lt (fun r => RadialPhaseLimit.radius r) _ _ n r x ξ hξ,
      RestrictedTEActualCore.deviceFieldH_apply hd hq hRb n r hbr x ξ hξ,
      spaceFieldH_core q hq.le n r _ _ b x _ i (by rw [MaxwellPlaneTail.planePoint_norm]; exact hξ)]
    rfl
  · rw [RestrictedTEActualPiecewise.piecewiseE_apply_ge (fun r => RadialPhaseLimit.radius r) _ _ n r x ξ
      (not_lt.mp hξ), spaceFieldH_out q hq.le n r _ _ b x _ i
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact not_lt.mp hξ)]
    have e : RestrictedTEBackgroundOutside.outFieldH q hq.le radH n r x ξ i =
        RestrictedTEActualPiecewise.bgFieldH q hq.le n r x (MaxwellPlaneTail.planePoint ξ) i +
          radH n r x ξ i := rfl
    rw [e, hrad x ξ]

end Device

/-- **Physical identification for the concrete doubled device.**  For all large gain index `n` (so that the limiting
effective block is a unit), every input `x` and all large shell index `r`, the physical fields of the combined
shell-plus-inclusion device with the doubled inclusion `devCoeff`, `devData` (enclosing radius `max R 1`) are the
space versions of the piecewise fields. -/
theorem device_physical_identification {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Vec, ∀ᶠ r : ℕ in atTop,
      PhysicallyIdentified q hq.le n r (devCoeff r0 y ρ χ h hχ q n) (devData r0 y ρ χ h R hρ hχ hi q hq n)
        (max R 1) x := by
  have hb0 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  filter_upwards [RestrictedTEPartnerSmallness.partner_limitEffective_isUnit (devPos r0 y h) ρ χ R (max R 1)
    hρ hχ.le hb0 (le_max_left R 1) hi q hq] with n hL
  intro x
  exact physical_identification q hq.le n _ _ (max R 1) hb0
    (RestrictedTEActualCounting.device_carrier_le (devPos r0 y h) ρ χ R (max R 1) hρ hχ.le (le_max_left R 1) hi
      q hq n) hL x

/-- **The piecewise device fields of the assembly are the physical fields.**  For the concrete doubled device, all
large gain index `n`, every input `x` and all large shell index `r`: the physical fields are identified
(`PhysicallyIdentified`), and whenever the outside radiated fields `radE`, `radH` are the radiated series at plane
points, the piecewise device fields `deviceFieldsE`, `deviceFieldsH` of the assembly (with the outside fields
`outFieldE`, `outFieldH`) are the space versions at every plane point. -/
theorem device_piecewise_identification {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ)
    (ρ χ h R : ℝ) (hρ : 0 < ρ) (hχ : 0 < χ) (hρh : ρ < h)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Vec, ∀ᶠ r : ℕ in atTop,
      PhysicallyIdentified q hq.le n r (devCoeff r0 y ρ χ h hχ q n) (devData r0 y ρ χ h R hρ hχ hi q hq n)
        (max R 1) x ∧
      ∀ (radE radH : ℕ → ℕ → RestrictedTEActualPiecewise.FieldMap),
        (∀ (x : Vec) (ξ : PlaneInverseCube.Plane), radE n r x ξ =
          radiatedE q hq.le n r (devCoeff r0 y ρ χ h hχ q n) (devData r0 y ρ χ h R hρ hχ hi q hq n) (max R 1) x
            (MaxwellPlaneTail.planePoint ξ)) →
        (∀ (x : Vec) (ξ : PlaneInverseCube.Plane), radH n r x ξ =
          radiatedH q hq.le n r (devCoeff r0 y ρ χ h hχ q n) (devData r0 y ρ χ h R hρ hχ hi q hq n) (max R 1) x
            (MaxwellPlaneTail.planePoint ξ)) →
        ∀ ξ : PlaneInverseCube.Plane,
          RestrictedTEActualPiecewise.deviceFieldsE r0 y ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
              (RestrictedTEBackgroundOutside.outFieldE q hq.le radE) n r x ξ =
            spaceFieldE q hq.le n r (devCoeff r0 y ρ χ h hχ q n) (devData r0 y ρ χ h R hρ hχ hi q hq n)
              (max R 1) x (MaxwellPlaneTail.planePoint ξ) ∧
          RestrictedTEActualPiecewise.deviceFieldsH r0 y ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
              (RestrictedTEBackgroundOutside.outFieldH q hq.le radH) n r x ξ =
            spaceFieldH q hq.le n r (devCoeff r0 y ρ χ h hχ q n) (devData r0 y ρ χ h R hρ hχ hi q hq n)
              (max R 1) x (MaxwellPlaneTail.planePoint ξ) := by
  filter_upwards [device_physical_identification r0 y ρ χ h R hρ hχ hi q hq] with n hn x
  filter_upwards [hn x, SourcePairedReduction.eventually_inner_radius q hq.le n (max R 1)] with r h1 hbr
  exact ⟨h1, fun radE radH hE hH ξ =>
    ⟨deviceFieldsE_eq_space r0 y ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) n r hbr x ξ radE hE,
      deviceFieldsH_eq_space r0 y ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) n r hbr x ξ radH hH⟩⟩

end OQ14.PhysicalFieldIdentification

#print axioms OQ14.PhysicalFieldIdentification.response_split3
#print axioms OQ14.PhysicalFieldIdentification.electric_split3
#print axioms OQ14.PhysicalFieldIdentification.magnetic_split3
#print axioms OQ14.PhysicalFieldIdentification.block_facts
#print axioms OQ14.PhysicalFieldIdentification.shell_support_X
#print axioms OQ14.PhysicalFieldIdentification.incl_support_X
#print axioms OQ14.PhysicalFieldIdentification.exterior_split_electric
#print axioms OQ14.PhysicalFieldIdentification.exterior_split_magnetic
#print axioms OQ14.PhysicalFieldIdentification.coreE_eq_field
#print axioms OQ14.PhysicalFieldIdentification.coreH_eq_field
#print axioms OQ14.PhysicalFieldIdentification.gap_of_not_mem_closure
#print axioms OQ14.PhysicalFieldIdentification.datum_zero
#print axioms OQ14.PhysicalFieldIdentification.core_identification_electric
#print axioms OQ14.PhysicalFieldIdentification.core_identification_magnetic
#print axioms OQ14.PhysicalFieldIdentification.extE_eq_coreEField
#print axioms OQ14.PhysicalFieldIdentification.inclSolution_bounded
#print axioms OQ14.PhysicalFieldIdentification.vSeq_norm_le
#print axioms OQ14.PhysicalFieldIdentification.vSeq_eq
#print axioms OQ14.PhysicalFieldIdentification.coeffFam_congr
#print axioms OQ14.PhysicalFieldIdentification.exterior_identification
#print axioms OQ14.PhysicalFieldIdentification.response_split3_of_integrable
#print axioms OQ14.PhysicalFieldIdentification.response_integrable_ae
#print axioms OQ14.PhysicalFieldIdentification.magnetic_split3_ae
#print axioms OQ14.PhysicalFieldIdentification.scattered_split3_ae
#print axioms OQ14.PhysicalFieldIdentification.annulus_identification_electric
#print axioms OQ14.PhysicalFieldIdentification.annulus_identification_magnetic
#print axioms OQ14.PhysicalFieldIdentification.add_support_X
#print axioms OQ14.PhysicalFieldIdentification.measurableSet_physRegion
#print axioms OQ14.PhysicalFieldIdentification.spaceFieldE_core
#print axioms OQ14.PhysicalFieldIdentification.spaceFieldE_out
#print axioms OQ14.PhysicalFieldIdentification.spaceFieldH_core
#print axioms OQ14.PhysicalFieldIdentification.spaceFieldH_out
#print axioms OQ14.PhysicalFieldIdentification.physical_identification_electric
#print axioms OQ14.PhysicalFieldIdentification.physical_identification_magnetic
#print axioms OQ14.PhysicalFieldIdentification.physical_identification
#print axioms OQ14.PhysicalFieldIdentification.deviceFieldsE_eq_space
#print axioms OQ14.PhysicalFieldIdentification.deviceFieldsH_eq_space
#print axioms OQ14.PhysicalFieldIdentification.device_physical_identification
#print axioms OQ14.PhysicalFieldIdentification.device_piecewise_identification
