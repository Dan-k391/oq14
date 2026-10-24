import FrequencyFieldResponse
import PhysicalFieldIdentification
import RestrictedTEActualCore
import ChannelMaterialThroughput
import DilationVolume

/-! The frequency-`k` fields of the device as the frequency-`k` material solution.

Part A: the dilation identities for the physical fields of the combined shell-plus-inclusion device
`q hq n r ci dci x`, from the field-level identities of `FrequencyFieldResponse`:

* `physE_dilate`, `physH_dilate`: the rescaled physical total electric and magnetic fields are the frequency-`k`
  total fields of `(scaleCoeff k (pairedCoeff ..), dilate k (coreSol ..))` with the rescaled incident field;
* `datum_dilate_shell`, `datum_dilate_incl`, `dilate_datum_add`: the dilated shell and inclusion data are the weighted
  data of the rescaled incident field for the dilated coefficients, and the dilation of the sum of the data is the sum
  of the dilations;
* `scaleCoeff_pairedCoeff`: the dilated paired coefficient is the sum of the dilated shell and inclusion coefficients.

Part B: the dilated combined solution is the frequency-`k` volume solution at radius `X / k` of the dilated device
(`coreSol_dilate`, from `DilationVolume.solution_dilate`), the dilated volume block is a unit exactly when the
unit-frequency block is (`block_isUnit_iff`), hence the rescaled physical fields are the frequency-`k` total fields of
the solution of the dilated volume equation (`physE_volume`, `physH_volume`); `dilated_fields_are_volume_solution`
packages all of this with the dilated data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FrequencyVolumeSolution
open MeasureTheory OQ14.Maxwell
open OQ14.FrequencyScalingMaxwell (scaleField scaleCoeff)
open OQ14.ChannelMaterialThroughput (pairedCoeff)

section PartA

variable (k : ℝ) (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
  (dci : BoundedMaterialKernel.SupportData ci) (x : OQ14.RestrictedTEActualCore.Vec)

/-- **A1.**  The rescaled physical `L2` total electric field is, almost everywhere, the frequency-`k` total electric
field of the dilated paired coefficient with the dilated combined solution and the rescaled incident field. -/
theorem physE_dilate (hk : 0 < k) (i : Fin 3) :
    (fun y => scaleField k (OQ14.PhysicalFieldIdentification.physE q hq n r ci dci x) y i) =ᵐ[volume]
      fun y => MaterialField.total (scaleCoeff k (pairedCoeff q hq n r ci)) k
        (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.coreSol q hq n r ci dci x))
        (scaleField k (RestrictedTEPlaneLocal.electric x)) y i :=
  OQ14.FrequencyFieldResponse.total_dilate k hk _ _ _ i

/-- **A2.**  The rescaled physical total magnetic field is, at every point, the frequency-`k` total magnetic field of
the dilated paired coefficient with the dilated combined solution and the rescaled incident field. -/
theorem physH_dilate (hk : 0 < k) (y : Space) (i : Fin 3) :
    scaleField k (OQ14.PhysicalFieldIdentification.physH q hq n r ci dci x) y i =
      MaterialMaxwell.totalMagnetic (scaleCoeff k (pairedCoeff q hq n r ci)) k
        (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.coreSol q hq n r ci dci x))
        (scaleField k (RestrictedTEPlaneLocal.magnetic x)) y i :=
  OQ14.FrequencyFieldResponse.totalMagnetic_dilate k hk _ _ _ y i

/-- **A3.**  The dilated shell datum is the weighted datum of the rescaled incident electric field for the dilated
shell coefficient. -/
theorem datum_dilate_shell (hk : 0 < k) :
    SourcePairedPlaneIdentification.IsDatum (scaleCoeff k (SourcePairedInclusion.shell q hq n r))
      (scaleField k (RestrictedTEPlaneLocal.electric x))
      (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq n r x)) :=
  OQ14.FrequencyFieldResponse.isDatum_dilate k hk _ _ _ (OQ14.RestrictedTEActualCore.fs_isDatum q hq n r x)

/-- The dilated inclusion datum is the weighted datum of the rescaled incident electric field for the dilated
inclusion coefficient. -/
theorem datum_dilate_incl (hk : 0 < k) :
    SourcePairedPlaneIdentification.IsDatum (scaleCoeff k ci) (scaleField k (RestrictedTEPlaneLocal.electric x))
      (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fiLin ci dci x)) :=
  OQ14.FrequencyFieldResponse.isDatum_dilate k hk _ _ _ (OQ14.RestrictedTEActualCore.fi_isDatum ci dci x)

/-- The dilation of the total datum is the sum of the dilated shell and inclusion data. -/
theorem dilate_datum_add :
    OQ14.DilationL2.dilate k
        (OQ14.RestrictedTEActualCore.fsLin q hq n r x + OQ14.RestrictedTEActualCore.fiLin ci dci x) =
      OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq n r x) +
        OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fiLin ci dci x) :=
  map_add _ _ _

/-- **A4.**  The dilated paired coefficient is the sum of the dilated shell and inclusion coefficients. -/
theorem scaleCoeff_pairedCoeff :
    scaleCoeff k (pairedCoeff q hq n r ci) =
      ShellInclusionVolume.add (scaleCoeff k (SourcePairedInclusion.shell q hq n r)) (scaleCoeff k ci) :=
  OQ14.FrequencyFieldResponse.scaleCoeff_add k _ _

end PartA

section PartB

variable (k : ℝ) (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
  (dci : BoundedMaterialKernel.SupportData ci) (x : OQ14.RestrictedTEActualCore.Vec)

/-- **B1.**  The dilated combined solution is the frequency-`k` solution, at radius `X / k`, of the dilated volume
equation of the dilated paired coefficient with the dilated total datum. -/
theorem coreSol_dilate (hk : 0 < k) :
    OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.coreSol q hq n r ci dci x) =
      MaterialField.solution (scaleCoeff k (pairedCoeff q hq n r ci)) k
        ((SourcePairedInclusion.data q hq n r).X / k)
        (OQ14.DilationL2.dilate k
          (OQ14.RestrictedTEActualCore.fsLin q hq n r x + OQ14.RestrictedTEActualCore.fiLin ci dci x)) :=
  (OQ14.DilationVolume.solution_dilate k (SourcePairedInclusion.data q hq n r).X hk (pairedCoeff q hq n r ci) _).symm

/-- **B2.**  The dilated volume block (frequency `k`, radius `X / k`) of the dilated paired coefficient is a unit
exactly when the unit-frequency volume block of the paired coefficient is. -/
theorem block_isUnit_iff (hk : 0 < k) :
    IsUnit (DynamicVolume.volumeBlock (scaleCoeff k (pairedCoeff q hq n r ci)) k
        ((SourcePairedInclusion.data q hq n r).X / k)) ↔
      IsUnit (DynamicVolume.volumeBlock (pairedCoeff q hq n r ci) 1 (SourcePairedInclusion.data q hq n r).X) :=
  OQ14.DilationVolume.volumeBlock_isUnit_iff k (SourcePairedInclusion.data q hq n r).X hk _

/-- **B3.**  The rescaled physical `L2` total electric field is, almost everywhere, the frequency-`k` total electric
field of the volume solution (radius `X / k`) of the dilated device with the dilated datum. -/
theorem physE_volume (hk : 0 < k) (i : Fin 3) :
    (fun y => scaleField k (OQ14.PhysicalFieldIdentification.physE q hq n r ci dci x) y i) =ᵐ[volume]
      fun y => MaterialField.total (scaleCoeff k (pairedCoeff q hq n r ci)) k
        (MaterialField.solution (scaleCoeff k (pairedCoeff q hq n r ci)) k
          ((SourcePairedInclusion.data q hq n r).X / k)
          (OQ14.DilationL2.dilate k
            (OQ14.RestrictedTEActualCore.fsLin q hq n r x + OQ14.RestrictedTEActualCore.fiLin ci dci x)))
        (scaleField k (RestrictedTEPlaneLocal.electric x)) y i := by
  have h := physE_dilate k q hq n r ci dci x hk i
  rw [coreSol_dilate k q hq n r ci dci x hk] at h
  exact h

/-- **B4.**  The rescaled physical total magnetic field is, at every point, the frequency-`k` total magnetic field of
the volume solution (radius `X / k`) of the dilated device with the dilated datum. -/
theorem physH_volume (hk : 0 < k) (y : Space) (i : Fin 3) :
    scaleField k (OQ14.PhysicalFieldIdentification.physH q hq n r ci dci x) y i =
      MaterialMaxwell.totalMagnetic (scaleCoeff k (pairedCoeff q hq n r ci)) k
        (MaterialField.solution (scaleCoeff k (pairedCoeff q hq n r ci)) k
          ((SourcePairedInclusion.data q hq n r).X / k)
          (OQ14.DilationL2.dilate k
            (OQ14.RestrictedTEActualCore.fsLin q hq n r x + OQ14.RestrictedTEActualCore.fiLin ci dci x)))
        (scaleField k (RestrictedTEPlaneLocal.magnetic x)) y i := by
  have h := physH_dilate k q hq n r ci dci x hk y i
  rw [coreSol_dilate k q hq n r ci dci x hk] at h
  exact h

/-- The dilated total datum is the weighted datum of the rescaled incident electric field for the dilated paired
coefficient (the data of the shell and of the inclusion add up for disjoint supports). -/
theorem datum_dilate_total (hk : 0 < k) (b : ℝ) (hb : b < (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ y : Space, y ∉ Metric.closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0) :
    SourcePairedPlaneIdentification.IsDatum (scaleCoeff k (pairedCoeff q hq n r ci))
      (scaleField k (RestrictedTEPlaneLocal.electric x))
      (OQ14.DilationL2.dilate k
        (OQ14.RestrictedTEActualCore.fsLin q hq n r x + OQ14.RestrictedTEActualCore.fiLin ci dci x)) := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hb.le hci
  have hdk : ShellInclusionVolume.Disjoint (scaleCoeff k (SourcePairedInclusion.shell q hq n r))
      (scaleCoeff k ci) := fun ξ => hd (k • ξ)
  rw [scaleCoeff_pairedCoeff k q hq n r ci, dilate_datum_add k q hq n r ci dci x]
  exact SourcePairedPlaneIdentification.isDatum_add _ _ hdk _ _ _ (datum_dilate_shell k q hq n r x hk)
    (datum_dilate_incl k ci dci x hk)

/-- **B5.  The frequency-`k` fields of the counting theorem are the frequency-`k` material solution.**  For `k > 0`,
the rescaled physical fields of the combined device (`x ↦ k F (k x)` of the `L2` total electric field and of the total
magnetic field of `PhysicalFieldIdentification`) are, almost everywhere for the electric field and at every point for
the magnetic field, exactly the frequency-`k` total electric and magnetic fields `MaterialField.total` and
`MaterialMaxwell.totalMagnetic` of the volume solution `MaterialField.solution` at frequency `k` and radius `X / k` of
the dilated paired coefficient, with the dilated total datum and the rescaled incident field.  The dilated shell and
inclusion data are the weighted data of the rescaled incident electric field for the dilated shell and inclusion
coefficients, the dilated total datum is their sum, and the dilated volume block is a unit exactly when the
unit-frequency block of the device is. -/
theorem dilated_fields_are_volume_solution (hk : 0 < k) :
    (∀ i : Fin 3, (fun y => scaleField k (OQ14.PhysicalFieldIdentification.physE q hq n r ci dci x) y i) =ᵐ[volume]
      fun y => MaterialField.total (scaleCoeff k (pairedCoeff q hq n r ci)) k
        (MaterialField.solution (scaleCoeff k (pairedCoeff q hq n r ci)) k
          ((SourcePairedInclusion.data q hq n r).X / k)
          (OQ14.DilationL2.dilate k
            (OQ14.RestrictedTEActualCore.fsLin q hq n r x + OQ14.RestrictedTEActualCore.fiLin ci dci x)))
        (scaleField k (RestrictedTEPlaneLocal.electric x)) y i) ∧
    (∀ (y : Space) (i : Fin 3),
      scaleField k (OQ14.PhysicalFieldIdentification.physH q hq n r ci dci x) y i =
        MaterialMaxwell.totalMagnetic (scaleCoeff k (pairedCoeff q hq n r ci)) k
          (MaterialField.solution (scaleCoeff k (pairedCoeff q hq n r ci)) k
            ((SourcePairedInclusion.data q hq n r).X / k)
            (OQ14.DilationL2.dilate k
              (OQ14.RestrictedTEActualCore.fsLin q hq n r x + OQ14.RestrictedTEActualCore.fiLin ci dci x)))
          (scaleField k (RestrictedTEPlaneLocal.magnetic x)) y i) ∧
    SourcePairedPlaneIdentification.IsDatum (scaleCoeff k (SourcePairedInclusion.shell q hq n r))
      (scaleField k (RestrictedTEPlaneLocal.electric x))
      (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq n r x)) ∧
    SourcePairedPlaneIdentification.IsDatum (scaleCoeff k ci) (scaleField k (RestrictedTEPlaneLocal.electric x))
      (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fiLin ci dci x)) ∧
    OQ14.DilationL2.dilate k
        (OQ14.RestrictedTEActualCore.fsLin q hq n r x + OQ14.RestrictedTEActualCore.fiLin ci dci x) =
      OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq n r x) +
        OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fiLin ci dci x) ∧
    (IsUnit (DynamicVolume.volumeBlock (scaleCoeff k (pairedCoeff q hq n r ci)) k
        ((SourcePairedInclusion.data q hq n r).X / k)) ↔
      IsUnit (DynamicVolume.volumeBlock (pairedCoeff q hq n r ci) 1 (SourcePairedInclusion.data q hq n r).X)) :=
  ⟨fun i => physE_volume k q hq n r ci dci x hk i, fun y i => physH_volume k q hq n r ci dci x hk y i,
    datum_dilate_shell k q hq n r x hk, datum_dilate_incl k ci dci x hk,
    dilate_datum_add k q hq n r ci dci x, block_isUnit_iff k q hq n r ci hk⟩

end PartB

end OQ14.FrequencyVolumeSolution

#print axioms OQ14.FrequencyVolumeSolution.physE_dilate
#print axioms OQ14.FrequencyVolumeSolution.physH_dilate
#print axioms OQ14.FrequencyVolumeSolution.datum_dilate_shell
#print axioms OQ14.FrequencyVolumeSolution.datum_dilate_incl
#print axioms OQ14.FrequencyVolumeSolution.dilate_datum_add
#print axioms OQ14.FrequencyVolumeSolution.scaleCoeff_pairedCoeff
#print axioms OQ14.FrequencyVolumeSolution.coreSol_dilate
#print axioms OQ14.FrequencyVolumeSolution.block_isUnit_iff
#print axioms OQ14.FrequencyVolumeSolution.physE_volume
#print axioms OQ14.FrequencyVolumeSolution.physH_volume
#print axioms OQ14.FrequencyVolumeSolution.datum_dilate_total
#print axioms OQ14.FrequencyVolumeSolution.dilated_fields_are_volume_solution
