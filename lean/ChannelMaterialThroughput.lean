import ChannelUnitThroughput
import ExteriorMaterial
import SmallVolumeMaxwell
import SourcePairedSolutionFormula
import RestrictedTEDatumLinear
import SourcePairedReduction

/-! Unit throughput of the actual material device.

For a bounded nonnegative coefficient `c` supported in `closedBall 0 d.radius` and the volume solution `u` of
`volumeBlock c 1 d.radius u = datum c d A` (finite restricted TE incident field `A`), the complete field
`E = ExteriorMaterial.total c 1 d.radius u (electric A)`, `H = totalMagnetic c 1 u (magnetic A)` satisfies every
hypothesis of `ChannelUnitThroughput.unit_throughput_energy`: it is a weak Maxwell pair with the real bounded
permittivity `dielectric c` (`MaterialMaxwell.volume_solution_testMaxwell`, transported to the continuous exterior
representative by `ExteriorMaterial.testMaxwell_congr`), locally L2, and outside the support it is the incident field
(incoming plus outgoing Hankel parts) plus the pointwise dyadic integral of the source
`ρ = DynamicVolume.source c u`.  Hence `(∫ |out|^2)/2 = ‖input A‖^2`.  The same holds for the paired shells plus
inclusion `add (shell q hq n r) ci` whenever the effective inclusion block is a unit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.ChannelMaterialThroughput
open Filter MeasureTheory Metric Topology OQ14.Maxwell OQ14.ChannelScaledFields OQ14.ChannelFarFluxExpansion
  OQ14.ChannelUnitThroughput
abbrev Idx := SymmetricHarmonicJets.Index
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

/-- Support data of a coefficient vanishing outside a given closed ball (carrier: the set where it is nonzero). -/
def supportOfRadius (c : Coefficient) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall (0 : Space) R → c.value (VectorFourier.coordinateMap x) = 0) :
    BoundedMaterialKernel.SupportData c where
  radius := R
  carrier := {x | c.value (VectorFourier.coordinateMap x) ≠ 0}
  measurable := (c.measurable.comp VectorFourier.coordinateMap.measurable) (measurableSet_singleton (0 : ℝ)).compl
  finite := by
    have hsub : {x : Space | c.value (VectorFourier.coordinateMap x) ≠ 0} ⊆ closedBall (0 : Space) R := by
      intro x hx
      by_contra h
      exact hx (hc x h)
    exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hsub)
  ballZero := hc
  carrierZero := fun x hx => by simpa using hx

theorem dielectric_measurable (c : Coefficient) : Measurable (MaterialMaxwell.dielectric c) :=
  measurable_const.add (c.measurable.comp VectorFourier.coordinateMap.measurable)

theorem dielectric_norm_le (c : Coefficient) (x : Space) : ‖MaterialMaxwell.dielectric c x‖ ≤ 1 + c.bound := by
  have h := MaterialMaxwell.dielectric_bounds c x
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [h.1])]
  exact h.2

/-- Unit throughput of the actual material device: for the volume solution `u` of the dielectric with the finite TE
incident field `A`, half the outgoing energy of the complete field is the physical incoming power. -/
theorem material_unit_throughput (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (A : Idx →₀ ℂ)
    (u : VectorL2) (hsol : DynamicVolume.volumeBlock c 1 d.radius u = RestrictedTEMaterial.datum c d A) :
    (∫ n, energy (outAmplitude A (DynamicVolume.source c u) n) ∂OQ14.AngularPower.angularMeasure) / 2 =
      ‖RestrictedTEInput.input A‖ ^ 2 := by
  have hρ : ∀ j, Integrable (DynamicVolume.source c u j) :=
    DynamicVolume.source_integrable c u d.radius d.ballZero
  have hmax0 : MaterialMaxwell.TestMaxwell 1 (MaterialMaxwell.dielectric c)
      (MaterialField.total c 1 u (RestrictedTEPlaneLocal.electric A))
      (MaterialMaxwell.totalMagnetic c 1 u (RestrictedTEPlaneLocal.magnetic A)) :=
    MaterialMaxwell.volume_solution_testMaxwell c 1 d.radius u (RestrictedTEMaterial.datum c d A)
      (RestrictedTEPlaneLocal.electric A) (RestrictedTEPlaneLocal.magnetic A) d.ballZero
      (RestrictedTEMaterial.datum_actual c d A) hsol
      (fun i => (RestrictedTEMaterial.electric_smooth A i).continuous.locallyIntegrable)
      (fun i => (RestrictedTEMaterial.magnetic_smooth A i).continuous.locallyIntegrable)
      (RestrictedTEMaterial.testMaxwell A)
  have hmax : MaterialMaxwell.TestMaxwell 1 (MaterialMaxwell.dielectric c)
      (ExteriorMaterial.total c 1 d.radius u (RestrictedTEPlaneLocal.electric A))
      (MaterialMaxwell.totalMagnetic c 1 u (RestrictedTEPlaneLocal.magnetic A)) :=
    ExteriorMaterial.testMaxwell_congr 1 _ _ _ _ _
      (ExteriorMaterial.total_ae c 1 d.radius u _ d.ballZero).symm Filter.EventuallyEq.rfl hmax0
  have hc : ∀ j y, y ∉ closedBall (0 : Space) (max d.radius 0) → DynamicVolume.source c u j y = 0 :=
    fun j y hy => DynamicVolume.source_zero c u d.radius d.ballZero j y
      (fun h => hy (closedBall_subset_closedBall (le_max_left _ _) h))
  have hEx : ∀ x : Space, max d.radius 0 < ‖x‖ →
      ExteriorMaterial.total c 1 d.radius u (RestrictedTEPlaneLocal.electric A) x =
        RestrictedTEIncoming.incomingElectric A x + RestrictedTEIncoming.outgoingElectric A x +
          ExteriorContinuity.electric 1 (DynamicVolume.source c u) x := by
    intro x hx
    have hxR : d.radius < ‖x‖ := lt_of_le_of_lt (le_max_left _ _) hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (le_max_right _ _) hx)
    funext i
    have h1 : RestrictedTEPlaneLocal.electric A x i =
        RestrictedTEIncoming.outgoingElectric A x i + RestrictedTEIncoming.incomingElectric A x i :=
      congrFun (RestrictedTEIncoming.electric_split A x hx0) i
    have h2 : ExteriorContinuity.electric 1 (DynamicVolume.source c u) x i =
        ∑ j, ∫ y, DynamicVolume.source c u j y * DyadicKernel.dyadic 1 (x - y) i j := rfl
    change RestrictedTEPlaneLocal.electric A x i + ExteriorMaterial.scattered c 1 d.radius u x i = _
    rw [ExteriorMaterial.scattered_exterior c 1 d.radius u x hxR i, h1]
    simp only [Pi.add_apply]
    rw [h2]
    ring
  have hHx : ∀ x : Space, max d.radius 0 < ‖x‖ →
      MaterialMaxwell.totalMagnetic c 1 u (RestrictedTEPlaneLocal.magnetic A) x =
        RestrictedTEIncoming.incomingMagnetic A x + RestrictedTEIncoming.outgoingMagnetic A x +
          MagneticResponse.magnetic 1 (DynamicVolume.source c u) x := by
    intro x hx
    have hx0 : x ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (le_max_right _ _) hx)
    funext i
    have h1 : RestrictedTEPlaneLocal.magnetic A x i =
        RestrictedTEIncoming.outgoingMagnetic A x i + RestrictedTEIncoming.incomingMagnetic A x i :=
      congrFun (RestrictedTEIncoming.magnetic_split A x hx0) i
    change RestrictedTEPlaneLocal.magnetic A x i + MagneticResponse.magnetic 1 (DynamicVolume.source c u) x i = _
    rw [h1]
    simp only [Pi.add_apply]
    ring
  exact unit_throughput_input_norm A (max d.radius 0) (le_max_right _ _) (DynamicVolume.source c u) hρ hc
    (MaterialMaxwell.dielectric c) (dielectric_measurable c) (1 + c.bound) (dielectric_norm_le c)
    (ExteriorMaterial.total c 1 d.radius u (RestrictedTEPlaneLocal.electric A))
    (MaterialMaxwell.totalMagnetic c 1 u (RestrictedTEPlaneLocal.magnetic A))
    (fun T i => ExteriorMaterial.total_memLp_ball c 1 d.radius T u (RestrictedTEPlaneLocal.electric A) d.ballZero
      (fun i' => RestrictedTEMaterial.electric_memLp A T i') i)
    (fun T i => SmallVolumeMaxwell.total_magnetic_memLp_ball c 1 d.radius T u (RestrictedTEPlaneLocal.magnetic A)
      d.ballZero (fun i' => magnetic_memLp A T i') i)
    hmax hEx hHx

/-- The same with the volume block a unit and the solution given by the inverse of the block. -/
theorem material_unit_throughput_of_isUnit (c : Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (hU : IsUnit (DynamicVolume.volumeBlock c 1 d.radius)) (A : Idx →₀ ℂ) :
    (∫ n, energy (outAmplitude A (DynamicVolume.source c
        (Ring.inverse (DynamicVolume.volumeBlock c 1 d.radius) (RestrictedTEMaterial.datum c d A))) n)
      ∂OQ14.AngularPower.angularMeasure) / 2 = ‖RestrictedTEInput.input A‖ ^ 2 := by
  refine material_unit_throughput c d A _ ?_
  exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (RestrictedTEMaterial.datum c d A))
    (Ring.mul_inverse_cancel (DynamicVolume.volumeBlock c 1 d.radius) hU)

/-! ### The paired shells plus inclusion -/

/-- The combined susceptibility of the actual paired shell and the inclusion. -/
abbrev pairedCoeff (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) : Coefficient :=
  ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci

theorem pairedCoeff_support (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (b : ℝ)
    (hb : b ≤ (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ x : Space, x ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap x) = 0) :
    ∀ x : Space, x ∉ closedBall (0 : Space) (SourcePairedInclusion.data q hq n r).X →
      (pairedCoeff q hq n r ci).value (VectorFourier.coordinateMap x) = 0 := by
  intro x hx
  change (SourcePairedInclusion.shell q hq n r).value (VectorFourier.coordinateMap x) +
    ci.value (VectorFourier.coordinateMap x) = 0
  rw [SourcePairedInclusion.shell_support q hq n r x hx,
    SourcePairedInclusion.inclusion_support q hq n r ci b hb hci x hx, add_zero]

/-- Support data of the combined coefficient at the enclosing radius of the actual shells. -/
def pairedSupport (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (b : ℝ)
    (hb : b ≤ (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ x : Space, x ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap x) = 0) :
    BoundedMaterialKernel.SupportData (pairedCoeff q hq n r ci) :=
  supportOfRadius _ (SourcePairedInclusion.data q hq n r).X (pairedCoeff_support q hq n r ci b hb hci)

/-- The combined volume solution for the finite TE incident field `A`. -/
def pairedSolution (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (b : ℝ)
    (hb : b ≤ (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ x : Space, x ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap x) = 0)
    (A : Idx →₀ ℂ) : VectorL2 :=
  MaterialField.solution (pairedCoeff q hq n r ci) 1 (SourcePairedInclusion.data q hq n r).X
    (RestrictedTEMaterial.datum (pairedCoeff q hq n r ci) (pairedSupport q hq n r ci b hb hci) A)

/-- The combined solution is the explicit inverse formula applied to the datum. -/
theorem pairedSolution_eq (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (b : ℝ)
    (hb : b ≤ (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ x : Space, x ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap x) = 0)
    (hE : IsUnit (DynamicVolume.volumeBlock ci 1 b -
      ShellInclusionReaction.reaction (SourcePairedInclusion.shell q hq n r) ci 1
        (SourcePairedInclusion.data q hq n r).X))
    (A : Idx →₀ ℂ) :
    pairedSolution q hq n r ci b hb hci A =
      ShellInclusionBlocks.combinedInverse
        (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r))
        (StaticCoefficient.sqrtMultiplier ci)
        (ShellInclusionVolume.kernel 1 (SourcePairedInclusion.data q hq n r).X)
        (RestrictedTEMaterial.datum (pairedCoeff q hq n r ci) (pairedSupport q hq n r ci b hb hci) A) :=
  SourcePairedSolutionFormula.combined_solution_eq q hq n r ci b hb hci hE _

/-- Unit throughput of the actual paired-shell-plus-inclusion device at shell index `r`, whenever the effective
inclusion block is a unit. -/
theorem paired_device_unit_throughput (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (b : ℝ)
    (hb : b ≤ (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ x : Space, x ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap x) = 0)
    (hE : IsUnit (DynamicVolume.volumeBlock ci 1 b -
      ShellInclusionReaction.reaction (SourcePairedInclusion.shell q hq n r) ci 1
        (SourcePairedInclusion.data q hq n r).X))
    (A : Idx →₀ ℂ) :
    (∫ m, energy (outAmplitude A (DynamicVolume.source (pairedCoeff q hq n r ci)
        (pairedSolution q hq n r ci b hb hci A)) m) ∂OQ14.AngularPower.angularMeasure) / 2 =
      ‖RestrictedTEInput.input A‖ ^ 2 := by
  have hU : IsUnit (DynamicVolume.volumeBlock (pairedCoeff q hq n r ci) 1
      (SourcePairedInclusion.data q hq n r).X) :=
    SourcePairedInclusion.combined_isUnit_of_effective q hq n r ci b hb hci hE
  refine material_unit_throughput (pairedCoeff q hq n r ci) (pairedSupport q hq n r ci b hb hci) A _ ?_
  exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 =>
    L (RestrictedTEMaterial.datum (pairedCoeff q hq n r ci) (pairedSupport q hq n r ci b hb hci) A))
    (Ring.mul_inverse_cancel (DynamicVolume.volumeBlock (pairedCoeff q hq n r ci) 1
      (SourcePairedInclusion.data q hq n r).X) hU)

/-- For a fixed finite inclusion with a unit limiting effective block, for all large shell indices `r` the paired
device has unit throughput for every finite TE incident field. -/
theorem paired_device_unit_throughput_eventually (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : Coefficient)
    (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : 0 < b) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b)
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci d b hb)) :
    ∀ᶠ r : ℕ in atTop, ∃ hbR : b ≤ (SourcePairedInclusion.data q hq n r).R,
      ∀ A : Idx →₀ ℂ,
        (∫ m, energy (outAmplitude A (DynamicVolume.source (pairedCoeff q hq n r ci)
          (pairedSolution q hq n r ci b hbR (SourcePairedReduction.inclusion_vanish ci d b hcar) A)) m)
          ∂OQ14.AngularPower.angularMeasure) / 2 = ‖RestrictedTEInput.input A‖ ^ 2 := by
  filter_upwards [SourcePairedReduction.eventually_effective_isUnit q hq n ci d b hb hcar hL,
    SourcePairedReduction.eventually_inner_radius q hq n b] with r hE hbR
  exact ⟨hbR.le, fun A => paired_device_unit_throughput q hq n r ci b hbR.le
    (SourcePairedReduction.inclusion_vanish ci d b hcar) hE A⟩

end OQ14.ChannelMaterialThroughput
#print axioms OQ14.ChannelMaterialThroughput.dielectric_measurable
#print axioms OQ14.ChannelMaterialThroughput.dielectric_norm_le
#print axioms OQ14.ChannelMaterialThroughput.material_unit_throughput
#print axioms OQ14.ChannelMaterialThroughput.material_unit_throughput_of_isUnit
#print axioms OQ14.ChannelMaterialThroughput.pairedCoeff_support
#print axioms OQ14.ChannelMaterialThroughput.pairedSolution_eq
#print axioms OQ14.ChannelMaterialThroughput.paired_device_unit_throughput
#print axioms OQ14.ChannelMaterialThroughput.paired_device_unit_throughput_eventually
