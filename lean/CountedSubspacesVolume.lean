import CountedSubspacesManuscript
import RestrictedTEFrequencyScaling
import FrequencyVolumeSolution

/-! # The frequency-`k` counting theorem with the frequency-`k` volume solution

`FrequencyVolumeSolution.dilated_fields_are_volume_solution` identifies the rescaled physical fields of the device with
the frequency-`k` material total fields of the solution of the dilated volume equation.  This module adds that
identification to the counted-subspace theorems at frequency `k`:

* `counted_subspaces_at_frequency_volume`: the last clause of `RestrictedTEFrequencyScaling.counted_subspaces_at_frequency`
  extended by the volume-solution conjunction and the total-datum clause;
* `counted_subspaces_manuscript_volume`: the manuscript form (explicit indices, square `Dsq (L / 2)`), with the per-basis
  vector clause extended likewise; its docstring updates the list of what is asserted and what is not. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace OQ14.CountedSubspacesVolume

open Filter Topology MeasureTheory OQ14.MaterialMaxwell OQ14.FrequencyScalingMaxwell OQ14.FrequencyScalingFlux
  OQ14.FrequencyScalingPower OQ14.FrequencyScalingDevice OQ14.PhysicalFieldIdentification
  OQ14.RestrictedTEActualDevice OQ14.RestrictedTEActualCounting OQ14.RestrictedTEPassageTransfer
  OQ14.RestrictedTEActualSquare OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEPartnerSmallness OQ14.ChannelMaterialThroughput OQ14.RestrictedTEActualPiecewise
  OQ14.RestrictedTEBackgroundOutside

/-- **Counted subspaces at an arbitrary frequency, with the frequency-`k` volume solution.**
`counted_subspaces_at_frequency` with its last clause extended: eventually in `n`, for every input `x`, eventually in
`r`, besides the identification `PhysicallyIdentifiedAt`, the weak system at frequency `k` and the plane-value
equalities, the rescaled physical fields are the frequency-`k` total fields (`MaterialField.total`, almost everywhere;
`MaterialMaxwell.totalMagnetic`, at every point) of the frequency-`k` volume solution
`MaterialField.solution (scaleCoeff k (pairedCoeff ..)) k (X / k) (dilate k (fsLin .. + fiLin ..))` of the dilated
paired dielectric with the rescaled incident field (`FrequencyVolumeSolution.dilated_fields_are_volume_solution`, at the
dilated device `devCoeff`, `devData`); the dilated total datum is the weighted datum of the rescaled incident electric
field for the dilated paired coefficient (`datum_dilate_total`, with the enclosing radius `max R 1` below the inner shell
radius for large `r` and the inclusion vanishing outside the ball of radius `max R 1`, as in
`PhysicalFieldIdentification`); and the dilated volume block is a unit if and only if the unit-frequency block is. -/
theorem counted_subspaces_at_frequency_volume (k : ℝ) (hk : 0 < k) (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ)
    (hη : 0 < η) (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) :
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (hρh : ρ < h) (_ : 0 ≤ R)
      (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
        ‖abovePoint (hpoint (-(k * L)) (ysq N (k * L)) l) (h * a)‖ + ρ ≤ R)
      (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ),
      q ^ 2 ≤ εp ∧ 1 + χ ≤ εp ∧
      Orthonormal ℂ (fun j => RestrictedTEInput.input (A j)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      (∀ a : SymmetricHarmonicJets.Index →₀ ℂ,
        TestMaxwell k (fun _ => 1) (scaleField k (RestrictedTEPlaneLocal.electric a))
          (scaleField k (RestrictedTEPlaneLocal.magnetic a)) ∧
        Tendsto (scaledInwardPower k a) atTop (𝓝 (RestrictedTEIncoming.physicalPower a))) ∧
      (∀ n : ℕ, ∀ᶠ r : ℕ in atTop, ∃ _ : max R 1 ≤ (SourcePairedInclusion.data q hq.le n r).R,
        ∀ x : FourierL2.Space,
          1 ≤ MaterialMaxwell.dielectric (scaleCoeff k (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-(k * L)) (ysq N (k * L)) l) (h * a)) ρ χ hχ.le q n)))
            x ∧
          MaterialMaxwell.dielectric (scaleCoeff k (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-(k * L)) (ysq N (k * L)) l) (h * a)) ρ χ hχ.le q n)))
            x ≤ εp) ∧
      (∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
        IsCounted (Submodule.span ℂ (Set.range A))
          (actualScatter (fun a l => abovePoint (hpoint (-(k * L)) (ysq N (k * L)) l) (h * a)) ρ χ R (max R 1)
            hρ hχ.le (le_max_left R 1) hi q hq n r)
          (fun a => passage volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
            (scaleMap k (deviceFieldsE (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
              (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
                (devRadE (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hq)) n r))
            (scaleMap k (deviceFieldsH (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
              (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
                (devRadH (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hq)) n r)) a))
          (fun a => bypass volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
            (scaleMap k (deviceFieldsE (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
              (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
                (devRadE (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hq)) n r))
            (scaleMap k (deviceFieldsH (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
              (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
                (devRadH (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hq)) n r)) a)) τ η δ) ∧
      (∀ᶠ n : ℕ in atTop, ∀ x : OQ14.RestrictedTEActualCore.Vec, ∀ᶠ r : ℕ in atTop,
        PhysicallyIdentifiedAt k q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
            (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) (max R 1) x ∧
          TestMaxwell k (MaterialMaxwell.dielectric (scaleCoeff k (pairedCoeff q hq.le n r
              (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n))))
            (scaleField k (physE q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
              (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) x))
            (scaleField k (physH q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
              (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) x)) ∧
          (∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≠ RadialPhaseLimit.radius r / k →
            scaleMap k (deviceFieldsE (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
                (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
                  (devRadE (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hq)) n r) x ξ =
              scaleField k (spaceFieldE q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
                (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) (max R 1) x)
                (MaxwellPlaneTail.planePoint ξ) ∧
            scaleMap k (deviceFieldsH (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
                (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
                  (devRadH (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hq)) n r) x ξ =
              scaleField k (spaceFieldH q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
                (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) (max R 1) x)
                (MaxwellPlaneTail.planePoint ξ)) ∧
          ((∀ i : Fin 3, (fun y => scaleField k (physE q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n) (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) x) y i) =ᵐ[volume]
              fun y => MaterialField.total (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n))) k
                (MaterialField.solution (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n))) k
              ((SourcePairedInclusion.data q hq.le n r).X / k)
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r x +
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n) (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) x)))
                (scaleField k (RestrictedTEPlaneLocal.electric x)) y i) ∧
            (∀ (y : Maxwell.Space) (i : Fin 3),
              scaleField k (physH q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n) (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) x) y i =
                MaterialMaxwell.totalMagnetic (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n))) k
                  (MaterialField.solution (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n))) k
              ((SourcePairedInclusion.data q hq.le n r).X / k)
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r x +
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n) (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) x)))
                  (scaleField k (RestrictedTEPlaneLocal.magnetic x)) y i) ∧
            SourcePairedPlaneIdentification.IsDatum (scaleCoeff k (SourcePairedInclusion.shell q hq.le n r))
              (scaleField k (RestrictedTEPlaneLocal.electric x))
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r x)) ∧
            SourcePairedPlaneIdentification.IsDatum (scaleCoeff k (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n))
              (scaleField k (RestrictedTEPlaneLocal.electric x))
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n) (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) x)) ∧
            OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r x +
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n) (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) x) =
              OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r x) +
                OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n) (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) x) ∧
            (IsUnit (DynamicVolume.volumeBlock (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n))) k
                ((SourcePairedInclusion.data q hq.le n r).X / k)) ↔
              IsUnit (DynamicVolume.volumeBlock (pairedCoeff q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)) 1
                (SourcePairedInclusion.data q hq.le n r).X))) ∧
          SourcePairedPlaneIdentification.IsDatum (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)))
              (scaleField k (RestrictedTEPlaneLocal.electric x))
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r x +
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n) (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) x))):= by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    OQ14.RestrictedTEFrequencyScaling.counted_subspaces_at_frequency k hk εp hεp N η δ hη hηδ τ hτ L hL
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  filter_upwards [h8] with n hn
  intro x
  filter_upwards [hn x, SourcePairedReduction.eventually_inner_radius q hq.le n (max R 1)] with r hr hbr
  have hcar := device_carrier_le (fun a l => abovePoint (hpoint (-(k * L)) (ysq N (k * L)) l) (h * a)) ρ χ R
    (max R 1) hρ hχ.le (le_max_left R 1) hi q hq n
  have hci := SourcePairedReduction.inclusion_vanish (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
    (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) (max R 1) hcar
  exact ⟨hr.1, hr.2.1, hr.2.2,
    OQ14.FrequencyVolumeSolution.dilated_fields_are_volume_solution k q hq.le n r
      (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
      (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) x hk,
    OQ14.FrequencyVolumeSolution.datum_dilate_total k q hq.le n r
      (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
      (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) x hk (max R 1) hbr hci⟩

/-- **Manuscript form of `uc:counterexample`, with the frequency-`k` volume solution.**
This is `OQ14.CountedSubspacesManuscript.counted_subspaces_manuscript` (frequency `k > 0`, `εp > 1`, side `L > 0`,
`0 < τ < 1`, `0 < η < δ`, every `N`; square `Dsq (L / 2)`, the open square `(-L/2, L/2)²`; explicit indices `n`, `r`;
the clauses a finite real scalar dielectric `1 ≤ ε ≤ εp`, no interior sources, the `N`-dimensional orthonormal
family `A` of finite TE inputs, the complete scattering map `actualScatter` with unit throughput
`‖actualScatter a‖² = physicalPower a`, and `IsCounted` (transmission, passage `η ‖T a‖² ≤ Pass a`, bypass
`Byp a ≤ δ ‖a‖²`) through the square, with the common data fixed before `N`) with the per-basis-vector clause
extended by the volume-solution clause at `x := A j`.

**Now asserted (this replaces item (iii) of the "not asserted" list of the manuscript module):** for every basis
vector `A j`, the rescaled physical fields `scaleField k physE`, `scaleField k physH` are the frequency-`k` material
total fields, `MaterialField.total` (almost everywhere, electric) and `MaterialMaxwell.totalMagnetic` (at every point,
magnetic) at frequency `k`, of the frequency-`k` volume solution
`MaterialField.solution (scaleCoeff k (pairedCoeff ..)) k (X / k) (dilate k (fsLin .. + fiLin ..))` of the explicit
dilated dielectric (value formula `counted_subspaces_at_frequency_coefficient`: the value at `ξ` is the value of the
unit-frequency coefficient at `k ξ`) with the rescaled incident field `scaleField k electric`, `scaleField k magnetic`;
the dilated shell datum and the dilated inclusion datum are the weighted data (`IsDatum`) of the rescaled incident
electric field for the dilated shell and inclusion coefficients, their dilated sum is the sum of the dilations, and the
dilated total datum is the weighted datum of the rescaled incident electric field for the dilated paired
coefficient (`datum_dilate_total`, at the extracted `r`, where `max R 1 < inner shell radius`); and the dilated volume
block (frequency `k`, radius `X / k`) is a unit if and only if the unit-frequency volume block of the paired
coefficient is.

**Still not asserted:** (i) the inputs are the finite even-degree restricted TE fields (the family `A` lies in the
finite-dimensional space of finite TE incoming data), not the full physical incoming space; (ii) flux integrability
is not a separate clause (the plane flux is integrated inside `IsCounted`); (iii) the identification of the
dilated physical fields with the dilated space fields (`PhysicallyIdentifiedAt`) is in space (almost everywhere on
the stated regions, pointwise elsewhere) and the plane fields are continuous representatives, equal to the space
fields at the plane points off the circle `‖ξ‖ = radius r / k`; (iv) the normalization of the flux density against the
manuscript's `½ Re ∫ (E × H̄)·ẑ` is the power normalization of the formalization; (v) no rates: `n` and `r` are
existential, without bounds in `N` or the parameters; (vi) the solution map `MaterialField.solution` is `Ring.inverse`
of the volume block (it is zero where the block is not a unit): the clause states only the equivalence of the
invertibility of the dilated and the unit-frequency blocks, and the invertibility of the unit-frequency block of the
device is whatever the frozen development proves (it is used there for the physical fields) and is not re-proved here;
(vii) the dilation is the amplitude-normalized rescaling `k F (k x)` of the unit-frequency fields of the device of
half-side `k (L / 2)` (`reviews/frequency_scaling_design.md`), and the frequency-`k` fields are identified with the
solution of the dilated volume equation as stated above, not re-derived by solving a new equation. -/
theorem counted_subspaces_manuscript_volume (k : ℝ) (hk : 0 < k) (εp : ℝ) (hεp : 1 < εp) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (L : ℝ) (hL : 0 < L) (N : ℕ) :
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (hρh : ρ < h) (_ : 0 ≤ R)
      (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
        ‖abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)‖ + ρ ≤ R)
      (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ) (n r : ℕ),
      q ^ 2 ≤ εp ∧ 1 + χ ≤ εp ∧
      Orthonormal ℂ (fun j => RestrictedTEInput.input (A j)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      (∀ a : SymmetricHarmonicJets.Index →₀ ℂ,
        TestMaxwell k (fun _ => 1) (scaleField k (RestrictedTEPlaneLocal.electric a))
          (scaleField k (RestrictedTEPlaneLocal.magnetic a)) ∧
        Tendsto (scaledInwardPower k a) atTop (𝓝 (RestrictedTEIncoming.physicalPower a))) ∧
      (max R 1 ≤ (SourcePairedInclusion.data q hq.le n r).R ∧
        ∀ x : FourierL2.Space,
          1 ≤ MaterialMaxwell.dielectric (scaleCoeff k (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a))
              ρ χ hχ.le q n))) x ∧
          MaterialMaxwell.dielectric (scaleCoeff k (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a))
              ρ χ hχ.le q n))) x ≤ εp) ∧
      (∀ a : SymmetricHarmonicJets.Index →₀ ℂ,
        ‖actualScatter (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ R
          (max R 1) hρ hχ.le (le_max_left R 1) hi q hq n r a‖ ^ 2 = RestrictedTEIncoming.physicalPower a) ∧
      IsCounted (Submodule.span ℂ (Set.range A))
        (actualScatter (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ R
          (max R 1) hρ hχ.le (le_max_left R 1) hi q hq n r)
        (fun a => passage volume (Dsq (L / 2)) (OQ14.RestrictedTEActualFields.fieldFlux
          (scaleMap k (deviceFieldsE (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh hq
            (le_max_left R 1) (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
              (devRadE (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hq)) n r))
          (scaleMap k (deviceFieldsH (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh hq
            (le_max_left R 1) (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
              (devRadH (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hq)) n r)) a))
        (fun a => bypass volume (Dsq (L / 2)) (OQ14.RestrictedTEActualFields.fieldFlux
          (scaleMap k (deviceFieldsE (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh hq
            (le_max_left R 1) (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
              (devRadE (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hq)) n r))
          (scaleMap k (deviceFieldsH (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh hq
            (le_max_left R 1) (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
              (devRadH (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hq)) n r)) a)) τ η δ ∧
      ∀ j : Fin N,
        PhysicallyIdentifiedAt k q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)
            (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (max R 1) (A j) ∧
          TestMaxwell k (MaterialMaxwell.dielectric (scaleCoeff k (pairedCoeff q hq.le n r
              (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))))
            (scaleField k (physE q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)
              (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j)))
            (scaleField k (physH q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)
              (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j))) ∧
          (∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≠ RadialPhaseLimit.radius r / k →
            scaleMap k (deviceFieldsE (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh hq
                (le_max_left R 1) (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
                  (devRadE (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hq)) n r) (A j) ξ =
              scaleField k (spaceFieldE q hq.le n r
                (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)
                (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (max R 1) (A j))
                (MaxwellPlaneTail.planePoint ξ) ∧
            scaleMap k (deviceFieldsH (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh hq
                (le_max_left R 1) (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
                  (devRadH (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hq)) n r) (A j) ξ =
              scaleField k (spaceFieldH q hq.le n r
                (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)
                (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (max R 1) (A j))
                (MaxwellPlaneTail.planePoint ξ)) ∧
          ((∀ i : Fin 3, (fun y => scaleField k (physE q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j)) y i) =ᵐ[volume]
              fun y => MaterialField.total (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))) k
                (MaterialField.solution (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))) k
              ((SourcePairedInclusion.data q hq.le n r).X / k)
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r (A j) +
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j))))
                (scaleField k (RestrictedTEPlaneLocal.electric (A j))) y i) ∧
            (∀ (y : Maxwell.Space) (i : Fin 3),
              scaleField k (physH q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j)) y i =
                MaterialMaxwell.totalMagnetic (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))) k
                  (MaterialField.solution (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))) k
              ((SourcePairedInclusion.data q hq.le n r).X / k)
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r (A j) +
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j))))
                  (scaleField k (RestrictedTEPlaneLocal.magnetic (A j))) y i) ∧
            SourcePairedPlaneIdentification.IsDatum (scaleCoeff k (SourcePairedInclusion.shell q hq.le n r))
              (scaleField k (RestrictedTEPlaneLocal.electric (A j)))
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r (A j))) ∧
            SourcePairedPlaneIdentification.IsDatum (scaleCoeff k (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))
              (scaleField k (RestrictedTEPlaneLocal.electric (A j)))
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j))) ∧
            OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r (A j) +
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j)) =
              OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r (A j)) +
                OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j)) ∧
            (IsUnit (DynamicVolume.volumeBlock (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))) k
                ((SourcePairedInclusion.data q hq.le n r).X / k)) ↔
              IsUnit (DynamicVolume.volumeBlock (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)) 1
                (SourcePairedInclusion.data q hq.le n r).X))) ∧
          SourcePairedPlaneIdentification.IsDatum (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)))
              (scaleField k (RestrictedTEPlaneLocal.electric (A j)))
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r (A j) +
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j))):= by
  have _h0 := hτ0
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    counted_subspaces_at_frequency_volume k hk εp hεp N η δ hη hηδ τ hτ1.le (L / 2) (half_pos hL)
  have hb0 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hiso := actualScatter_norm_eventually
    (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
    hb0 (le_max_left R 1) hi q hq
  obtain ⟨n, hn⟩ := ((h7.and hiso).and h8).exists
  obtain ⟨⟨hc, hs⟩, hp⟩ := hn
  obtain ⟨r, hr⟩ := (((hc.and hs).and (Filter.eventually_all.mpr (fun j => hp (A j)))).and (h6 n)).exists
  obtain ⟨⟨⟨hcount, hunit⟩, hid⟩, hdiel⟩ := hr
  obtain ⟨hb, hd⟩ := hdiel
  exact ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, n, r, h1, h2, h3, h4, h5, ⟨hb, hd⟩, hunit, hcount, hid⟩

end OQ14.CountedSubspacesVolume

#print axioms OQ14.CountedSubspacesVolume.counted_subspaces_at_frequency_volume
#print axioms OQ14.CountedSubspacesVolume.counted_subspaces_manuscript_volume
