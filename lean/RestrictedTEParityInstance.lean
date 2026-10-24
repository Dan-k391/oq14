import RestrictedTEActualPhase
import RestrictedTEBackgroundOutside
import BackgroundTransmissionParity
import CoreMajorantDevice

/-! The counted-subspace theorem for the modal phase and the discharged core majorant.

* `actual_counted_subspaces_of_pieces_parity`: `RestrictedTEActualPhase.actual_counted_subspaces_of_pieces_phase`
  with the global phase `c q n = parityPhase q n` of the modal module `BackgroundTransmissionParity`
  (`parityPhase_norm`, `input_scaledCoeff`), so that the twist hypothesis is gone: the remaining hypotheses are the
  outside fields `outE`, `outH` with measurable coordinates, the structure `OutsideDecomposition` and `CoreMajorant`.
* `actual_counted_subspaces_of_radiated`: the outside fields are the TE background plus linear radiated fields
  (`outFieldE`, `outFieldH` of `RestrictedTEBackgroundOutside`, whose sum structure holds by definition) and the core
  majorant is discharged by `CoreMajorantDevice.coreMajorant_device`.  The remaining field hypotheses are exactly
  that the radiated fields `radE`, `radH` have measurable coordinates and satisfy the uniform radial/tangential
  decomposition `hrad` (for all large `n`, on the unit-power sphere of the span of every orthonormal family, uniformly
  in the shell index, outside the disk of radius `radius r`). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEParityInstance
open MeasureTheory Filter Topology Metric Set
open scoped ComplexConjugate
open OQ14.RestrictedTEPassageTransfer OQ14.RestrictedTEActualCounting OQ14.RestrictedTEActualWindow
  OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEConcreteDoubled OQ14.RestrictedTEPartnerBalls OQ14.RestrictedTEPlaneJets
  OQ14.RestrictedTEPartnerCount OQ14.RestrictedTEPartnerSmallness OQ14.ChannelMaterialThroughput
  OQ14.RestrictedTEActualSquare OQ14.RestrictedTEActualPiecewise

abbrev FieldMap := OQ14.RestrictedTEActualFields.FieldMap
abbrev Vec := OQ14.RestrictedTEActualCore.Vec

/-- **Counted subspaces from the pieces, with the modal phase.**  The twist hypothesis of
`actual_counted_subspaces_of_pieces` is discharged by the modal computation: the global phase of the limiting
transmissions is `parityPhase q n` (modulus one, `parityPhase_norm`) and the physical input of the rescaled vector is
`q^n * parityPhase q n` times its input (`input_scaledCoeff`).  For the device parameters and the orthonormal family
`A` of the square theorem, for every pair of outside fields with measurable coordinates satisfying
`OutsideDecomposition` and every core majorant, the span of `A` is counted through the square for the flux of the
assembled plane fields. -/
theorem actual_counted_subspaces_of_pieces_parity (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) :
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (hρh : ρ < h) (_ : 0 ≤ R)
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
      ∀ (outE outH : ℕ → ℕ → FieldMap) (radE radH : ℕ → ℕ → Vec → PlaneInverseCube.Plane → Maxwell.Vector),
        (∀ (n r : ℕ) (x : Vec) (i : Fin 3), AEStronglyMeasurable (fun ξ => outE n r x ξ i) volume ∧
          AEStronglyMeasurable (fun ξ => outH n r x ξ i) volume) →
        OutsideDecomposition q hq.le outE outH radE radH →
        CoreMajorant (-L) (ysq N L) ρ χ h R hρ hχ hi q hq →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
              (deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outE n r)
              (deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outH n r) a))
            (fun a => bypass volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
              (deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outE n r)
              (deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outH n r) a)) τ η δ :=
  OQ14.RestrictedTEActualPhase.actual_counted_subspaces_of_pieces_phase εp hεp N η δ hη hηδ τ hτ L hL
    (fun q n => OQ14.BackgroundTransmissionParity.parityPhase q n)
    (fun q _ => Eventually.of_forall (OQ14.BackgroundTransmissionParity.parityPhase_norm q))
    (fun q hq => Eventually.of_forall (fun n x => OQ14.BackgroundTransmissionParity.input_scaledCoeff q hq.le n x))

/-- **Counted subspaces for the TE background plus a radiated field.**  For every `ε₊ > 1`, `N`, thresholds
`0 < η < δ`, `τ ≤ 1` and half-side `L > 0` there are the device parameters of the square theorem and an orthonormal
family `A` of `N` physical inputs (permittivity of the paired device in `[1, ε₊]`) such that for all linear radiated
fields `radE`, `radH` of the input with measurable plane coordinates (`hmeas`) satisfying the uniform
radial/tangential decomposition (`hrad`: for all large `n`, for every orthonormal family, constants `K1 K2 L1 L2` and
a shell index `r2` such that for `r ≥ r2`, every unit-power `x` in the span and every plane point outside the disk of
radius `radius r` the radiated electric and magnetic fields decompose), the span of `A` is a counted subspace through
the square `Dsq L` for the plane flux of the assembled fields: the cut-off device core fields inside the disk of
radius `radius r` and the TE background `bgOutE`, `bgOutH` plus the radiated fields `radE`, `radH` beyond.  The core
majorant is the proved `CoreMajorantDevice.coreMajorant_device`. -/
theorem actual_counted_subspaces_of_radiated (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) :
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (hρh : ρ < h) (_ : 0 ≤ R)
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
      ∀ (radE radH : ℕ → ℕ → FieldMap),
        (∀ (n r : ℕ) (x : Vec) (i : Fin 3), AEStronglyMeasurable (fun ξ => radE n r x ξ i) volume ∧
          AEStronglyMeasurable (fun ξ => radH n r x ξ i) volume) →
        (∀ᶠ n : ℕ in atTop, ∀ (N' : Nat) (B : Fin N' → Vec),
          Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (K1 K2 L1 L2 : ℝ) (r2 : ℕ),
            ∀ r ≥ r2, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
              ∀ ξ : PlaneInverseCube.Plane, RadialPhaseLimit.radius r ≤ ‖ξ‖ →
                OQ14.SourceRemotePlaneBand.Decomp K1 K2 (radE n r x ξ) (MaxwellPlaneTail.planePoint ξ) ∧
                  OQ14.SourceRemotePlaneBand.Decomp L1 L2 (radH n r x ξ) (MaxwellPlaneTail.planePoint ξ)) →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
              (deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
                (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le radE) n r)
              (deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
                (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le radH) n r) a))
            (fun a => bypass volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
              (deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
                (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le radE) n r)
              (deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
                (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le radH) n r) a)) τ η δ := by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6⟩ :=
    actual_counted_subspaces_of_pieces_parity εp hεp N η δ hη hηδ τ hτ L hL
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, ?_⟩
  intro radE radH hmeas hrad
  refine h6 (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le radE)
    (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le radH) (fun n r x ξ => radE n r x ξ)
    (fun n r x ξ => radH n r x ξ) ?_
    (OQ14.RestrictedTEBackgroundOutside.outsideDecomposition_of_radiated q hq.le radE radH hrad)
    (OQ14.CoreMajorantDevice.coreMajorant_device (-L) (ysq N L) ρ χ h R hρ hχ hρh hi q hq)
  intro n r x i
  exact ⟨(OQ14.RestrictedTEBackgroundOutside.bgOutE_meas q hq.le n r x i).add (hmeas n r x i).1,
    (OQ14.RestrictedTEBackgroundOutside.bgOutH_meas q hq.le n r x i).add (hmeas n r x i).2⟩

end OQ14.RestrictedTEParityInstance

#print axioms OQ14.RestrictedTEParityInstance.actual_counted_subspaces_of_pieces_parity
#print axioms OQ14.RestrictedTEParityInstance.actual_counted_subspaces_of_radiated
