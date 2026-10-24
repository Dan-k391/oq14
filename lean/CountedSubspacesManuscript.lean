import RestrictedTEFrequencyScaling
import PhysicalDeviceFields
import RestrictedTEActualDevice

/-! # Manuscript-form corollaries of the final counting theorems

The final theorems of the channel branch carry eventual quantifiers: `∀ᶠ n, ∀ᶠ r, ...`.  The manuscript statement
`uc:counterexample` asks for one finite device.  This module extracts the indices (`Filter.Eventually.exists`), so that
the conclusions are literal existence statements about a single device (a gain index `n` and a shell index `r`):

* `counted_subspaces_exists`: the unit-frequency theorem `RestrictedTEActualDevice.actual_counted_subspaces_device`
  conjoined with the physical identification `PhysicalDeviceFields.device_fields_physical` and the unit throughput
  `actualScatter_norm_eventually`, all at the same `n`, `r`, for the basis vectors of the family;
* `counted_subspaces_at_frequency_exists`: the same for every frequency `k > 0`, from
  `RestrictedTEFrequencyScaling.counted_subspaces_at_frequency`;
* `counted_subspaces_manuscript`: the frequency form with the manuscript's data, the open square `(-L/2, L/2)²` (the
  square `Dsq (L / 2)` of half-side `L / 2`) and the ranges `0 < τ < 1`, `0 < η < δ`; its docstring maps the conclusion
  clause by clause to `uc:counterexample` and lists what is not asserted. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace OQ14.CountedSubspacesManuscript

open Filter Topology MeasureTheory OQ14.MaterialMaxwell OQ14.FrequencyScalingMaxwell OQ14.FrequencyScalingFlux
  OQ14.FrequencyScalingPower OQ14.FrequencyScalingDevice OQ14.PhysicalFieldIdentification
  OQ14.RestrictedTEActualDevice OQ14.RestrictedTEActualCounting OQ14.RestrictedTEPassageTransfer
  OQ14.RestrictedTEActualSquare OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEPartnerSmallness OQ14.ChannelMaterialThroughput OQ14.RestrictedTEActualPiecewise
  OQ14.RestrictedTEBackgroundOutside

/-- **Counted subspaces at unit frequency, with explicit indices.**  For every `εp > 1`, `N`, window `0 < η < δ`,
`τ ≤ 1` and half-side `L > 0` there exist the device parameters of the unit-frequency theorem, an orthonormal family
`A` of `N` finite TE inputs and natural numbers `n` (gain index) and `r` (shell index) such that, for this single
device: the dielectric of the paired coefficient takes values in `[1, εp]` at every point (and the enclosing radius
is below the inner shell radius); the scattering map `actualScatter` has unit throughput,
`‖actualScatter a‖² = physicalPower a` for every finite TE input `a`; the span of `A` is a counted subspace through
the square `Dsq L` for the plane flux of the piecewise device fields; and for every basis vector `A j` the physical
fields are identified with the space versions of the piecewise fields (`PhysicallyIdentified`), and at every plane
point off the circle `‖ξ‖ = radius r` the piecewise device fields are the plane values of the space fields. -/
theorem counted_subspaces_exists (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ)
    (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) :
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (hρh : ρ < h) (_ : 0 ≤ R)
      (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
        ‖abovePoint (hpoint (-L) (ysq N L) l) (h * a)‖ + ρ ≤ R)
      (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ) (n r : ℕ),
      q ^ 2 ≤ εp ∧ 1 + χ ≤ εp ∧
      Orthonormal ℂ (fun j => RestrictedTEInput.input (A j)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      (max R 1 ≤ (SourcePairedInclusion.data q hq.le n r).R ∧
        ∀ x : FourierL2.Space,
          1 ≤ MaterialMaxwell.dielectric (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ hχ.le q n)) x ∧
          MaterialMaxwell.dielectric (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ hχ.le q n)) x ≤ εp) ∧
      (∀ a : SymmetricHarmonicJets.Index →₀ ℂ,
        ‖actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
          (le_max_left R 1) hi q hq n r a‖ ^ 2 = RestrictedTEIncoming.physicalPower a) ∧
      IsCounted (Submodule.span ℂ (Set.range A))
        (actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
          (le_max_left R 1) hi q hq n r)
        (fun a => passage volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
          (deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
            (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
              (devRadE (-L) (ysq N L) ρ χ h R hρ hχ hi hq)) n r)
          (deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
            (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
              (devRadH (-L) (ysq N L) ρ χ h R hρ hχ hi hq)) n r) a))
        (fun a => bypass volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
          (deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
            (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
              (devRadE (-L) (ysq N L) ρ χ h R hρ hχ hi hq)) n r)
          (deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
            (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
              (devRadH (-L) (ysq N L) ρ χ h R hρ hχ hi hq)) n r) a)) τ η δ ∧
      ∀ j : Fin N,
        PhysicallyIdentified q hq.le n r (devCoeff (-L) (ysq N L) ρ χ h hχ q n)
            (devData (-L) (ysq N L) ρ χ h R hρ hχ hi q hq n) (max R 1) (A j) ∧
          ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≠ RadialPhaseLimit.radius r →
            deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
                (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
                  (devRadE (-L) (ysq N L) ρ χ h R hρ hχ hi hq)) n r (A j) ξ =
              spaceFieldE q hq.le n r (devCoeff (-L) (ysq N L) ρ χ h hχ q n)
                (devData (-L) (ysq N L) ρ χ h R hρ hχ hi q hq n) (max R 1) (A j)
                (MaxwellPlaneTail.planePoint ξ) ∧
            deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
                (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
                  (devRadH (-L) (ysq N L) ρ χ h R hρ hχ hi hq)) n r (A j) ξ =
              spaceFieldH q hq.le n r (devCoeff (-L) (ysq N L) ρ χ h hχ q n)
                (devData (-L) (ysq N L) ρ χ h R hρ hχ hi q hq n) (max R 1) (A j)
                (MaxwellPlaneTail.planePoint ξ) := by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6⟩ :=
    OQ14.RestrictedTEActualDevice.actual_counted_subspaces_device εp hεp N η δ hη hηδ τ hτ L hL
  have hphys := OQ14.PhysicalDeviceFields.device_fields_physical (-L) (ysq N L) ρ χ h R hρ hχ hρh hi q hq
  have hb0 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hiso := actualScatter_norm_eventually (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R
    (max R 1) hρ hχ.le hb0 (le_max_left R 1) hi q hq
  obtain ⟨n, hn⟩ := ((h6.and hiso).and hphys).exists
  obtain ⟨⟨hc, hs⟩, hp⟩ := hn
  obtain ⟨r, hr⟩ := (((hc.and hs).and (Filter.eventually_all.mpr (fun j => hp (A j)))).and (h5 n)).exists
  obtain ⟨⟨⟨hcount, hunit⟩, hid⟩, hdiel⟩ := hr
  obtain ⟨hb, hd⟩ := hdiel
  exact ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, n, r, h1, h2, h3, h4, ⟨hb, hd⟩, hunit, hcount, hid⟩

/-- **Counted subspaces at an arbitrary frequency, with explicit indices.**  For every frequency `k > 0`, `εp > 1`,
`N`, window `0 < η < δ`, `τ ≤ 1` and half-side `L > 0` there exist the device parameters of
`counted_subspaces_at_frequency` (the unit-frequency device of half-side `k L`, dilated by `1 / k`), an orthonormal
family `A` of `N` finite TE inputs and natural numbers `n`, `r` such that: the dilated finite TE incident fields are
vacuum weak Maxwell pairs at frequency `k` whose limiting inward power is `physicalPower` (for every input); the
dilated dielectric `scaleCoeff k (pairedCoeff ..)` takes values in `[1, εp]` at every point; the scattering map has
unit throughput; the span of `A` is a counted subspace through the square `Dsq L` for the plane flux of the dilated
device fields; and for every basis vector `A j` the dilated physical fields are a weak Maxwell pair at frequency `k`
with the dilated dielectric, are identified with the dilated space fields (`PhysicallyIdentifiedAt`), and at every
plane point off the circle `‖ξ‖ = radius r / k` the dilated piecewise device fields are the plane values of the
dilated space fields. -/
theorem counted_subspaces_at_frequency_exists (k : ℝ) (hk : 0 < k) (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ)
    (hη : 0 < η) (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) :
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (hρh : ρ < h) (_ : 0 ≤ R)
      (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
        ‖abovePoint (hpoint (-(k * L)) (ysq N (k * L)) l) (h * a)‖ + ρ ≤ R)
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
            (deviceCoeff (fun a l => abovePoint (hpoint (-(k * L)) (ysq N (k * L)) l) (h * a)) ρ χ hχ.le q n)))
            x ∧
          MaterialMaxwell.dielectric (scaleCoeff k (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-(k * L)) (ysq N (k * L)) l) (h * a)) ρ χ hχ.le q n)))
            x ≤ εp) ∧
      (∀ a : SymmetricHarmonicJets.Index →₀ ℂ,
        ‖actualScatter (fun a l => abovePoint (hpoint (-(k * L)) (ysq N (k * L)) l) (h * a)) ρ χ R (max R 1)
          hρ hχ.le (le_max_left R 1) hi q hq n r a‖ ^ 2 = RestrictedTEIncoming.physicalPower a) ∧
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
              (devRadH (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hq)) n r)) a)) τ η δ ∧
      ∀ j : Fin N,
        PhysicallyIdentifiedAt k q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
            (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) (max R 1) (A j) ∧
          TestMaxwell k (MaterialMaxwell.dielectric (scaleCoeff k (pairedCoeff q hq.le n r
              (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n))))
            (scaleField k (physE q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
              (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) (A j)))
            (scaleField k (physH q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
              (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) (A j))) ∧
          ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≠ RadialPhaseLimit.radius r / k →
            scaleMap k (deviceFieldsE (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
                (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
                  (devRadE (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hq)) n r) (A j) ξ =
              scaleField k (spaceFieldE q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
                (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) (max R 1) (A j))
                (MaxwellPlaneTail.planePoint ξ) ∧
            scaleMap k (deviceFieldsH (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1)
                (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
                  (devRadH (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi hq)) n r) (A j) ξ =
              scaleField k (spaceFieldH q hq.le n r (devCoeff (-(k * L)) (ysq N (k * L)) ρ χ h hχ q n)
                (devData (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hi q hq n) (max R 1) (A j))
                (MaxwellPlaneTail.planePoint ξ) := by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    OQ14.RestrictedTEFrequencyScaling.counted_subspaces_at_frequency k hk εp hεp N η δ hη hηδ τ hτ L hL
  have hb0 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hiso := actualScatter_norm_eventually
    (fun a l => abovePoint (hpoint (-(k * L)) (ysq N (k * L)) l) (h * a)) ρ χ R (max R 1) hρ hχ.le hb0
    (le_max_left R 1) hi q hq
  obtain ⟨n, hn⟩ := ((h7.and hiso).and h8).exists
  obtain ⟨⟨hc, hs⟩, hp⟩ := hn
  obtain ⟨r, hr⟩ := (((hc.and hs).and (Filter.eventually_all.mpr (fun j => hp (A j)))).and (h6 n)).exists
  obtain ⟨⟨⟨hcount, hunit⟩, hid⟩, hdiel⟩ := hr
  obtain ⟨hb, hd⟩ := hdiel
  exact ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, n, r, h1, h2, h3, h4, h5, ⟨hb, hd⟩, hunit, hcount, hid⟩

/-- **Manuscript form of `uc:counterexample`: arbitrarily large counted subspaces at fixed thresholds.**
Fix the frequency `k > 0` (the manuscript's `k₀`), `εp > 1` (the manuscript's `ε₊`), the side `L > 0`, `0 < τ < 1` and
`0 < η < δ`; then for every `N` the conclusion below holds.  The square is `Dsq (L / 2)`, the open square
`(-L/2, L/2)²` of the plane `z = 0`.  The data `k`, `εp`, `L`, `τ`, `η`, `δ` are fixed before `N` is chosen, so they
are common to the whole sequence of devices.  The indices `n`, `r` are existential (a single finite device).

Clause by clause:
* *a finite, real scalar dielectric with `1 ≤ ε_r ≤ ε₊`*: the dielectric
  `MaterialMaxwell.dielectric (scaleCoeff k (pairedCoeff q hq.le n r (deviceCoeff ..)))` (the value function of the
  finite paired shell stack plus the `2N` small spheres, dilated for the frequency `k`) satisfies
  `1 ≤ ε ≤ εp` at every point of space (the clause `max R 1 ≤ inner shell radius ∧ ∀ x, 1 ≤ .. ∧ .. ≤ εp`),
  with `q² ≤ εp` and `1 + χ ≤ εp` for the layer and sphere parameters;
* *no interior sources*: the physical fields `physE`, `physH` of the device are the total fields of the source-free
  material problem; at frequency `k` they satisfy the homogeneous weak Maxwell system
  `TestMaxwell k (dielectric ..) (scaleField k physE) (scaleField k physH)` for every basis vector `A j`;
* *the physical incoming space contains an `N`-dimensional counted subspace*: `A : Fin N → ..` is an orthonormal
  family of `N` finite TE inputs for the physical power inner product
  (`Orthonormal ℂ (input ∘ A)`, `finrank (span A) = N`); each input is a vacuum weak Maxwell pair at frequency `k`
  (`TestMaxwell k (fun _ => 1) (scaleField k electric) (scaleField k magnetic)`) whose limiting inward power is
  `physicalPower` (`Tendsto (scaledInwardPower k a) atTop (𝓝 (physicalPower a))`);
* *the selected outgoing map is the complete scattering map*: `actualScatter`, the far amplitude of the scattered
  plus incident field, the map used in the counted-subspace condition;
* *unit power throughput*: `‖actualScatter a‖² = physicalPower a` for every finite TE input `a`; the transmission
  condition `τ ‖a‖² ≤ ‖T a‖²` is the first component of `IsCounted`;
* *passage at least `η` times that power, absolute bypass at most `δ` times that power*: the second and third
  components of `IsCounted (span A) T Pass Byp τ η δ`, namely `η ‖T a‖² ≤ Pass a` and `Byp a ≤ δ ‖a‖²` for every
  `a` in the span, with `Pass` the real part of the integral over the square `Dsq (L / 2)` and `Byp` the integral of
  the modulus over its complement of the plane flux density `E × conj H` (normal component) of the dilated piecewise
  device fields;
* *common frequency, material interval, square, thresholds*: `k`, `εp`, `L / 2`, `τ`, `η`, `δ` do not depend on `N`.

What is NOT asserted: (i) the inputs are the finite even-degree restricted TE fields (the family `A` lies in the
finite-dimensional space of finite TE incoming data of the formalization), so the incoming space of the theorem is
that finite TE space, not the full physical incoming space; (ii) flux integrability: the plane flux is integrated
inside `IsCounted` as a Bochner integral, integrability is proved in the development of the counted-subspace theorem
(the `L¹` estimates) but is not a separate clause here; (iii) the dilation sense of the frequency `k`
(`reviews/frequency_scaling_design.md`, section 5): the frequency-`k` fields are the amplitude-normalized dilations
of the unit-frequency fields of the device of half-side `k (L / 2)`, not re-solved frequency-`k` volume equations;
the physical content is the weak system `TestMaxwell k` for the dilated fields and dilated dielectric, the vacuum
system for the dilated inputs, the invariance of the limiting inward power and (in the development) of the far
amplitude; (iv) the identification of the dilated physical fields with the dilated space fields holds in space (almost
everywhere on the stated regions, pointwise elsewhere) and the plane fields are continuous representatives, equal to
the space fields at the plane points off the circle `‖ξ‖ = radius r / k`, not almost everywhere on the plane for the
`L²` class; (v) the normalization of the flux density against the manuscript's `½ Re ∫ (E × H̄)·ẑ` is the
power normalization of the formalization (scope note, section 4); (vi) no rates: the indices `n` and `r` are
existential, without bounds in `N` or the parameters. -/
theorem counted_subspaces_manuscript (k : ℝ) (hk : 0 < k) (εp : ℝ) (hεp : 1 < εp) (η δ : ℝ) (hη : 0 < η)
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
          ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≠ RadialPhaseLimit.radius r / k →
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
                (MaxwellPlaneTail.planePoint ξ) := by
  have _h0 := hτ0
  exact counted_subspaces_at_frequency_exists k hk εp hεp N η δ hη hηδ τ hτ1.le (L / 2) (half_pos hL)

end OQ14.CountedSubspacesManuscript

#print axioms OQ14.CountedSubspacesManuscript.counted_subspaces_exists
#print axioms OQ14.CountedSubspacesManuscript.counted_subspaces_at_frequency_exists
#print axioms OQ14.CountedSubspacesManuscript.counted_subspaces_manuscript
