import FrequencyScalingDevice
import FrequencyScalingPower

/-! # Counted subspaces at an arbitrary frequency: the final k-frequency counting theorem

This module derives the k-frequency form of the final counting theorem of the channel branch from the frozen
unit-frequency theorem `OQ14.RestrictedTEActualDevice.actual_counted_subspaces_device` by the dilation lemmas
of `FrequencyScalingMaxwell`, `FrequencyScalingFlux`, `FrequencyScalingPower` and `FrequencyScalingDevice`.

* `ysq_mul`, `hpoint_smul`, `abovePoint_smul`, `devPos_scale`: the geometry of the dilated device.  The k-frequency
  device is the unit-frequency device of half-side `k L` dilated by `1 / k`: the sphere centres of the device of
  half-side `k L` at height `h a` are `k` times the sphere centres of half-side `L` at height `h / k * a`.
* `counted_subspaces_at_frequency`: for every frequency `k > 0` the unit-frequency device of half-side `k L`,
  with its coefficient dilated by `scaleCoeff k` and its plane fields dilated by `scaleMap k`, gives an orthonormal
  family of `N` finite TE inputs whose span is a counted subspace through the square of half-side `L`, with the
  same scattering map, power and thresholds.  The k-frequency incident fields are weak vacuum Maxwell pairs at
  frequency `k` with limiting inward power `physicalPower`, and the dilated physical fields are weak Maxwell pairs
  at frequency `k` with the dilated dielectric, identified with the dilated space fields.
* `counted_subspaces_at_frequency_coefficient`: the explicit value formula of the k-frequency device coefficient.

The k-frequency fields are dilations of the unit-frequency fields, not re-solved volume equations. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace OQ14.RestrictedTEFrequencyScaling

open Filter Topology MeasureTheory OQ14.MaterialMaxwell OQ14.FrequencyScalingMaxwell OQ14.FrequencyScalingFlux
  OQ14.FrequencyScalingPower OQ14.FrequencyScalingDevice OQ14.PhysicalFieldIdentification
  OQ14.RestrictedTEActualDevice OQ14.RestrictedTEActualCounting OQ14.RestrictedTEPassageTransfer
  OQ14.RestrictedTEActualSquare OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEPartnerSmallness OQ14.ChannelMaterialThroughput OQ14.RestrictedTEActualPiecewise
  OQ14.RestrictedTEBackgroundOutside

/-! ### Geometry of the dilated device -/

/-- The sphere heights `ysq` of half-side `k L` are `k` times those of half-side `L`. -/
theorem ysq_mul (N : ℕ) (k L : ℝ) (l : Fin N) : ysq N (k * L) l = k * ysq N L l := by
  unfold ysq
  ring

/-- The point `hpoint` of the dilated data is the dilation of the point. -/
theorem hpoint_smul {ι : Type*} (k r0 : ℝ) (y : ι → ℝ) (l : ι) :
    hpoint (k * r0) (fun l => k * y l) l = k • hpoint r0 y l := by
  ext i
  fin_cases i <;> simp [hpoint]

/-- The point above a plane point commutes with the dilation. -/
theorem abovePoint_smul (k : ℝ) (c : PlaneInverseCube.Plane) (t : ℝ) :
    abovePoint (k • c) (k * t) = k • abovePoint c t := by
  ext i
  fin_cases i <;> simp [abovePoint]

/-- **The k-frequency device is the unit-frequency device dilated by `1 / k`.**  The sphere centre of the device of
half-side `k L` at the gain `a` and height `h a` is `k` times the sphere centre of the device of half-side `L` at
height `h / k * a`. -/
theorem devPos_scale (k : ℝ) (hk : 0 < k) (N : ℕ) (L h a : ℝ) (l : Fin N) :
    abovePoint (hpoint (-(k * L)) (ysq N (k * L)) l) (h * a) =
      k • abovePoint (hpoint (-L) (ysq N L) l) (h / k * a) := by
  have h1 : -(k * L) = k * (-L) := by ring
  have h2 : ysq N (k * L) = fun l => k * ysq N L l := funext (ysq_mul N k L)
  have h3 : h * a = k * (h / k * a) := by
    field_simp
  rw [h1, h2, hpoint_smul, h3, abovePoint_smul]

/-! ### The final k-frequency counting theorem -/

/-- **Counted subspaces at an arbitrary frequency.**  For every frequency `k > 0`, every `εp > 1`, every `N`, every
window `0 < η < δ`, every `τ ≤ 1` and every half-side `L > 0` there are device parameters and an orthonormal family
of `N` finite TE inputs such that: the k-frequency inputs (the amplitude-normalized dilations of the finite TE
incident fields) are vacuum weak Maxwell pairs at frequency `k` whose limiting inward power is `physicalPower`; the
k-frequency device coefficient `scaleCoeff k (pairedCoeff ..)` (the unit-frequency device of half-side `k L`
dilated by `1 / k`: shells of radii `R_r / k`, `X_r / k`, spheres of radius `ρ a_n / k` at height `h a_n / k` above
the points `(-L, y_l)`, see `devPos_scale`) has dielectric values in `[1, εp]` for every gain index and all large
shell indices; eventually in the gain and shell indices the span is a counted subspace through the square of
half-side `L` for the plane flux of the dilated device fields with the scattering map, power and thresholds
unchanged; and eventually in `n`, for every input, eventually in `r`, the dilated physical fields are a weak Maxwell
pair at frequency `k` with the dilated dielectric, are identified with the dilated space fields, and the counted
plane fields are their plane values off the circle of radius `radius r / k`.  Derived from
`actual_counted_subspaces_device` at half-side `k L` by the scaling lemmas; the k-frequency fields are dilations of
the unit-frequency fields, not re-solved volume equations (see reviews/frequency_scaling_design.md). -/
theorem counted_subspaces_at_frequency (k : ℝ) (hk : 0 < k) (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ)
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
          ∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≠ RadialPhaseLimit.radius r / k →
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
                (MaxwellPlaneTail.planePoint ξ)) := by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6⟩ :=
    OQ14.RestrictedTEActualDevice.actual_counted_subspaces_device εp hεp N η δ hη hηδ τ hτ (k * L)
      (mul_pos hk hL)
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, ?_, ?_, ?_, ?_⟩
  · intro a
    exact ⟨incident_testMaxwell_scale k hk a, scaledInwardPower_limit k hk a⟩
  · intro n
    filter_upwards [h5 n] with r hr
    obtain ⟨hb, hd⟩ := hr
    refine ⟨hb, fun x => ?_⟩
    rw [dielectric_scaleCoeff]
    exact hd (k • x)
  · filter_upwards [h6] with n hn
    filter_upwards [hn] with r hr
    exact isCounted_scale k L hk _ _ _ _ τ η δ hr
  · exact device_fields_scaled k hk (-(k * L)) (ysq N (k * L)) ρ χ h R hρ hχ hρh hi q hq

/-- The explicit value formula of the k-frequency device coefficient: the value at the frequency `ξ` is the value of
the unit-frequency coefficient at `k ξ`. -/
theorem counted_subspaces_at_frequency_coefficient (k : ℝ) (c : StaticCoefficient.Coefficient)
    (ξ : VectorFourier.Frequency) : (scaleCoeff k c).value ξ = c.value (k • ξ) :=
  scaleCoeff_value k c ξ

end OQ14.RestrictedTEFrequencyScaling

#print axioms OQ14.RestrictedTEFrequencyScaling.ysq_mul
#print axioms OQ14.RestrictedTEFrequencyScaling.hpoint_smul
#print axioms OQ14.RestrictedTEFrequencyScaling.abovePoint_smul
#print axioms OQ14.RestrictedTEFrequencyScaling.devPos_scale
#print axioms OQ14.RestrictedTEFrequencyScaling.counted_subspaces_at_frequency
#print axioms OQ14.RestrictedTEFrequencyScaling.counted_subspaces_at_frequency_coefficient
