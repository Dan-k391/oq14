# Fixed-input transfer through the rounded family — scope and author verification

Read-only survey of `lean/` followed by one new module, `lean/ConicalFixedInputTransfer.lean`. Nothing existing was edited.

## (a) Which API carries which input

Two different incident-field APIs coexist.

1. Internal-source (annular) illumination: `ConicalDynamicVolume.incident p k` (and the separated variant `ConicalSeparatedDynamic.incident p a k`) is a single fixed vector in `VectorL2` determined by `p` (and `a`, `k`). The rounded families `ConicalRoundedPeaks.field p n k`, `ConicalRoundedMaxwell.*`, `ConicalSeparatedRounding.field p a k n` drive the rounded material with this incident. There is no free input in these theorems.
2. Entire incident fields: `ConicalEntireGauge.Incident k` (smooth entire vacuum Maxwell pair). The fixed angular input `FiniteAngularHerglotz.incident k d` is of this type. `ConicalEntireGauge.electric/system` use it with the unrounded separated material `ConicalSeparatedSource.material p a`. Before this work no theorem applied a rounded material to an `Incident` (only to finite plane sums `WaveIndex →₀ ℂ`, in `ConicalFiniteIlluminationPeaks`).

## (b)(i) Theorems that already have the input fixed outside rounding and threshold quantifiers

* `OQ14.ConicalRoundedPeaks.explicit_rounded_peaks`: `∃ δ, 0<δ ∧ δ ≤ commonRadius p.contrast p.cutoff.rOut ∧ ∀ k, 0<k → k<δ → ∀ R, 0<R → R ≤ p.cutoff.rIn → ∃ i : Fin 3, ∀ M : ℝ, ∀ᶠ n : ℕ in atTop, 0 < (volume.restrict (ball 0 R)) {x | M < ‖NewtonL2.physicalCoordinate (field p n k) i x‖}`. Incident is the fixed annular one; `i` is outside `M` and `n`.
* `OQ14.ConicalRoundedPeaks.field_tendsto` and `OQ14.ConicalSeparatedRounding.field_tendsto`/`ballField_tendsto`/`eventually_avoids_bound`: convergence of the rounded fields to the limit field for the fixed (annular or separated) incident, `Tendsto (field p a k) atTop (𝓝 (ConicalSeparatedDynamic.field p a k))`; `eventually_avoids_bound` fixes `i` and the unboundedness hypothesis before `M` and `n`.
* `OQ14.ConicalRoundedHotspot.physical_electric_peaks`: `∀ M, ∀ᶠ n` with the fixed annular incident.
* `OQ14.ConicalFixedAngularInput.positive_frequency_fixed_input` and `OQ14.ConicalFixedFiniteInput.positive_frequency_fixed_input`: `∃ δ, 0<δ ∧ ∀ k, 0<k → k<δ → ∃ hfreq c J hJ heJ q, c≠0 ∧ q≠0 ∧ projected ... =ᵐ ...`. The input `c` is chosen per `k`, and no rounding level or threshold appears. These do not mention the rounded family at all.

## (b)(ii) Theorems that select the input inside the quantifiers (need a fixed-input version)

* `OQ14.ConicalFiniteIlluminationPeaks.eventually_finite_high_superlevel`: conclusion `∀ᶠ n : ℕ in atTop, ∃ b : WaveIndex →₀ ℂ, TestMaxwell ... ∧ 0 < (volume.restrict (ball 0 R)) {x | M < ‖electric p a k n b x‖}` for a given `M`, so `b` is reselected for each `n` and `M`.
* `OQ14.ConicalFiniteIlluminationPeaks.positive_frequency_rounded_finite_peaks`: `... ∀ M : ℝ, ∀ᶠ n : ℕ in atTop, ∃ b : WaveIndex →₀ ℂ, TestMaxwell k (permittivity p a n) (electric p a k n b) (magnetic p a k n b) ∧ 0 < ... {x | M < ‖electric p a k n b x‖}`: same defect.
* `OQ14.ConicalFiniteIlluminationPeaks.positive_frequency_rounded_finite_hcurl_peaks`: same `∃ b` inside `∀ M, ∀ᶠ n`. (Not transferred here; H(curl) membership of the fixed-input rounded fields is not part of this module.)
* The supporting `ConicalSeparatedIllumination.finite_total_approximation` is fine as a lemma but its `∃ b` depends on the tolerance `ε`, which is how the rounding level entered; it is not used by the new module.

## (b)(iii) Proposed (and now proved) transfer statement

`OQ14.ConicalFixedInputTransfer.positive_frequency_fixed_input_rounded_transfer`, copied:

```
theorem positive_frequency_fixed_input_rounded_transfer (p : Data) (a b R : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hR : 0 < R) (hRb : R < b) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ) (hk : 0 < k), k < δ →
      ∃ (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
        (c : ModeIndex →₀ ℂ) (J : Field)
        (hJ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x i))
        (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=
          ConicalEntireGauge.error p a k (FiniteAngularHerglotz.incident k c) i x)
        (q : ℂ), c≠0 ∧ q≠0 ∧
        projected p (system p a b k ha hai hba hk.ne' hfreq (incident k c) J ...).graph
          =ᵐ[volume.restrict (Ioo 0 b)] (fun r => q*power p.exponent r+particular p.exponent (radialCorrection ...) (tangentCorrection ...) r) ∧
        Tendsto (fun n => totalOperator (ConicalSeparatedRounding.material p a n) k a (restricted a (incident k c))) atTop
          (𝓝 (totalOperator (ConicalSeparatedSource.material p a) k a (restricted a (incident k c)))) ∧
        (∀ n : ℕ, MaterialMaxwell.TestMaxwell k (ConicalSeparatedRounding.permittivity p a n)
          (electric p a k n (incident k c)) (magnetic p a k n (incident k c))) ∧
        ∀ R' : ℝ, 0 < R' → R' ≤ b → ∃ i : Fin 3, ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
          0 < (volume.restrict (ball (0 : Space) R'))
            {x | M < ‖electric p a k n (incident k c) x i‖}
```
(`incident k c` is `FiniteAngularHerglotz.incident k c`; the file spells every term out.) The quantifier order is `k`, then `c` (and `J`, `q`), then `R'`, `i`, `M`, `n`: the input is fixed before the rounding level `n`, the peak radius, the coordinate and the threshold. No physical normalization is assumed or claimed: `c` carries no unit-power constraint. A parametric version with `c` arbitrary and the nonzero-coefficient data `q≠0` plus the projected expansion as explicit hypotheses is `rounded_transfer_of_nonzero_coefficient`; those hypotheses are exactly the outputs of `ConicalFixedAngularInput.positive_frequency_fixed_input` (which is also what the combined theorem invokes). Here `electric p a k n I` is the literal `MaterialField.total (ConicalSeparatedRounding.material p a n) k (ConicalMaterialRunge.solutionOperator ... (restricted a I)) I.E`.

Mathematical content added: (1) a hot-spot lemma for an arbitrary `ConicalProjectionData.System` (nonzero singular coefficient implies the compared field is not essentially bounded on any ball of radius at most b), `not_essentially_bounded`; (2) strong convergence of the rounded ball total operators on a fixed `Incident` via the extension-by-zero reduction to `MaterialVolumeLimit.volumeField_tendsto`, `ballField_tendsto`; (3) the rounded fields solve the weak Maxwell system for each `n`, `rounded_maxwell`; (4) the superlevel sets are eventually of positive measure, `eventually_high_superlevel`. The extra smallness `k < commonRadius p.contrast a` is needed for convergence of the rounded family and is included in `δ`.

## Author verification of `lean/ConicalFixedInputTransfer.lean`

Source SHA256 `B37373635BB06AB3F0D796A71CCE6FC5825B79AB21BEA53F5B41BAE82C9E5E86` (20165 bytes). Draft check1 (exit 1): one type-mismatch in `ballField_tendsto` plus two unused-variable warnings; check2 `lean/logs/ConicalFixedInputTransfer-check2.log` exit 0 with no output other than axiom reports. Final/object run `lean/logs/ConicalFixedInputTransfer-final.log` SHA256 `4F88842DAF925CEA04E01E3BC74EBA9F01CBCE80BBFA5D5CA720612B9B688AD8`; exit file `lean/logs/ConicalFixedInputTransfer-final.exit.log` = 0; object `lean/.lake/build/lib/lean/ConicalFixedInputTransfer.olean` 652536 bytes. Eight reports, all `[propext, Classical.choice, Quot.sound]`, no warnings, no `sorryAx`.

Root independent audit pending.
