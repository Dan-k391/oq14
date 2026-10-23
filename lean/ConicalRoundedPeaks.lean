import ConicalTipRounding

/-! Explicit tip-rounded conical coefficients with fixed contrast and volume peaks. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalRoundedPeaks
open MeasureTheory Set Metric Filter OQ14.ConicalStaticVolume OQ14.ConicalTipRounding
open scoped Topology
abbrev Space := Maxwell.Space

def permittivity (p : Data) (n : ℕ) (x : Space) : ℝ :=
  1+(rounded (coefficient p) n).value (VectorFourier.coordinateMap x)

def field (p : Data) (n : ℕ) (k : ℝ) : VectorFourier.VectorL2 :=
  MaterialVolumeLimit.volumeField (rounded (coefficient p) n) k p.cutoff.rOut
    (ConicalDynamicVolume.incident p k)

theorem permittivity_bounds (p : Data) (n : ℕ) (x : Space) :
    permittivity p n x ∈ Icc (1 : ℝ) (1+p.contrast) := by
  have h0 := (rounded (coefficient p) n).nonnegative (VectorFourier.coordinateMap x)
  have h1 := (rounded (coefficient p) n).bounded (VectorFourier.coordinateMap x)
  change (rounded (coefficient p) n).value (VectorFourier.coordinateMap x) ≤ p.contrast at h1
  constructor <;> unfold permittivity <;> linarith

theorem permittivity_one_inner (p : Data) (n : ℕ) (x : Space) (hx : ‖x‖ ≤ radius n) :
    permittivity p n x=1 := by
  simp only [permittivity,rounded_zero_inner _ n x hx,add_zero]

theorem permittivity_eq_outer (p : Data) (n : ℕ) (x : Space) (hx : 2*radius n ≤ ‖x‖) :
    permittivity p n x=ConicalAnnularSource.dielectric p.cutoff p.contrast p.threshold x := by
  rw [permittivity,rounded_eq_outer _ n x hx,coefficient_spatial]
  ring

theorem permittivity_smooth_near_tip (p : Data) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (permittivity p n) (ball (0 : Space) (radius n)) :=
  contDiffOn_const.add (rounded_smooth_near_tip (coefficient p) n)

theorem permittivity_one_outside (p : Data) (n : ℕ) (x : Space)
    (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) : permittivity p n x=1 := by
  simp only [permittivity,conical_common_support p n x hx,add_zero]

theorem field_tendsto (p : Data) (k : ℝ)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast p.cutoff.rOut) :
    Tendsto (fun n => field p n k) atTop (𝓝 (ConicalDynamicVolume.field p k)) := by
  have hh := MaterialVolumeLimit.volumeField_tendsto (rounded (coefficient p)) (coefficient p)
    p.contrast k p.cutoff.rOut p.cutoff.rOut_pos.le (fun _ => le_rfl) le_rfl
    (rounded_ae_tendsto (coefficient p)) hk (ConicalDynamicVolume.incident p k)
  rwa [ConicalVolumePeaks.volumeField_eq] at hh

theorem explicit_rounded_peaks (p : Data) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ MaterialVolumeLimit.commonRadius p.contrast p.cutoff.rOut ∧
      ∀ k : ℝ, 0 < k → k < δ → ∀ R : ℝ, 0 < R → R ≤ p.cutoff.rIn →
      ∃ i : Fin 3, ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
        0 < (volume.restrict (ball (0 : Space) R))
          {x | M < ‖NewtonL2.physicalCoordinate (field p n k) i x‖} :=
  ConicalVolumePeaks.eventually_positive_physical_peaks p hν (rounded (coefficient p))
    p.contrast (fun _ => le_rfl) le_rfl (rounded_ae_tendsto (coefficient p))

theorem exists_prescribed_contrast (χ : ContDiffBump (0 : Space)) (d t : ℝ)
    (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ (p : Data) (δ : ℝ), p.cutoff=χ ∧ p.contrast=d ∧ p.threshold=t ∧
      p.exponent ∈ Ioo (0 : ℝ) 1 ∧ 0 < δ ∧
      δ ≤ MaterialVolumeLimit.commonRadius d χ.rOut ∧
      (∀ n x, permittivity p n x ∈ Icc (1 : ℝ) (1+d)) ∧
      (∀ n x, ‖x‖ ≤ radius n → permittivity p n x=1) ∧
      (∀ n x, x ∉ closedBall (0 : Space) χ.rOut → permittivity p n x=1) ∧
      ∀ k : ℝ, 0 < k → k < δ → ∀ R : ℝ, 0 < R → R ≤ χ.rIn →
      ∃ i : Fin 3, ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
        0 < (volume.restrict (ball (0 : Space) R))
          {x | M < ‖NewtonL2.physicalCoordinate (field p n k) i x‖} := by
  obtain ⟨p,hχ,hd',ht',hν,_⟩ := ConicalFamily.exists_data χ d t hd ht ht1
  obtain ⟨δ,hδ,hδb,hpeaks⟩ := explicit_rounded_peaks p hν
  refine ⟨p,δ,hχ,hd',ht',⟨p.exponent_pos,hν⟩,hδ,?_,?_,?_,?_,?_⟩
  · simpa only [hχ,hd'] using hδb
  · intro n x
    simpa only [hd'] using permittivity_bounds p n x
  · exact fun n x hx => permittivity_one_inner p n x hx
  · intro n x hx
    exact permittivity_one_outside p n x (by rwa [hχ])
  · intro k hk hkd R hR hRR
    exact hpeaks k hk hkd R hR (by rwa [hχ])

end OQ14.ConicalRoundedPeaks

#print axioms OQ14.ConicalRoundedPeaks.permittivity_bounds
#print axioms OQ14.ConicalRoundedPeaks.permittivity_one_inner
#print axioms OQ14.ConicalRoundedPeaks.permittivity_eq_outer
#print axioms OQ14.ConicalRoundedPeaks.permittivity_smooth_near_tip
#print axioms OQ14.ConicalRoundedPeaks.permittivity_one_outside
#print axioms OQ14.ConicalRoundedPeaks.field_tendsto
#print axioms OQ14.ConicalRoundedPeaks.explicit_rounded_peaks
#print axioms OQ14.ConicalRoundedPeaks.exists_prescribed_contrast
