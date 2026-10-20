import PiecewiseMaxwellUniqueness
import VolumeAnalyticAlternative

/-! # Actual positive-real regularity of the partition-material volume inverse -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.PiecewiseRealSpectrum

open MeasureTheory Metric Set OQ14.Maxwell OQ14.PiecewiseMaxwellUniqueness
open scoped Topology

abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

theorem inverse_real_apply (c : Coefficient) (k R : ℝ) (f : VectorL2) :
    Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c (k : ℂ) R) f =
      MaterialField.solution c k R f := by
  rw [ComplexConvolutionAnalytic.volumeBlock_ofReal]
  rfl

section Geometry

variable {ι : Type*} (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (p : Partition ι (MaterialMaxwell.dielectric c))
    (i₀ : ι) (x₀ : Space) (hx₀ : x₀ ∈ p.cell i₀) (hout : R < ‖x₀‖)

include hR hc p i₀ x₀ hx₀ hout

theorem positive_volumeBlock_isUnit (k : ℝ) (hk : 0 < k) :
    IsUnit (ComplexConvolutionAnalytic.volumeBlock c (k : ℂ) R) := by
  rw [ComplexConvolutionAnalytic.volumeBlock_ofReal]
  exact volumeBlock_isUnit c k hk R hR hc p i₀ x₀ hx₀ hout

theorem positive_not_exceptional (k : ℝ) (hk : 0 < k) :
    (k : ℂ) ∉ {z : ℂ | ¬ IsUnit (ComplexConvolutionAnalytic.volumeBlock c z R)} :=
  not_not.mpr (positive_volumeBlock_isUnit c R hR hc p i₀ x₀ hx₀ hout k hk)

theorem exceptional_disjoint_positiveAxis :
    Disjoint {z : ℂ | ¬ IsUnit (ComplexConvolutionAnalytic.volumeBlock c z R)}
      (Complex.ofReal '' Ioi (0 : ℝ)) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨k,hk,rfl⟩
  exact hz (positive_volumeBlock_isUnit c R hR hc p i₀ x₀ hx₀ hout k hk)

theorem inverse_analyticAt_positive (k : ℝ) (hk : 0 < k) :
    AnalyticAt ℂ (fun z => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z R)) (k : ℂ) :=
  VolumeAnalyticAlternative.inverse_analyticAt_of_isUnit c R hR (k : ℂ)
    (positive_volumeBlock_isUnit c R hR hc p i₀ x₀ hx₀ hout k hk)

theorem inverse_analyticOnNhd_positiveAxis :
    AnalyticOnNhd ℂ (fun z => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z R))
      (Complex.ofReal '' Ioi (0 : ℝ)) := by
  rintro z ⟨k,hk,rfl⟩
  exact inverse_analyticAt_positive c R hR hc p i₀ x₀ hx₀ hout k hk

theorem complex_neighborhood_regular (k : ℝ) (hk : 0 < k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (k : ℂ) δ,
      IsUnit (ComplexConvolutionAnalytic.volumeBlock c z R) ∧
      AnalyticAt ℂ (fun w => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c w R)) z := by
  have hopen : IsOpen {z : ℂ | IsUnit (ComplexConvolutionAnalytic.volumeBlock c z R)} :=
    Units.isOpen.preimage (ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR).continuous
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hopen (k : ℂ)
    (positive_volumeBlock_isUnit c R hR hc p i₀ x₀ hx₀ hout k hk)
  exact ⟨δ,hδ,fun z hz => ⟨hball hz,
    VolumeAnalyticAlternative.inverse_analyticAt_of_isUnit c R hR z (hball hz)⟩⟩

theorem inverse_apply_analyticAt_positive (k : ℝ) (hk : 0 < k) (f : VectorL2) :
    AnalyticAt ℂ (fun z => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z R) f) (k : ℂ) :=
  ((ContinuousLinearMap.apply ℂ VectorL2 f).analyticAt
    (Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c (k : ℂ) R))).comp
    (f := fun z => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z R))
    (inverse_analyticAt_positive c R hR hc p i₀ x₀ hx₀ hout k hk)

end Geometry

end OQ14.PiecewiseRealSpectrum

#print axioms OQ14.PiecewiseRealSpectrum.inverse_real_apply
#print axioms OQ14.PiecewiseRealSpectrum.positive_volumeBlock_isUnit
#print axioms OQ14.PiecewiseRealSpectrum.positive_not_exceptional
#print axioms OQ14.PiecewiseRealSpectrum.exceptional_disjoint_positiveAxis
#print axioms OQ14.PiecewiseRealSpectrum.inverse_analyticAt_positive
#print axioms OQ14.PiecewiseRealSpectrum.inverse_analyticOnNhd_positiveAxis
#print axioms OQ14.PiecewiseRealSpectrum.complex_neighborhood_regular
#print axioms OQ14.PiecewiseRealSpectrum.inverse_apply_analyticAt_positive
