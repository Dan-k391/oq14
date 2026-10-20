import ComplexConvolutionAnalytic
import LocalFredholmReduction
import AnalyticCompactInverse
import Mathlib.Topology.MetricSpace.Bounded

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace OQ14.VolumeAnalyticAlternative

open Metric OQ14.DynamicConvolution OQ14.ComplexConvolutionAnalytic
open OQ14.StaticCoefficient (Coefficient)
open scoped Topology

theorem volumeBlock_isUnit_iff_pencil (c : Coefficient) (k : ℂ) (R : ℝ) :
    IsUnit (volumeBlock c k R) ↔ IsUnit (pencil c k R) := by
  constructor
  · intro hu
    have h := (StaticNewton.volumeBlock_isUnit c).ringInverse.mul hu
    rwa [preconditioned_eq] at h
  · intro hu
    rw [volumeBlock_factor]
    exact (StaticNewton.volumeBlock_isUnit c).mul hu

theorem pencil_punctured_isUnit (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z₀ : ℂ) : ∀ᶠ z in 𝓝[≠] z₀, IsUnit (pencil c z R) := by
  have hbase : ∃ z : ℂ, IsUnit (1-compactPart c z R) :=
    ⟨0, by rw [compactPart_zero, sub_zero]; exact isUnit_one⟩
  simpa only [pencil, CompactPerturbation.defect] using
    LocalFredholmReduction.anchored_punctured_isUnit (fun z => compactPart c z R)
      (compactPart_differentiable c R hR) (fun z => compactPart_compact c z R hc) hbase z₀

theorem volumeBlock_punctured_isUnit (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z₀ : ℂ) : ∀ᶠ z in 𝓝[≠] z₀, IsUnit (volumeBlock c z R) :=
  (pencil_punctured_isUnit c R hR hc z₀).mono
    (fun z hz => (volumeBlock_isUnit_iff_pencil c z R).mpr hz)

theorem exceptional_isClosed (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) :
    IsClosed {z : ℂ | ¬ IsUnit (volumeBlock c z R)} :=
  (Units.isOpen.preimage (volumeBlock_differentiable c R hR).continuous).isClosed_compl

theorem exceptional_discrete (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    DiscreteTopology {z : ℂ | ¬ IsUnit (volumeBlock c z R)} := by
  apply discreteTopology_subtype_iff.mpr
  intro z _
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [volumeBlock_punctured_isUnit c R hR hc z] with w hw
  exact fun hn => hn hw

theorem finite_exceptional_in_bounded (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (K : Set ℂ) (hK : Bornology.IsBounded K) :
    Set.Finite (K ∩ {z : ℂ | ¬ IsUnit (volumeBlock c z R)}) := by
  letI := exceptional_discrete c R hR hc
  exact Metric.finite_isBounded_inter_isClosed hK (exceptional_isClosed c R hR)

theorem inverse_factor (c : Coefficient) (k : ℂ) (R : ℝ) (hp : IsUnit (pencil c k R)) :
    Ring.inverse (volumeBlock c k R) =
      Ring.inverse (pencil c k R) * Ring.inverse (StaticNewton.volumeBlock c) := by
  have hv := (volumeBlock_isUnit_iff_pencil c k R).mpr hp
  have hh : volumeBlock c k R *
      (Ring.inverse (pencil c k R) * Ring.inverse (StaticNewton.volumeBlock c)) = 1 := by
    rw [volumeBlock_factor, mul_assoc,
      ← mul_assoc (pencil c k R) (Ring.inverse (pencil c k R)),
      Ring.mul_inverse_cancel _ hp, one_mul,
      Ring.mul_inverse_cancel _ (StaticNewton.volumeBlock_isUnit c)]
  calc
    Ring.inverse (volumeBlock c k R) = Ring.inverse (volumeBlock c k R) * 1 := by rw [mul_one]
    _ = Ring.inverse (volumeBlock c k R) *
        (volumeBlock c k R *
          (Ring.inverse (pencil c k R) * Ring.inverse (StaticNewton.volumeBlock c))) := by rw [hh]
    _ = _ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hv, one_mul]

theorem pencil_inverse_meromorphicAt (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z₀ : ℂ) : MeromorphicAt (fun z => Ring.inverse (pencil c z R)) z₀ := by
  have hbase : ∃ z : ℂ, IsUnit (1-compactPart c z R) :=
    ⟨0, by rw [compactPart_zero, sub_zero]; exact isUnit_one⟩
  simpa only [pencil, CompactPerturbation.defect] using
    AnalyticCompactInverse.inverse_meromorphicAt (fun z => compactPart c z R)
      (compactPart_differentiable c R hR) (fun z => compactPart_compact c z R hc) hbase z₀

theorem inverse_meromorphicAt (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z₀ : ℂ) : MeromorphicAt (fun z => Ring.inverse (volumeBlock c z R)) z₀ := by
  have hh := MeromorphicOperator.clm_comp (fun z => Ring.inverse (pencil c z R))
    (fun _ : ℂ => Ring.inverse (StaticNewton.volumeBlock c)) z₀
      (pencil_inverse_meromorphicAt c R hR hc z₀)
      (MeromorphicAt.const (Ring.inverse (StaticNewton.volumeBlock c)) z₀)
  apply hh.congr
  filter_upwards [pencil_punctured_isUnit c R hR hc z₀] with z hz
  exact (inverse_factor c z R hz).symm

theorem inverse_meromorphicOn (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    MeromorphicOn (fun z => Ring.inverse (volumeBlock c z R)) Set.univ :=
  fun z _ => inverse_meromorphicAt c R hR hc z

theorem inverse_analyticAt_of_isUnit (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) (z₀ : ℂ)
    (hu : IsUnit (volumeBlock c z₀ R)) :
    AnalyticAt ℂ (fun z => Ring.inverse (volumeBlock c z R)) z₀ :=
  (analyticOnNhd_inverse (𝕜 := ℂ) _ hu).comp (f := fun z : ℂ => volumeBlock c z R)
    (volumeBlock_analyticAt c z₀ R hR)

theorem inverse_order_negative (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z₀ : ℂ) (hnot : ¬ IsUnit (volumeBlock c z₀ R)) :
    (inverse_meromorphicAt c R hR hc z₀).order < 0 := by
  by_contra hnegative
  obtain ⟨C, hC⟩ := (inverse_meromorphicAt c R hR hc z₀).tendsto_nhds_of_order_nonneg
    (le_of_not_gt hnegative)
  have hAt := (volumeBlock_analyticAt c z₀ R hR).continuousAt.tendsto.mono_left
    (show 𝓝[≠] z₀ ≤ 𝓝 z₀ from nhdsWithin_le_nhds)
  have hu := volumeBlock_punctured_isUnit c R hR hc z₀
  have hleft : volumeBlock c z₀ R * C = 1 := by
    have ht : Filter.Tendsto (fun z => volumeBlock c z R * Ring.inverse (volumeBlock c z R))
        (𝓝[≠] z₀) (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hu] with z hz
      exact (Ring.mul_inverse_cancel _ hz).symm
    exact tendsto_nhds_unique (hAt.mul hC) ht
  have hright : C * volumeBlock c z₀ R = 1 := by
    have ht : Filter.Tendsto (fun z => Ring.inverse (volumeBlock c z R) * volumeBlock c z R)
        (𝓝[≠] z₀) (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hu] with z hz
      exact (Ring.inverse_mul_cancel _ hz).symm
    exact tendsto_nhds_unique (hC.mul hAt) ht
  exact hnot ⟨⟨volumeBlock c z₀ R, C, hleft, hright⟩, rfl⟩

end OQ14.VolumeAnalyticAlternative

#print axioms OQ14.VolumeAnalyticAlternative.volumeBlock_isUnit_iff_pencil
#print axioms OQ14.VolumeAnalyticAlternative.pencil_punctured_isUnit
#print axioms OQ14.VolumeAnalyticAlternative.volumeBlock_punctured_isUnit
#print axioms OQ14.VolumeAnalyticAlternative.exceptional_isClosed
#print axioms OQ14.VolumeAnalyticAlternative.exceptional_discrete
#print axioms OQ14.VolumeAnalyticAlternative.finite_exceptional_in_bounded
#print axioms OQ14.VolumeAnalyticAlternative.inverse_factor
#print axioms OQ14.VolumeAnalyticAlternative.pencil_inverse_meromorphicAt
#print axioms OQ14.VolumeAnalyticAlternative.inverse_meromorphicAt
#print axioms OQ14.VolumeAnalyticAlternative.inverse_meromorphicOn
#print axioms OQ14.VolumeAnalyticAlternative.inverse_analyticAt_of_isUnit
#print axioms OQ14.VolumeAnalyticAlternative.inverse_order_negative
