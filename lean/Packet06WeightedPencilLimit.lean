import Packet06WeightedRemainderLimit
import Mathlib.Analysis.Complex.LocallyUniformLimit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06WeightedPencilLimit
open Filter Set MeasureTheory Metric OQ14.StaticCoefficient OQ14.Packet06WeightedStaticLimit
open scoped Topology
abbrev V := VectorFourier.VectorL2
abbrev Space := FourierL2.Space

theorem compactPart_uniform (c : ℕ → Coefficient) (c₀ : Coefficient) (D R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (n : ℕ) (x : Space), x ∉ closedBall 0 R → (c n).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : Space, x ∉ closedBall 0 R → c₀.value (VectorFourier.coordinateMap x) = 0)
    (A : Set ℂ) (hA : IsCompact A) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ A,
      ‖ComplexConvolutionAnalytic.compactPart (c n) z R -
        ComplexConvolutionAnalytic.compactPart c₀ z R‖ < ε := by
  let T : ℕ → V →L[ℂ] V := fun n => Ring.inverse (weightedBlock (c n)) - Ring.inverse (weightedBlock c₀)
  let K : ℂ → V →L[ℂ] V := fun z => ComplexConvolutionAnalytic.weightedRemainder c₀ z R
  have hbT (n : ℕ) : ‖T n‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by
      have h1 := weightedBlock_inverse_norm_le (c n)
      have h2 := weightedBlock_inverse_norm_le c₀
      linarith)
  have hsT (f : V) : Tendsto (fun n => T n f) atTop (𝓝 0) := by
    change Tendsto (fun n => Ring.inverse (weightedBlock (c n)) f - Ring.inverse (weightedBlock c₀) f) atTop (𝓝 0)
    simpa using (weightedBlock_inverse_strong c c₀ D hb hb₀ ha f).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => Ring.inverse (weightedBlock c₀) f) atTop (𝓝 (Ring.inverse (weightedBlock c₀) f)))
  have hcont : ContinuousOn K A :=
    (ComplexConvolutionAnalytic.weightedRemainder_differentiable c₀ R hR).continuous.continuousOn
  have hcompact (z : ℂ) : IsCompactOperator (K z) :=
    ComplexConvolutionAnalytic.weightedRemainder_compact c₀ z R hc₀
  have hsecond := Packet06StrongCompact.compact_family_uniform T 2 (by norm_num)
    hbT hsT K A hA hcont (fun z _ => hcompact z)
  have hfirst := Packet06WeightedRemainderLimit.weightedRemainder_uniform c c₀ D R hR hb hb₀ ha hc hc₀ A hA
  intro ε hε
  filter_upwards [hfirst (ε/2) (by positivity), hsecond (ε/2) (by positivity)] with n hn1 hn2 z hz
  have h1 := hn1 z hz
  have h2 : ‖T n * K z‖ < ε/2 := hn2 z hz
  have he : ComplexConvolutionAnalytic.compactPart (c n) z R -
      ComplexConvolutionAnalytic.compactPart c₀ z R =
      Ring.inverse (weightedBlock (c n)) *
        (ComplexConvolutionAnalytic.weightedRemainder (c n) z R - K z) + T n * K z := by
    dsimp [ComplexConvolutionAnalytic.compactPart,T,K]
    rw [StaticNewton.volumeBlock_eq,StaticNewton.volumeBlock_eq]
    noncomm_ring
  rw [he]
  have hterm : ‖Ring.inverse (weightedBlock (c n)) *
      (ComplexConvolutionAnalytic.weightedRemainder (c n) z R - K z)‖ < ε/2 := by
    calc
      _ ≤ ‖Ring.inverse (weightedBlock (c n))‖ *
          ‖ComplexConvolutionAnalytic.weightedRemainder (c n) z R - K z‖ := norm_mul_le _ _
      _ ≤ ‖ComplexConvolutionAnalytic.weightedRemainder (c n) z R - K z‖ := by
        simpa using mul_le_mul_of_nonneg_right (weightedBlock_inverse_norm_le (c n)) (norm_nonneg _)
      _ < ε/2 := h1
  linarith [norm_add_le (Ring.inverse (weightedBlock (c n)) *
    (ComplexConvolutionAnalytic.weightedRemainder (c n) z R - K z)) (T n * K z)]

theorem compactPart_locally_uniform (c : ℕ → Coefficient) (c₀ : Coefficient) (D R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (n : ℕ) (x : Space), x ∉ closedBall 0 R → (c n).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : Space, x ∉ closedBall 0 R → c₀.value (VectorFourier.coordinateMap x) = 0) :
    TendstoLocallyUniformlyOn (fun n z => ComplexConvolutionAnalytic.compactPart (c n) z R)
      (fun z => ComplexConvolutionAnalytic.compactPart c₀ z R) atTop univ := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mpr
  intro A _ hA
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have h := compactPart_uniform c c₀ D R hR hb hb₀ ha hc hc₀ A hA ε hε
  filter_upwards [h] with n hn z hz
  simpa only [dist_eq_norm,norm_sub_rev] using hn z hz
#print axioms OQ14.Packet06WeightedPencilLimit.compactPart_uniform
#print axioms OQ14.Packet06WeightedPencilLimit.compactPart_locally_uniform
end OQ14.Packet06WeightedPencilLimit
