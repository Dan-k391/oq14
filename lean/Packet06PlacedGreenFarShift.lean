import Packet06PlacedGreenOutgoing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06PlacedGreenFarShift
open Complex MeasureTheory Metric Filter Maxwell ComplexGreenKernel DyadicRadiation ComplexDyadicOutgoing
open scoped Topology InnerProductSpace

def shiftedAmplitude (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorFourier.VectorL2)
    (n b : Space) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, ∫ y, DynamicVolume.source c u j y *
    ((Complex.exp (-I*z*(⟪n,y+b⟫_ℝ : ℝ)) / (4*Real.pi)) * (z^2 * transverse n i j))

/-- Outgoing dyadic volume fields have their ordinary origin-ray limit after a fixed translation. -/
theorem exterior_shifted_limit (c : StaticCoefficient.Coefficient) (z : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (n b : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => (r : ℂ) * Complex.exp (-I*z*r) *
      ComplexExteriorIntegral.field c z u (r • n-b) i) atTop (𝓝 (shiftedAmplitude c z u n b i)) := by
  let R' := R+‖b‖
  have hR' : 0 ≤ R' := add_nonneg hR (norm_nonneg b)
  have hlim (j : Fin 3) : Tendsto (fun r : ℝ => ∫ y,
      DynamicVolume.source c u j y * ((r : ℂ) * Complex.exp (-I*z*r) *
        ComplexDynamicKernel.dyadic z (r • n-(y+b)) i j)) atTop
      (𝓝 (∫ y, DynamicVolume.source c u j y *
        ((Complex.exp (-I*z*(⟪n,y+b⟫_ℝ : ℝ)) / (4*Real.pi)) * (z^2 * transverse n i j)))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun y => ‖DynamicVolume.source c u j y‖ *
        ((2 * Real.exp (‖z‖*R') / (4*Real.pi)) * (2*‖z‖^2 + 4*(‖z‖+1))))
    · apply Eventually.of_forall
      intro r
      apply (DynamicVolume.source_integrable c u R hc j).aestronglyMeasurable.mul
      apply AEStronglyMeasurable.const_mul
      exact ((dyadic_measurable z i j).comp (measurable_const.sub (measurable_id.add_const b))).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (2*R'), eventually_ge_atTop (2 : ℝ)] with r hr hr2
      filter_upwards with y
      by_cases hy : y ∈ closedBall (0 : Space) R
      · have hy' : y+b ∈ closedBall (0 : Space) R' := by
          simp only [mem_closedBall,dist_zero_right] at hy ⊢
          exact (norm_add_le y b).trans (add_le_add_right hy _)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (scaled_dyadic_bound z R' r hR' hr hr2 n (y+b) hn hy' i j) (norm_nonneg _)
      · simp [DynamicVolume.source_zero c u R hc j y hy]
    · exact (DynamicVolume.source_integrable c u R hc j).norm.mul_const _
    · filter_upwards with y
      exact tendsto_const_nhds.mul (scaled_dyadic_limit z n (y+b) hn i j)
  have h := tendsto_finset_sum Finset.univ (fun j _ => hlim j)
  apply h.congr'
  filter_upwards with r
  simp only [ComplexExteriorIntegral.field, Finset.mul_sum,shiftedAmplitude]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  have he : r • n-b-y = r • n-(y+b) := by abel
  rw [he]
  ring

theorem electric_shifted_limit (c : StaticCoefficient.Coefficient) (z : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (n b : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => (r : ℂ) * Complex.exp (-I*z*r) *
      Packet06GlobalField.electric c z R u (r • n-b) i) atTop (𝓝 (shiftedAmplitude c z u n b i)) := by
  apply (exterior_shifted_limit c z R hR u hc n b hn i).congr'
  filter_upwards [eventually_gt_atTop (R+1+‖b‖),eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have hnorm : ‖r • n‖ = r := by simp [norm_smul,hn,abs_of_pos hr0]
  have htri : ‖r • n‖ ≤ ‖r • n-b‖+‖b‖ := by
    simpa using norm_add_le (r • n-b) b
  have hout : ¬ ‖r • n-b‖ ≤ R+1 := by rw [hnorm] at htri; linarith
  simp only [Packet06GlobalField.electric, if_neg hout]

theorem projected_shifted_limit (c : StaticCoefficient.Coefficient) (S J : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J)
    (z : ℂ) (f : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (n b : Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => (r : ℂ)*Complex.exp (-I*z*r)*
      Packet06ProjectedGlobal.field c S J z f (r • n-b) i) atTop
      (𝓝 ((z^2)⁻¹ * (shiftedAmplitude (Packet06ExternalFreeMaxwell.supportCoefficient J) z
          (Packet06ProjectedGreen.project f) n b i +
        shiftedAmplitude c z (Ring.inverse (Packet06MaterialSector.pencil c S z)
          (Packet06ExternalResidue.incidentDatum c S J z (Packet06ProjectedGreen.project f))) n b i))) := by
  have h1 := electric_shifted_limit (Packet06ExternalFreeMaxwell.supportCoefficient J) z J hJ
    (Packet06ProjectedGreen.project f) (Packet06ExternalFreeMaxwell.supportCoefficient_support J) n b hn i
  have h2 := electric_shifted_limit c z S hS (Ring.inverse (Packet06MaterialSector.pencil c S z)
    (Packet06ExternalResidue.incidentDatum c S J z (Packet06ProjectedGreen.project f))) hc n b hn i
  have h := (h1.add h2).const_mul ((z^2)⁻¹)
  apply h.congr'
  filter_upwards with r
  dsimp only [Packet06ProjectedGlobal.field]
  ring

#print axioms OQ14.Packet06PlacedGreenFarShift.projected_shifted_limit
#print axioms OQ14.Packet06PlacedGreenFarShift.electric_shifted_limit
#print axioms OQ14.Packet06PlacedGreenFarShift.exterior_shifted_limit
end OQ14.Packet06PlacedGreenFarShift
