import ConicalJunctionPhysical
import CommonTipRounding

/-! One inward binary material sequence for all disjoint translated conical inclusions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.CommonBinaryRounding
open MeasureTheory Set Metric Filter
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))
  (ha0 : ∀ i, 0 < a i)

def localValue (n : ℕ) (i : ι) (x : Space) : ℝ :=
  (ConicalJunctionPhysical.binaryMaterial (p i) (a i) n).value
    (VectorFourier.coordinateMap (x-center i))

def coefficient (n : ℕ) : StaticCoefficient.Coefficient where
  value ξ := ∑ i, localValue p a center n i (VectorFourier.coordinateMap.symm ξ)
  bound := B
  measurable := (Finset.measurable_sum Finset.univ fun i _ =>
    (ConicalJunctionPhysical.binaryMaterial (p i) (a i) n).measurable.comp
      (VectorFourier.coordinateMap_preserving.measurable.comp
        (continuous_id.sub continuous_const).measurable)).comp VectorFourier.coordinateMap.symm.measurable
  nonnegative ξ := Finset.sum_nonneg fun i _ =>
    (ConicalJunctionPhysical.binaryMaterial (p i) (a i) n).nonnegative _
  bounded ξ := by
    calc
      _ ≤ ∑ i, ConicalCommonMaterial.localValue p a center i (VectorFourier.coordinateMap.symm ξ) := by
        apply Finset.sum_le_sum
        intro i _
        exact ConicalJunctionPhysical.binary_below_original (p i) (a i) (ha0 i) (ha i) n _
      _ ≤ B := ConicalCommonMaterial.sum_bound p a center B hB hcontrast ha hsep _

omit [DecidableEq ι] in
theorem coefficient_below (n : ℕ) (ξ : StaticCoefficient.Space) :
    (coefficient p a center B hB hcontrast ha hsep ha0 n).value ξ ≤
      (ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep).value ξ := by
  apply Finset.sum_le_sum
  intro i _
  exact ConicalJunctionPhysical.binary_below_original (p i) (a i) (ha0 i) (ha i) n _

omit [DecidableEq ι] in
theorem coefficient_support (n : ℕ) (R : ℝ)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (x : Space) (hx : x ∉ closedBall (0 : Space) R) :
    (coefficient p a center B hB hcontrast ha hsep ha0 n).value (VectorFourier.coordinateMap x) = 0 := by
  have hb := coefficient_below p a center B hB hcontrast ha hsep ha0 n (VectorFourier.coordinateMap x)
  have hz := ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep R hR x hx
  have hn := (coefficient p a center B hB hcontrast ha hsep ha0 n).nonnegative (VectorFourier.coordinateMap x)
  linarith

omit [DecidableEq ι] in
theorem coefficient_eventually_eq :
    ∀ᵐ ξ : StaticCoefficient.Space ∂volume, ∀ᶠ n : ℕ in atTop,
      (coefficient p a center B hB hcontrast ha hsep ha0 n).value ξ =
      (ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep).value ξ := by
  have haex : ∀ᵐ x : Space ∂volume, ∀ i, ∀ᶠ n : ℕ in atTop,
      (ConicalJunctionPhysical.binaryMaterial (p i) (a i) n).value
        (VectorFourier.coordinateMap (x-center i)) =
      (ConicalSeparatedSource.material (p i) (a i)).value
        (VectorFourier.coordinateMap (x-center i)) := by
    apply ae_all_iff.mpr
    intro i
    have h := (measurePreserving_add_right (volume : Measure Space) (-center i)).quasiMeasurePreserving.ae
      (ConicalJunctionPhysical.almost_everywhere_binary_matches (p i) (a i) (ha0 i) (ha i))
    simpa only [sub_eq_add_neg] using h
  have haeξ := (MeasurePreserving.symm VectorFourier.coordinateMap VectorFourier.coordinateMap_preserving).quasiMeasurePreserving.ae haex
  filter_upwards [haeξ] with ξ hξ
  have he := Filter.eventually_all.mpr hξ
  filter_upwards [he] with n hn
  simp only [coefficient, ConicalCommonMaterial.coefficient, localValue, ConicalCommonMaterial.localValue]
  exact Finset.sum_congr rfl (fun i _ => hn i)

omit [DecidableEq ι] in
theorem volumeField_tendsto (k R : ℝ) (hR : 0 ≤ R)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius B R) (incident : VectorFourier.VectorL2) :
    Tendsto (fun n => MaterialVolumeLimit.volumeField (coefficient p a center B hB hcontrast ha hsep ha0 n) k R incident)
      atTop (𝓝 (MaterialVolumeLimit.volumeField (ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep) k R incident)) := by
  apply MaterialVolumeLimit.volumeField_tendsto _ _ B k R hR (fun _ => le_rfl) le_rfl _ hk incident
  filter_upwards [coefficient_eventually_eq p a center B hB hcontrast ha hsep ha0] with ξ hξ
  exact tendsto_const_nhds.congr' (hξ.mono (fun _ h => h.symm))

end OQ14.CommonBinaryRounding
#print axioms OQ14.CommonBinaryRounding.coefficient_below
#print axioms OQ14.CommonBinaryRounding.coefficient_support
#print axioms OQ14.CommonBinaryRounding.coefficient_eventually_eq
#print axioms OQ14.CommonBinaryRounding.volumeField_tendsto
