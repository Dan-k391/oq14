import CommonBinaryRounding
import ConicalUniformCollar

/-! Uniform exact annular collars for the one common binary material sequence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.CommonBinaryCollar
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

omit [Fintype ι] [DecidableEq ι] in
include ha hsep ha0 in
theorem local_zero_of_other_outer (n : ℕ) (i j : ι) (hij : i ≠ j) (x : Space)
    (hx : x ∈ ConicalCommonMaterial.outer p center i) :
    CommonBinaryRounding.localValue p a center n j x = 0 := by
  have hs := ConicalCommonMaterial.localValue_eq_zero_of_mem_outer p a center ha hsep i j hij x hx
  have hb := ConicalJunctionPhysical.binary_below_original (p j) (a j) (ha0 j) (ha j) n
    (VectorFourier.coordinateMap (x-center j))
  have hn := (ConicalJunctionPhysical.binaryMaterial (p j) (a j) n).nonnegative
    (VectorFourier.coordinateMap (x-center j))
  change CommonBinaryRounding.localValue p a center n j x ≤ ConicalCommonMaterial.localValue p a center j x at hb
  change 0 ≤ CommonBinaryRounding.localValue p a center n j x at hn
  linarith

omit [DecidableEq ι] in
theorem common_local (n : ℕ) (i : ι) (x : Space)
    (hx : x ∈ ConicalCommonMaterial.outer p center i) :
    (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 n).value
      (VectorFourier.coordinateMap x) = CommonBinaryRounding.localValue p a center n i x := by
  simp only [CommonBinaryRounding.coefficient, MeasurableEquiv.symm_apply_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact local_zero_of_other_outer p a center ha hsep ha0 n i j (Ne.symm hji) x hx
  · simp

omit [DecidableEq ι] in
theorem eventually_annuli_agree (r b : ι → ℝ) (hr : ∀ i, 0 < r i) (hb : ∀ i, b i < a i) :
    ∀ᶠ n : ℕ in atTop, ∀ i : ι, ∀ x : Space,
      r i ≤ ‖x-center i‖ → ‖x-center i‖ ≤ b i →
      (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 n).value
        (VectorFourier.coordinateMap x) =
      (ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep).value
        (VectorFourier.coordinateMap x) := by
  have he : ∀ᶠ n : ℕ in atTop, ∀ i : ι, ∀ y : Space,
      r i ≤ ‖y‖ → ‖y‖ ≤ b i →
      (ConicalJunctionPhysical.binaryMaterial (p i) (a i) n).value (VectorFourier.coordinateMap y) =
        (ConicalSeparatedSource.material (p i) (a i)).value (VectorFourier.coordinateMap y) :=
    Filter.eventually_all.mpr (fun i => ConicalUniformCollar.eventually_annulus_agreement
      (p i) (a i) (b i) (r i) (ha0 i) (hr i) (hb i) (ha i))
  filter_upwards [he] with n hn i x hxlo hxhi
  have hx : x ∈ ConicalCommonMaterial.outer p center i := by
    change x ∈ closedBall (center i) (p i).cutoff.rOut
    simp only [mem_closedBall, dist_eq_norm]
    exact hxhi.trans ((hb i).le.trans (ha i))
  rw [common_local p a center B hB hcontrast ha hsep ha0 n i x hx,
    ConicalCommonMaterial.coefficient_local p a center B hB hcontrast ha hsep i x hx]
  exact hn i (x-center i) hxlo hxhi

end OQ14.CommonBinaryCollar
#print axioms OQ14.CommonBinaryCollar.eventually_annuli_agree
