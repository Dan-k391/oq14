import ConicalCommonDynamic
import ConicalEntireGauge

/-! Exact local dielectric seen by a translated tip in the common material. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalCommonLocal
open MeasureTheory Set Metric
open scoped SchwartzMap
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

omit [DecidableEq ι] in
theorem dielectric_local (i : ι) (hai : a i < (p i).cutoff.rIn) (y : Space)
    (hy : y ∈ closedBall (0 : Space) (a i)) :
    MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
      (center i + y) = ConicalLocalGauss.epsilon (p i) y := by
  have hm : center i + y ∈ ConicalCommonMaterial.materialBall a center i := by
    simpa [ConicalCommonMaterial.materialBall, mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hy
  have ho := ConicalCommonMaterial.material_subset_outer p a center ha i hm
  rw [MaterialMaxwell.dielectric]
  change 1 + (ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep).value
    (VectorFourier.coordinateMap (center i + y)) = _
  rw [ConicalCommonMaterial.coefficient_local p a center B hB hcontrast ha hsep i _ ho]
  change 1 + (ConicalSeparatedSource.material (p i) (a i)).value
    (VectorFourier.coordinateMap (center i + y - center i)) = _
  rw [add_sub_cancel_left, ConicalSeparatedMaxwell.material_spatial_inside (p i) (a i) hai y hy]
  change 1 + (ConicalLocalGauss.epsilon (p i) y - 1) = _
  ring

omit [DecidableEq ι] in
theorem local_gauss (i : ι) (b k : ℝ) (hb : b ≤ a i)
    (hai : a i < (p i).cutoff.rIn) (hk : k ≠ 0) (E H : Maxwell.Field)
    (hM : MaterialMaxwell.TestMaxwell k
      (MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)) E H)
    (f : 𝓢(Space, ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ ball (0 : Space) b) :
    (∑ j : Fin 3, ∫ y : Space, (ConicalLocalGauss.epsilon (p i) y : ℂ) *
      E (center i + y) j * Maxwell.dcoord f y j) = 0 := by
  let g := NewtonConvolution.translate (-center i) f
  have hg : HasCompactSupport (g : Space → ℂ) := by
    apply HasCompactSupport.intro' (isCompact_closedBall (center i) b) isClosed_closedBall
    intro x hx
    change f (x + -center i) = 0
    apply image_eq_zero_of_nmem_tsupport
    intro h
    have hm := hf h
    apply hx
    have hh : x - center i ∈ ball (0 : Space) b := by simpa [sub_eq_add_neg] using hm
    have hn : ‖x - center i‖ < b := by simpa using hh
    simpa only [mem_closedBall, dist_eq_norm] using hn.le
  have h := ConicalFiniteGauge.material_gauss k hk _ E H hM ⟨g, hg⟩
  have he (j : Fin 3) : (∫ x : Space,
      (MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) x : ℂ) *
        E x j * Maxwell.dcoord g x j) =
      ∫ y : Space, (ConicalLocalGauss.epsilon (p i) y : ℂ) * E (center i + y) j * Maxwell.dcoord f y j := by
    have ht := integral_add_right_eq_self (μ := (volume : Measure Space))
      (fun x => (MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) x : ℂ) *
        E x j * Maxwell.dcoord g x j) (center i)
    rw [← ht]
    apply integral_congr_ae
    filter_upwards with y
    have hd : Maxwell.dcoord g (y + center i) j = Maxwell.dcoord f y j := by
      change GradientProjection.pderivative j g (y + center i) = _
      rw [show g = NewtonConvolution.translate (-center i) f from rfl, NewtonConvolution.translate_pderivative]
      simp only [NewtonConvolution.translate_apply, add_neg_cancel_right]
      rfl
    rw [hd]
    by_cases hy : y ∈ ball (0 : Space) b
    · have hya : y ∈ closedBall (0 : Space) (a i) := closedBall_subset_closedBall hb (ball_subset_closedBall hy)
      rw [show y + center i = center i + y by abel, dielectric_local p a center B hB hcontrast ha hsep i hai y hya]
    · have hn : y ∉ tsupport (f : Space → ℂ) := fun ht => hy (hf ht)
      simp [Maxwell.dcoord, fderiv_of_not_mem_tsupport ℝ hn]
  simpa only [he] using h

end OQ14.ConicalCommonLocal
#print axioms OQ14.ConicalCommonLocal.dielectric_local
#print axioms OQ14.ConicalCommonLocal.local_gauss
