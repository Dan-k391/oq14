import MaxwellWeakTranslation
import WeakPoynting.RegularityBounds

/-! Exact localization commutator for genuine L² difference quotients. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.MaxwellCutoffCommutator
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.MaxwellDifferenceQuotient OQ14.WeakTranslations OQ14.WeakGreen

theorem quotient_ae (u : L2Scalar) (i : Fin 3) (h : ℝ) :
    (fun x => quotient u i h x) =ᵐ[volume]
      fun x => (h : ℂ)⁻¹ * (u (x+h • basis i)-u x) := by
  filter_upwards [Lp.coeFn_smul ((h : ℂ)⁻¹) (translateL2 u (h • basis i)-u),
    Lp.coeFn_sub (translateL2 u (h • basis i)) u, translateL2_ae u (h • basis i)] with x hs hd ht
  change (((h : ℂ)⁻¹ • (translateL2 u (h • basis i)-u) : L2Scalar) : Space → ℂ) x = _
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hd]
  simp only [Pi.sub_apply, ht]

theorem cutoff_quotient_commutator (χ : Test) (u : L2Scalar) (i : Fin 3) (h : ℝ) :
    (fun x => quotient (scaleL2 χ.function χ.regular.continuous χ.compact u) i h x) =ᵐ[volume]
      fun x => χ.function x * quotient u i h x +
        (h : ℂ)⁻¹ * (χ.function (x+h • basis i)-χ.function x) * u (x+h • basis i) := by
  let v := scaleL2 χ.function χ.regular.continuous χ.compact u
  have hscaled := scaleL2_ae χ.function χ.regular.continuous χ.compact u
  have hshift := (measurePreserving_add_right (volume : Measure Space) (h • basis i)).quasiMeasurePreserving.ae hscaled
  filter_upwards [quotient_ae v i h, quotient_ae u i h, hscaled, hshift] with x hv hu hs ht
  change quotient v i h x = _
  rw [hv,hu]
  change (h : ℂ)⁻¹ * (v (x+h • basis i)-v x) = _
  change v x = χ.function x * u x at hs
  change v (x+h • basis i) = χ.function (x+h • basis i)*u (x+h • basis i) at ht
  rw [ht,hs]
  ring

theorem cutoff_difference_bound (χ : Test) (i : Fin 3) (h : ℝ) (hh : h ≠ 0)
    (B : ℝ) (hχ : ∀ j x, ‖dcoord χ.function x j‖ ≤ B) (x : Space) :
    ‖(h : ℂ)⁻¹ * (χ.function (x+h • basis i)-χ.function x)‖ ≤ 3*B := by
  have hder : ∀ y : Space, ‖fderiv ℝ χ.function y‖ ≤ 3*B := by
    intro y
    apply (coordinate_opNorm_le _).trans
    have ht : (∑ j : Fin 3, ‖(fderiv ℝ χ.function y) (basis j)‖) ≤ ∑ _ : Fin 3, B := by
      apply Finset.sum_le_sum
      intro j _
      exact hχ j y
    simpa using ht
  have hdiff := (convex_univ : Convex ℝ (Set.univ : Set Space)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (χ.regular.differentiable (by norm_num)) y)
    (fun y _ => hder y) (Set.mem_univ x) (Set.mem_univ (x+h • basis i))
  have hbasis : ‖basis i‖ = 1 := by simp [basis]
  have hnorm : 0 < ‖h‖ := norm_pos_iff.mpr hh
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hbasis, mul_one] at hdiff
  rw [norm_mul, norm_inv, Complex.norm_real]
  apply (inv_mul_le_iff₀ hnorm).2
  simpa only [Real.norm_eq_abs, mul_comm] using hdiff

def cutoffCoefficient (χ : Test) (i : Fin 3) (h : ℝ) (x : Space) : ℂ :=
  (h : ℂ)⁻¹ * (χ.function (x+h • basis i)-χ.function x)

theorem cutoffSource_memLp (χ : Test) (u : L2Scalar) (i : Fin 3) (h : ℝ) (hh : h ≠ 0)
    (B : ℝ) (hχ : ∀ j x, ‖dcoord χ.function x j‖ ≤ B) :
    MemLp (fun x => cutoffCoefficient χ i h x * translateL2 u (h • basis i) x) 2 volume := by
  have hc : Continuous (cutoffCoefficient χ i h) :=
    continuous_const.mul ((χ.regular.continuous.comp (continuous_id.add continuous_const)).sub χ.regular.continuous)
  apply (Lp.memLp (translateL2 u (h • basis i))).of_le_mul
  · exact hc.measurable.aestronglyMeasurable.mul (Lp.memLp _).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (cutoff_difference_bound χ i h hh B hχ x) (norm_nonneg _)

def cutoffSource (χ : Test) (u : L2Scalar) (i : Fin 3) (h : ℝ) (hh : h ≠ 0)
    (B : ℝ) (hχ : ∀ j x, ‖dcoord χ.function x j‖ ≤ B) : L2Scalar :=
  (cutoffSource_memLp χ u i h hh B hχ).toLp _

theorem cutoffSource_norm (χ : Test) (u : L2Scalar) (i : Fin 3) (h : ℝ) (hh : h ≠ 0)
    (B : ℝ) (hχ : ∀ j x, ‖dcoord χ.function x j‖ ≤ B) :
    ‖cutoffSource χ u i h hh B hχ‖ ≤ 3*B*‖u‖ := by
  have hn : ‖cutoffSource χ u i h hh B hχ‖ ≤ 3*B*‖translateL2 u (h • basis i)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(cutoffSource_memLp χ u i h hh B hχ).coeFn_toLp] with x hx
    rw [show cutoffSource χ u i h hh B hχ x = _ from hx, norm_mul]
    exact mul_le_mul_of_nonneg_right (cutoff_difference_bound χ i h hh B hχ x) (norm_nonneg _)
  simpa only [translateL2_norm] using hn

theorem cutoff_quotient_decomposition (χ : Test) (u : L2Scalar) (i : Fin 3) (h : ℝ) (hh : h ≠ 0)
    (B : ℝ) (hχ : ∀ j x, ‖dcoord χ.function x j‖ ≤ B) :
    quotient (scaleL2 χ.function χ.regular.continuous χ.compact u) i h =
      scaleL2 χ.function χ.regular.continuous χ.compact (quotient u i h) +
        cutoffSource χ u i h hh B hχ := by
  apply Lp.ext
  filter_upwards [cutoff_quotient_commutator χ u i h,
    scaleL2_ae χ.function χ.regular.continuous χ.compact (quotient u i h),
    (cutoffSource_memLp χ u i h hh B hχ).coeFn_toLp,
    translateL2_ae u (h • basis i),
    Lp.coeFn_add (scaleL2 χ.function χ.regular.continuous χ.compact (quotient u i h))
      (cutoffSource χ u i h hh B hχ)] with x hc hs ht htr hadd
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hs]
  change _ = _ + cutoffSource χ u i h hh B hχ x
  rw [show cutoffSource χ u i h hh B hχ x = _ from ht, htr]
  exact hc

theorem cutoff_quotient_norm (χ : Test) (u : L2Scalar) (i : Fin 3) (h : ℝ) (hh : h ≠ 0)
    (A B : ℝ) (hA : ∀ x, ‖χ.function x‖ ≤ A)
    (hB : ∀ j x, ‖dcoord χ.function x j‖ ≤ B) :
    ‖quotient (scaleL2 χ.function χ.regular.continuous χ.compact u) i h‖ ≤
      A*‖quotient u i h‖ + 3*B*‖u‖ := by
  rw [cutoff_quotient_decomposition χ u i h hh B hB]
  exact (norm_add_le _ _).trans (add_le_add
    (InteriorTestDensity.scaleL2_norm_le χ.function χ.regular.continuous χ.compact _ hA)
    (cutoffSource_norm χ u i h hh B hB))

def derivativeCutoff (χ : Test) (hχ : ContDiff ℝ 2 χ.function) (j : Fin 3) : Test where
  function := fun x => dcoord χ.function x j
  regular := KernelSource.partial_contDiff hχ j
  compact := χ.compact.fderiv_apply ℝ (basis j)

theorem derivative_cutoff_commutator (χ : Test) (hχ : ContDiff ℝ 2 χ.function)
    (u : L2Scalar) (i j : Fin 3) (h : ℝ) :
    (fun x => quotient (scaleL2 (derivativeCutoff χ hχ j).function
      (derivativeCutoff χ hχ j).regular.continuous (derivativeCutoff χ hχ j).compact u) i h x) =ᵐ[volume]
      fun x => dcoord χ.function x j * quotient u i h x +
        (h : ℂ)⁻¹ * (dcoord χ.function (x+h • basis i) j-dcoord χ.function x j) *
          u (x+h • basis i) := by
  exact cutoff_quotient_commutator (derivativeCutoff χ hχ j) u i h

theorem derivative_cutoff_source_norm (χ : Test) (hχ : ContDiff ℝ 2 χ.function)
    (u : L2Scalar) (i j : Fin 3) (h : ℝ) (hh : h ≠ 0) (B : ℝ)
    (hB : ∀ l x, ‖dcoord (fun y => dcoord χ.function y j) x l‖ ≤ B) :
    ‖cutoffSource (derivativeCutoff χ hχ j) u i h hh B hB‖ ≤ 3*B*‖u‖ :=
  cutoffSource_norm (derivativeCutoff χ hχ j) u i h hh B hB

end OQ14.MaxwellCutoffCommutator
#print axioms OQ14.MaxwellCutoffCommutator.cutoff_quotient_commutator
#print axioms OQ14.MaxwellCutoffCommutator.cutoff_difference_bound
#print axioms OQ14.MaxwellCutoffCommutator.cutoffSource_norm
#print axioms OQ14.MaxwellCutoffCommutator.cutoff_quotient_norm
#print axioms OQ14.MaxwellCutoffCommutator.derivative_cutoff_commutator
#print axioms OQ14.MaxwellCutoffCommutator.derivative_cutoff_source_norm
