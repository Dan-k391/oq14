import Maxwell
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Actual integration by parts across a single point in three-space -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.PointSingularity

open MeasureTheory OQ14.Maxwell

abbrev Plane := Fin 2 → ℝ

def split (i : Fin 3) : Space ≃ᵐ ℝ × Plane :=
  (EuclideanSpace.measurableEquiv (Fin 3)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i)

theorem split_measurePreserving (i : Fin 3) : MeasurePreserving (split i) :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) i).comp
    (EuclideanSpace.volume_preserving_measurableEquiv (Fin 3))

theorem join_affine (i : Fin 3) (q : Plane) (t : ℝ) :
    (split i).symm (t, q) = t • basis i + (split i).symm (0, q) := by
  ext j
  change Fin.insertNth (α := fun _ : Fin 3 => ℝ) i t q j =
    t * (basis i j) + Fin.insertNth (α := fun _ : Fin 3 => ℝ) i 0 q j
  fin_cases i <;> fin_cases j <;> simp [basis, EuclideanSpace.single_apply, Fin.insertNth]
  all_goals rfl

theorem join_hasDerivAt (i : Fin 3) (q : Plane) (t : ℝ) :
    HasDerivAt (fun s => (split i).symm (s, q)) (basis i) t := by
  have he : (fun s => (split i).symm (s, q)) =
      (fun s => s • basis i + (split i).symm (0, q)) := funext (join_affine i q)
  rw [he]
  simpa using ((hasDerivAt_id t).smul_const (basis i)).add_const ((split i).symm (0, q))

theorem join_ne_zero (i : Fin 3) (q : Plane) (hq : q ≠ 0) (t : ℝ) :
    (split i).symm (t, q) ≠ 0 := by
  intro h
  have he := congrArg (split i) h
  have hz : split i 0 = (0, 0) := by
    apply Prod.ext
    · rfl
    · rfl
  rw [MeasurableEquiv.apply_symm_apply, hz] at he
  exact hq (congrArg Prod.snd he)

theorem split_integrable (i : Fin 3) (f : Space → ℂ) (hf : Integrable f) :
    Integrable (fun p : ℝ × Plane => f ((split i).symm p)) :=
  ((MeasurePreserving.symm (split i) (split_measurePreserving i)).integrable_comp_emb
    (split i).symm.measurableEmbedding).mpr hf

theorem coordinate_Fubini (i : Fin 3) (f : Space → ℂ) (hf : Integrable f) :
    (∫ x, f x) = ∫ q : Plane, ∫ t : ℝ, f ((split i).symm (t, q)) :=
  ((MeasurePreserving.symm (split i) (split_measurePreserving i)).integral_comp' f).symm.trans
    (integral_prod_symm _ (split_integrable i f hf))

/-- The off-origin derivatives give actual integration by parts whenever the
three ordinary products are integrable. The point is removed by transverse
Fubini, not by assuming that a weak derivative has no atomic source. -/
theorem integration_by_parts (i : Fin 3) (f g : Space → ℂ)
    (hf : ∀ x, x ≠ 0 → DifferentiableAt ℝ f x)
    (hg : ∀ x, x ≠ 0 → DifferentiableAt ℝ g x)
    (hleft : Integrable (fun x => dcoord f x i * g x))
    (hright : Integrable (fun x => f x * dcoord g x i))
    (hprod : Integrable (fun x => f x * g x)) :
    (∫ x, f x * dcoord g x i) = -(∫ x, dcoord f x i * g x) := by
  rw [coordinate_Fubini i _ hright, coordinate_Fubini i _ hleft, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [(split_integrable i _ hleft).prod_left_ae,
    (split_integrable i _ hright).prod_left_ae,
    (split_integrable i _ hprod).prod_left_ae,
    show ∀ᵐ q : Plane, q ≠ 0 from ae_iff.mpr (by simp)] with q hl hr hp hq
  apply integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun t => (hf _ (join_ne_zero i q hq t)).hasFDerivAt.comp_hasDerivAt t
      (join_hasDerivAt i q t))
    (fun t => (hg _ (join_ne_zero i q hq t)).hasFDerivAt.comp_hasDerivAt t
      (join_hasDerivAt i q t)) hr hl hp

theorem test_product_integrable (f g : Space → ℂ) (hf : LocallyIntegrable f)
    (hg : Continuous g) (hc : HasCompactSupport g) : Integrable (fun x => f x * g x) := by
  classical
  have hi := (hf.integrableOn_isCompact hc).mul_continuousOn hg.continuousOn hc
  have he : (tsupport g).indicator (fun x => f x * g x) = (fun x => f x * g x) := by
    apply Set.indicator_eq_self.mpr
    intro x hx
    by_contra hn
    have hz := image_eq_zero_of_nmem_tsupport hn
    exact hx (by simp [hz])
  rw [← he]
  exact (integrable_indicator_iff hc.measurableSet).mpr hi

/-- Local integrability and actual derivatives off the point imply the weak
partial identity against every genuine compact C1 test. -/
theorem weak_partial (i : Fin 3) (f f' : Space → ℂ)
    (hf : ∀ x, x ≠ 0 → DifferentiableAt ℝ f x)
    (hder : ∀ x, x ≠ 0 → dcoord f x i = f' x)
    (hfloc : LocallyIntegrable f) (hdloc : LocallyIntegrable f')
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    (∫ x, f' x * φ x) = -(∫ x, f x * dcoord φ x i) := by
  have he : (fun x => f' x * φ x) =ᵐ[volume] (fun x => dcoord f x i * φ x) := by
    filter_upwards [show ∀ᵐ x : Space, x ≠ 0 from ae_iff.mpr (by simp)] with x hx
    rw [hder x hx]
  have hl := (test_product_integrable f' φ hdloc hφ.continuous hc).congr he
  have hr := test_product_integrable f (fun x => dcoord φ x i) hfloc
    (partial_continuous hφ i) (hc.fderiv_apply ℝ (basis i))
  have hp := test_product_integrable f φ hfloc hφ.continuous hc
  have hb := integration_by_parts i f φ hf (fun x _ => hφ.differentiable le_rfl x) hl hr hp
  rw [integral_congr_ae he]
  simpa only [neg_neg] using congrArg Neg.neg hb.symm

end OQ14.PointSingularity

#print axioms OQ14.PointSingularity.split_measurePreserving
#print axioms OQ14.PointSingularity.join_affine
#print axioms OQ14.PointSingularity.join_hasDerivAt
#print axioms OQ14.PointSingularity.join_ne_zero
#print axioms OQ14.PointSingularity.split_integrable
#print axioms OQ14.PointSingularity.coordinate_Fubini
#print axioms OQ14.PointSingularity.integration_by_parts
#print axioms OQ14.PointSingularity.test_product_integrable
#print axioms OQ14.PointSingularity.weak_partial
