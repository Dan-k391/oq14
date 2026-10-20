import FourierL2
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
The actual spherical measure obtained from Euclidean volume is positive on
every nonempty open patch. The proof lifts a patch times an open radial
interval through the polar homeomorphism to a nonempty Euclidean open set.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OQ14.SphereMeasure
open MeasureTheory Metric Set
open scoped Pointwise
abbrev Space := FourierL2.Space
abbrev Sphere := sphere (0 : Space) 1

theorem volume_toSphere_open_pos (s : Set Sphere) (hs : IsOpen s) (hne : s.Nonempty) :
    0 < (volume : Measure Space).toSphere s := by
  let r : Ioi (0 : ℝ) := ⟨1, by norm_num⟩
  let V : Set ({(0 : Space)}ᶜ : Set Space) :=
    homeomorphUnitSphereProd Space ⁻¹' (s ×ˢ Iio r)
  have hv : IsOpen V := (hs.prod isOpen_Iio).preimage
    (homeomorphUnitSphereProd Space).continuous
  have hvn : V.Nonempty := by
    obtain ⟨n, hn⟩ := hne
    refine ⟨(homeomorphUnitSphereProd Space).symm (n, ⟨1/2, by norm_num⟩), ?_⟩
    change (homeomorphUnitSphereProd Space)
      ((homeomorphUnitSphereProd Space).symm (n, ⟨1/2, by norm_num⟩)) ∈ s ×ˢ Iio r
    rw [Homeomorph.apply_symm_apply]
    exact ⟨hn, by norm_num [r]⟩
  have ho : IsOpen (Subtype.val '' V : Set Space) :=
    isOpen_compl_singleton.isOpenMap_subtype_val V hv
  have hp : 0 < (volume : Measure Space) (Subtype.val '' V) :=
    ho.measure_pos volume (hvn.image Subtype.val)
  have he := Measure.toSphere_apply_aux (volume : Measure Space) s r
  change (volume : Measure Space) (Subtype.val '' V) =
    (volume : Measure Space) (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) at he
  rw [Measure.toSphere_apply' _ hs.measurableSet, ← he]
  have hd : Module.finrank ℝ Space = 3 := by simp [Space, FourierL2.Space]
  rw [hd]
  exact ENNReal.mul_pos (by norm_num) hp.ne'

instance volume_toSphere_openPos :
    Measure.IsOpenPosMeasure (volume : Measure Space).toSphere where
  open_pos s hs hn := (volume_toSphere_open_pos s hs hn).ne'

theorem continuous_zero_of_ae_zero (f : Sphere → ℝ) (hf : Continuous f)
    (hz : f =ᵐ[(volume : Measure Space).toSphere] 0) : f = 0 :=
  Measure.eq_of_ae_eq hz hf continuous_const

theorem continuous_zero_of_integral_zero (f : Sphere → ℝ) (hf : Continuous f)
    (hi : Integrable f (volume : Measure Space).toSphere) (hn : ∀ n, 0 ≤ f n)
    (hz : (∫ n, f n ∂(volume : Measure Space).toSphere) = 0) : f = 0 :=
  continuous_zero_of_ae_zero f hf ((integral_eq_zero_iff_of_nonneg hn hi).mp hz)

end OQ14.SphereMeasure

#print axioms OQ14.SphereMeasure.volume_toSphere_open_pos
#print axioms OQ14.SphereMeasure.continuous_zero_of_ae_zero
#print axioms OQ14.SphereMeasure.continuous_zero_of_integral_zero
