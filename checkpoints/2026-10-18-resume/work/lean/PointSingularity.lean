import Maxwell
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod

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
  change i.insertNth t q j = t * (basis i j) + i.insertNth 0 q j
  fin_cases i <;> fin_cases j <;> simp [basis, EuclideanSpace.single_apply, Fin.insertNth]

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

end OQ14.PointSingularity
