import Packet06PlacementHomeomorph

/-! Exact transport of continuous one-sided electric vectors and their
physical Euclidean amplitude under the normalized Maxwell placement. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06PlacedPhaseField
open Set Metric Maxwell Packet06PlacementHomeomorph Packet05ActualMaximum
  Packet05BinaryPhaseMaximum

def scale (s : ℝ) : ℝ := Real.sqrt s*s

def transport (s : ℝ) (hs : 0 < s) (a : Space) (R : Fin 3 → Space → ℂ) :
    Fin 3 → Space → ℂ :=
  fun k y => ((scale s : ℝ) : ℂ)*R (WeakCurl.previous k) ((placement s hs a).symm y)

theorem scale_pos (s : ℝ) (hs : 0 < s) : 0 < scale s :=
  mul_pos (Real.sqrt_pos.mpr hs) hs

theorem amplitude_transport (s : ℝ) (hs : 0 < s) (a : Space)
    (R : Fin 3 → Space → ℂ) (y : Space) :
    physicalAmplitude (transport s hs a R) y =
      scale s*physicalAmplitude R ((placement s hs a).symm y) := by
  have hβ : 0 ≤ scale s := (scale_pos s hs).le
  simp only [physicalAmplitude, transport, Fin.sum_univ_three, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ, WeakCurl.previous,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]
  change Real.sqrt ((scale s*‖R 2 ((placement s hs a).symm y)‖)^2+
      (scale s*‖R 0 ((placement s hs a).symm y)‖)^2+
      (scale s*‖R 1 ((placement s hs a).symm y)‖)^2) =
    scale s*Real.sqrt (‖R 0 ((placement s hs a).symm y)‖^2+
      ‖R 1 ((placement s hs a).symm y)‖^2+‖R 2 ((placement s hs a).symm y)‖^2)
  rw [show (scale s*‖R 2 ((placement s hs a).symm y)‖)^2+
      (scale s*‖R 0 ((placement s hs a).symm y)‖)^2+
      (scale s*‖R 1 ((placement s hs a).symm y)‖)^2 =
      (scale s)^2*(‖R 0 ((placement s hs a).symm y)‖^2+
      ‖R 1 ((placement s hs a).symm y)‖^2+‖R 2 ((placement s hs a).symm y)‖^2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hβ]

theorem continuous_transport (s : ℝ) (hs : 0 < s) (a : Space)
    (R : Fin 3 → Space → ℂ) (K : Set Space)
    (hR : ∀ k, ContinuousOn (R k) K) :
    ∀ k, ContinuousOn (transport s hs a R k) (placement s hs a '' K) := by
  intro k
  apply continuousOn_const.mul
  apply (hR (WeakCurl.previous k)).comp (placement s hs a).symm.continuous.continuousOn
  rintro y ⟨x,hx,rfl⟩
  simpa using hx

theorem phase_transport (s : ℝ) (hs : 0 < s) (a : Space)
    (inside outside : Fin 3 → Space → ℂ) (b : Bool) :
    phaseField (transport s hs a inside) (transport s hs a outside) b =
      transport s hs a (phaseField inside outside b) := by cases b <;> rfl

end OQ14.Packet06PlacedPhaseField
#print axioms OQ14.Packet06PlacedPhaseField.scale_pos
#print axioms OQ14.Packet06PlacedPhaseField.amplitude_transport
#print axioms OQ14.Packet06PlacedPhaseField.continuous_transport
#print axioms OQ14.Packet06PlacedPhaseField.phase_transport
