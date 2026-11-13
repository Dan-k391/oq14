import Packet06AxialActualField
import Packet05BinaryPhaseMaximum

/-! Cartesian transport of continuous phase representatives under axial rotation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06AxialPhaseField
open Set Metric Maxwell ModalAxialRotation Packet05ActualMaximum Packet05BinaryPhaseMaximum

def transport (θ : ℝ) (R : Fin 3 → Space → ℂ) : Fin 3 → Space → ℂ :=
  fun i x => ∑ j : Fin 3, matrix θ i j * R j (rotation (-θ) x)

theorem amplitude_transport (θ : ℝ) (R : Fin 3 → Space → ℂ) (x : Space) :
    physicalAmplitude (transport θ R) x = physicalAmplitude R (rotation (-θ) x) := by
  unfold physicalAmplitude
  have hh := Packet06AxialAmplitude.rotation_energy θ (fun j => R j (rotation (-θ) x))
  simp only [Maxwell.energy,Complex.normSq_eq_norm_sq] at hh
  have he : (fun i => transport θ R i x) = vector θ (fun j => R j (rotation (-θ) x)) := by
    funext i
    exact matrix_vector θ _ i
  simpa only [Fin.sum_univ_three, ← he] using congrArg Real.sqrt hh

theorem continuous_transport (θ : ℝ) (R : Fin 3 → Space → ℂ) (K : Set Space)
    (hR : ∀ k, ContinuousOn (R k) K) :
    ∀ k, ContinuousOn (transport θ R k) ((rotation θ) '' K) := by
  intro k
  unfold transport
  apply continuousOn_finset_sum
  intro j hj
  apply continuousOn_const.mul
  apply (hR j).comp ((rotation (-θ)).continuous.continuousOn)
  rintro y ⟨x,hx,rfl⟩
  simpa [rotation,spatial_inverse] using hx

theorem phase_transport (θ : ℝ) (inside outside : Fin 3 → Space → ℂ) (b : Bool) :
    phaseField (transport θ inside) (transport θ outside) b = transport θ (phaseField inside outside b) := by
  cases b <;> rfl

end OQ14.Packet06AxialPhaseField
#print axioms OQ14.Packet06AxialPhaseField.amplitude_transport
#print axioms OQ14.Packet06AxialPhaseField.continuous_transport
#print axioms OQ14.Packet06AxialPhaseField.phase_transport
