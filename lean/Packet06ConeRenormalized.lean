import Packet06ConeHolderParticular
import ConicalParticularLinear
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeRenormalized
open Set MeasureTheory OQ14.ConicalRadialParticular

theorem particular_constant_renormalized (ν : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1)
    (A B : ℝ → ℂ) (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0))
    (A₀ : ℂ) (r : ℝ) (hr : 0 < r) :
    particular ν (A-(fun _ => A₀)) (B-(fun _ => ((ν*(ν+1) : ℝ) : ℂ)*A₀)) r =
      particular ν A B r + (r : ℂ)*A₀ := by
  rw [ConicalParticularLinear.particular_sub ν hν A B _ _ hA hB continuousOn_const continuousOn_const r hr.le,
    Packet06ConeConstantCorrection.constant_particular ν hν A₀ r hr]
  ring

theorem zero_mode_projection_bound (ν α : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (hhalf : (1/2 : ℝ) ≤ ν)
    (hα : 0 < α) (A B : ℝ → ℂ) (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0))
    (A₀ : ℂ) (r M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (hb : ∀ s ∈ Ioo (0 : ℝ) r, ‖A s-A₀‖ ≤ M*s^α ∧
      ‖B s-((ν*(ν+1) : ℝ) : ℂ)*A₀‖ ≤ M*s^α)
    (hbr : ‖B r-((ν*(ν+1) : ℝ) : ℂ)*A₀‖ ≤ M*r^α) :
    ‖particular ν A B r+(r : ℂ)/((ν*(ν+1) : ℝ) : ℂ)*B r‖ ≤ (3/α+3)*M*r^(1+α) := by
  let ell : ℝ := ν*(ν+1)
  have hell : (0 : ℝ) < ell := mul_pos hν.1 (by linarith [hν.1])
  have hellb : (1/2 : ℝ) ≤ ell := by dsimp [ell]; nlinarith [hν.1]
  have hd : ((ell : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hell.ne'
  have he : particular ν A B r+(r : ℂ)/(ell : ℂ)*B r =
      (particular ν A B r+(r : ℂ)*A₀) + (r : ℂ)/(ell : ℂ)*(B r-(ell : ℂ)*A₀) := by
    field_simp [hd]
    ring
  have hp := Packet06ConeHolderParticular.particular_holder_bound ν α hν hα
    (A-(fun _ => A₀)) (B-(fun _ => (ell : ℂ)*A₀))
    (hA.sub continuousOn_const) (hB.sub continuousOn_const) r M hr hM (by simpa [ell] using hb)
  rw [particular_constant_renormalized ν hν A B hA hB A₀ r hr] at hp
  rw [he]
  calc
    _ ≤ ‖particular ν A B r+(r : ℂ)*A₀‖ + ‖(r : ℂ)/(ell : ℂ)*(B r-(ell : ℂ)*A₀)‖ := norm_add_le _ _
    _ ≤ (3/α+1)*M*r^(1+α) + 2*M*r^(1+α) := by
      apply add_le_add hp
      rw [norm_mul,norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos hr,abs_of_pos hell]
      have hb' : ‖B r-(ell : ℂ)*A₀‖ ≤ M*r^α := by simpa [ell] using hbr
      have hrl : r/ell ≤ 2*r := by
        apply (div_le_iff₀ hell).mpr
        nlinarith
      have hrpow : r*r^α = r^(1+α) := by
        calc
          r*r^α = r^(1 : ℝ)*r^α := by rw [Real.rpow_one]
          _ = r^(1+α) := (Real.rpow_add hr 1 α).symm
      calc
        _ ≤ (2*r)*(M*r^α) := mul_le_mul hrl hb' (norm_nonneg _) (by positivity)
        _ = _ := by rw [← hrpow]; ring
    _ = (3/α+3)*M*r^(1+α) := by ring
#print axioms OQ14.Packet06ConeRenormalized.particular_constant_renormalized
#print axioms OQ14.Packet06ConeRenormalized.zero_mode_projection_bound
end OQ14.Packet06ConeRenormalized
