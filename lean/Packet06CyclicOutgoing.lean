import Packet06CyclicRotationMaxwell

/-! Centered outgoing asymptotics under proper cyclic rotation and dilation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06CyclicOutgoing
open Filter Maxwell WeakCurl Packet06CyclicRotation Packet06CyclicRotationMaxwell
open scoped Topology

def factor (z : ℂ) (r : ℝ) : ℂ := (r : ℂ) * Complex.exp (-Complex.I*z*r)

theorem factor_scale (s r : ℝ) (z : ℂ) :
    factor ((s : ℂ)*z) r * (s : ℂ) = factor z (s*r) := by
  unfold factor
  have h : -Complex.I*((s : ℂ)*z)*(r : ℂ) = -Complex.I*z*((s*r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h]
  push_cast
  ring

theorem rotated_scaled_centered_limit (F : Field) (A : Space → Vector) (z : ℂ)
    (s : ℝ) (hs : 0 < s) (a n : Space) (hn : ‖n‖ = 1)
    (hF : ∀ v : Space, ‖v‖ = 1 → ∀ i : Fin 3,
      Tendsto (fun r : ℝ => factor z r * F (r • v) i) atTop (𝓝 (A v i)))
    (i : Fin 3) :
    Tendsto (fun r : ℝ => factor ((s : ℂ)*z) r *
      ((s : ℂ) * rotateField F (s • ((a+r • n)-a)) i)) atTop
      (𝓝 (A (unrotate n) (previous i))) := by
  have hu : ‖unrotate n‖ = 1 := by
    have h := rotation.symm.norm_map n
    change ‖unrotate n‖ = ‖n‖ at h
    rw [h,hn]
  have h := (hF (unrotate n) hu (previous i)).comp (tendsto_id.const_mul_atTop hs)
  refine h.congr (fun r => ?_)
  have ha : a+r • n-a = r • n := by abel
  rw [ha]
  have hr : unrotate (s • (r • n)) = (s*r) • unrotate n := by
    change rotation.symm (s • (r • n)) = _
    simpa only [smul_smul] using (rotation.symm.map_smul (s*r) n)
  change factor z (s*r) * F ((s*r) • unrotate n) (previous i) =
    factor ((s : ℂ)*z) r * ((s : ℂ) * F (unrotate (s • (r • n))) (previous i))
  rw [hr, ← mul_assoc, factor_scale]

end OQ14.Packet06CyclicOutgoing
#print axioms OQ14.Packet06CyclicOutgoing.factor_scale
#print axioms OQ14.Packet06CyclicOutgoing.rotated_scaled_centered_limit
