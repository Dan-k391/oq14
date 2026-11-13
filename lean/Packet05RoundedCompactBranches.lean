import Packet05CompactBinaryMode
import Packet05RoundedModeActualPhases

/-! The literal rounded modes have continuous actual material-side branches
on every compact observation set inside the sphere. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RoundedCompactBranches
open MeasureTheory Set Filter Metric Maxwell Packet06ConcreteModalRounding
open scoped Topology
abbrev Space := Maxwell.Space

theorem eventually_compact_branches {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η) :
    ∀ᶠ j : ℕ in atTop, ∀ (z : ℂ), z ≠ 0 → ∀ (mode : VectorFourier.VectorL2),
      ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) z 1 mode=0 →
      ∀ (K : Set Space), IsCompact K → K ⊆ ball (0 : Space) 1 →
      let E := Packet06ComplexElectric.electric z
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) mode)
        (DynamicVolume.source (rounded n hn g η hη j) mode)
      ∃ inside outside : Fin 3 → Space → ℂ,
        (∀ i, ContinuousOn (inside i) (K ∩ closure (body g j))) ∧
        (∀ i, ContinuousOn (outside i) (K ∩ closure (closure (body g j))ᶜ)) ∧
        (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ body g j)] inside i) ∧
        (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure (body g j))ᶜ)] outside i) := by
  classical
  filter_upwards [Packet05RoundedModeActualPhases.eventually_actual_cone_phase_representatives n hn g η hη]
    with j hj z hz mode hmode K hK hKΩ
  have hhost : (n^2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sq_pos_of_pos (by linarith : 0 < n)))
  have hjump : (1+η : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1+η by linarith))
  have hbody : IsOpen (body g j) :=
    CommonBinaryInterface.body_open (fun _ => g.datum) (fun _ => g.radius) g.center j
  have hε (x : Space) (hx : x ∈ ball (0 : Space) 1) :=
    (Packet05RoundedModeMaterial.local_cone_material n hn g η hη j x hx).self_of_nhds
  apply Packet05CompactBinaryMode.compact_binary_mode (rounded n hn g η hη j) z hz 1 mode
    (Packet05RoundedModeSupport.rounded_support n hn g η hη j) hmode K (ball (0 : Space) 1)
    (body g j) hK isOpen_ball hbody hKΩ ((n^2 : ℂ)*(1+η)) (n^2 : ℂ)
    (mul_ne_zero hhost hjump) hhost
  · intro x hx
    simpa only [if_pos hx.2] using hε x hx.1
  · intro x hx
    simpa only [if_neg hx.2,mul_one] using hε x hx.1
  · intro x hx
    exact hj z hz mode hmode x hx.2

end OQ14.Packet05RoundedCompactBranches
#print axioms OQ14.Packet05RoundedCompactBranches.eventually_compact_branches
