import Packet06BoundedModalMaterial
import Packet06PlacementHomeomorph
import Packet06PlacedSmoothBoundary

/-! Exact physical material values after the actual Maxwell placement. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06PlacedMaterialGeometry
open Set Metric Filter Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet06PlacementHomeomorph Packet06PlacedKernel
open scoped Topology

theorem placed_material_values {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (j : ℕ) (s : ℝ) (hs : 0 < s) (a x : Maxwell.Space) :
    MaterialMaxwell.dielectric (placedCoefficient s a (rounded n hn g η hη j)) x =
      (by classical exact if x ∈ placement s hs a '' body g j then (1+η)*n^2
        else if x ∈ placement s hs a '' ball (0 : Maxwell.Space) 1 then n^2 else 1) := by
  classical
  rw [Packet06BoundedModalMaterial.placed_dielectric]
  change 1 + (rounded n hn g η hη j).value (VectorFourier.coordinateMap ((placement s hs a).symm x)) = _
  rw [dielectric_values]
  rw [(placement s hs a).image_eq_preimage, (placement s hs a).image_eq_preimage]
  simp [Metric.mem_ball, dist_zero_right]

theorem unit_ball_smooth :
    ∀ x ∈ frontier (ball (0 : Maxwell.Space) 1), ∃ F : Maxwell.Space → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∃ U : Set Maxwell.Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
        (y ∈ ball (0 : Maxwell.Space) 1 ↔ 0 < F y) := by
  intro x hx
  have hnorm : ‖x‖ = 1 := by
    have hh : x ∈ sphere (0 : Maxwell.Space) 1 := by simpa only [frontier_ball (0 : Maxwell.Space) (by norm_num : (1 : ℝ) ≠ 0)] using hx
    simpa [Metric.mem_sphere, dist_zero_right] using hh
  let F : Maxwell.Space → ℝ := fun y => 1 - ‖y‖^2
  have hf : ContDiff ℝ (⊤ : ℕ∞) F := by
    dsimp [F]
    have h := (contDiff_inner.comp (contDiff_id.prodMk contDiff_id) : ContDiff ℝ (⊤ : ℕ∞) (fun y : Maxwell.Space => @inner ℝ Maxwell.Space _ y y))
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Maxwell.Space => ‖y‖^2) := by
      simpa only [Function.comp_def, id_eq, real_inner_self_eq_norm_sq] using h
    exact contDiff_const.sub h2
  have hd : HasFDerivAt F (-( (2 : ℕ) • innerSL ℝ x)) x := by
    simpa only [F, zero_sub] using (hasFDerivAt_const (1 : ℝ) x).sub (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hne : fderiv ℝ F x ≠ 0 := by
    intro hz
    have h := congrArg (fun L : Maxwell.Space →L[ℝ] ℝ => L x) hz
    rw [hd.fderiv] at h
    simp only [ContinuousLinearMap.neg_apply, two_smul, ContinuousLinearMap.add_apply, innerSL_apply,
      real_inner_self_eq_norm_sq, ContinuousLinearMap.zero_apply] at h
    nlinarith
  refine ⟨F,hf.contDiffAt,by simp [F,hnorm],hne,Set.univ,isOpen_univ,mem_univ x,?_⟩
  intro y hy
  simp only [mem_ball,dist_zero_right,F]
  constructor <;> intro h <;> nlinarith [norm_nonneg y]

theorem placed_outer_smooth (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) :
    ∀ x ∈ frontier (placement s hs a '' ball (0 : Maxwell.Space) 1), ∃ F : Maxwell.Space → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∃ U : Set Maxwell.Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
        (y ∈ placement s hs a '' ball (0 : Maxwell.Space) 1 ↔ 0 < F y) :=
  Packet06PlacedSmoothBoundary.smooth_boundary_image s hs a _ unit_ball_smooth
theorem placed_piecewise_smooth {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) :
    ∀ᶠ j : ℕ in atTop,
      let I := placement s hs a '' body g j
      let S := placement s hs a '' ball (0 : Maxwell.Space) 1
      IsOpen I ∧ IsOpen S ∧ I ⊆ S ∧
      (∀ x, MaterialMaxwell.dielectric (placedCoefficient s a (rounded n hn g η hη j)) x =
        (by classical exact if x ∈ I then (1+η)*n^2 else if x ∈ S then n^2 else 1)) ∧
      (∀ x ∈ frontier I, ∃ F : Maxwell.Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧
        fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Maxwell.Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, (y ∈ I ↔ 0 < F y)) ∧
      (∀ x ∈ frontier S, ∃ F : Maxwell.Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧
        fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Maxwell.Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, (y ∈ S ↔ 0 < F y)) := by
  filter_upwards [Packet05RoundedModeMaterial.eventually_boundary_certificate g] with j hj
  dsimp only
  refine ⟨(placement s hs a).isOpenMap _ ?_, (placement s hs a).isOpenMap _ isOpen_ball,
    Set.image_subset _ (body_inside g j), fun x => placed_material_values n hn g η hη j s hs a x,
    Packet06PlacedSmoothBoundary.smooth_boundary_image s hs a _ hj, placed_outer_smooth s hs a⟩
  exact CommonBinaryInterface.body_open (fun _ => g.datum) (fun _ => g.radius) g.center j
end OQ14.Packet06PlacedMaterialGeometry
#print axioms OQ14.Packet06PlacedMaterialGeometry.placed_material_values
#print axioms OQ14.Packet06PlacedMaterialGeometry.unit_ball_smooth
#print axioms OQ14.Packet06PlacedMaterialGeometry.placed_outer_smooth
#print axioms OQ14.Packet06PlacedMaterialGeometry.placed_piecewise_smooth
