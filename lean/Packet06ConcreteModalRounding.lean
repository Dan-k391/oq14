import Packet06ConcreteModalBranch
import Packet06RoundedMode
import Packet06SphereConeContrast

/-! The literal rounded family for the selected finite modal geometry. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ConcreteModalRounding
open Metric Set Filter Packet06ConcreteModalGeometry Packet06SectorOperator
open Packet06SimpleCertificate (Certified)
open Packet06PhysicalNormalization (reciprocalNorm)
open scoped Topology
abbrev Space := Maxwell.Space

def sharp {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n) (η : ℝ) (hη : 0 ≤ η) :=
  Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn) (cone g) η hη

def rounded {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n) (η : ℝ) (hη : 0 ≤ η) :=
  Packet06RoundedInsertion.rounded (fun _ => g.datum) (fun _ => g.radius) g.center
    (n^2) (sq_nonneg n) (fun _ => g.contrast.le) (fun _ => g.radius_outer)
    g.outer_disjoint (fun _ => g.radius_pos) (ModalWeightedMode.coefficient n hn) η hη

def body {N : ℕ} {n : ℝ} (g : Geometry N n) (j : ℕ) : Set Space :=
  CommonBinaryInterface.body (fun _ => g.datum) (fun _ => g.radius) g.center j

theorem body_inside {N : ℕ} {n : ℝ} (g : Geometry N n) (j : ℕ) : body g j ⊆ ball 0 1 := by
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  apply g.outer_inside i
  change ‖x-g.center i‖ ≤ g.datum.cutoff.rOut
  exact (ConicalJunctionPhysical.inclusion_norm_bound j _ _ g.radius_pos _ hi).le.trans g.radius_outer

theorem dielectric_values {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (j : ℕ) (x : Space) :
    1+(rounded n hn g η hη j).value (VectorFourier.coordinateMap x)=
      (by classical exact if x ∈ body g j then (1+η)*n^2 else if ‖x‖ < 1 then n^2 else 1) := by
  classical
  have he := Packet06SphereConeContrast.inserted_value (fun _ => g.datum) (fun _ => g.radius)
    g.center (n^2) (sq_nonneg n) (fun _ => g.contrast.le) (fun _ => g.radius_outer)
    g.outer_disjoint (fun _ => g.radius_pos) n hn (fun _ => g.contrast) j η hη x
  change 1+ (Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn) _ η hη).value
    (VectorFourier.coordinateMap x)=_
  rw [he,ModalWeightedMode.coefficient_value]
  by_cases hb : x ∈ body g j
  · have hx : ‖x‖ < 1 := by simpa using body_inside g j hb
    simp only [show x ∈ CommonBinaryInterface.body (fun _ => g.datum) (fun _ => g.radius) g.center j from hb,
      hb,if_pos,hx]
    ring
  · change 1+((if ‖x‖ < 1 then n^2-1 else 0)+(if x ∈ body g j then η*n^2 else 0))=_
    rw [if_neg hb,if_neg hb]
    split_ifs <;> ring

theorem same_mode_rounding {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z₀ : ℂ) (u₀ : Sector)
    (hcert : Certified (sharp n hn g η hη) 1 z₀ u₀)
    (hN : reciprocalNorm (sharp n hn g η hη) 1 z₀ u₀=1)
    (hre : 0 < z₀.re) (him : z₀.im < 0) (Q : ℝ) (hQ : Q < z₀.re/(-2*z₀.im)) :
    ∃ (z : ℕ → ℂ) (v : ℕ → Sector),
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto v atTop (𝓝 u₀) ∧
      (∀ T : ℝ, 1 ≤ T → Tendsto
        (fun j => Packet06LocalPencil.response (rounded n hn g η hη j) (z j) 1 T (v j)) atTop
        (𝓝 (Packet06LocalPencil.response (sharp n hn g η hη) z₀ 1 T u₀))) ∧
      (∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re/(-2*(z j).im) ∧
        Certified (rounded n hn g η hη j) 1 (z j) (v j) ∧
        reciprocalNorm (rounded n hn g η hη j) 1 (z j) (v j)=1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (rounded n hn g η hη j) (z j) 1 (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (rounded n hn g η hη j) 1 (z j) (v j)) := by
  exact Packet06RoundedMode.normalized_rounded_modes (fun _ => g.datum) (fun _ => g.radius)
    g.center (n^2) (sq_nonneg n) (fun _ => g.contrast.le) (fun _ => g.radius_outer)
    g.outer_disjoint (fun _ => g.radius_pos) (ModalWeightedMode.coefficient n hn) η hη
    (ModalWeightedMode.coefficient_support n hn) (Packet06SphereSymmetry.sphere_axial n hn)
    (Packet06SphereSymmetry.sphere_meridional n hn) g.onAxis
    (fun i => (g.outer_inside i).trans ball_subset_closedBall) z₀ u₀ hcert hN hre him Q hQ

end OQ14.Packet06ConcreteModalRounding
#print axioms OQ14.Packet06ConcreteModalRounding.body_inside
#print axioms OQ14.Packet06ConcreteModalRounding.dielectric_values
#print axioms OQ14.Packet06ConcreteModalRounding.same_mode_rounding
