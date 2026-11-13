import Packet06ConeRootLimit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ActualAngularBranch
open Filter Set OQ14.Maxwell
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data

theorem convergent_positive_branch (χ : ContDiffBump (0 : Space)) (t : ℝ)
    (ht0 : (1/2 : ℝ) ≤ t) (ht1 : t < 1) (η : ℕ → ℝ)
    (hη : ∀ j, 0 < η j) (hη0 : Tendsto η atTop (𝓝 0)) :
    ∃ p : ℕ → Data,
      (∀ j, (p j).cutoff = χ ∧ (p j).contrast = η j ∧ (p j).threshold = t ∧
        0 < (p j).exponent ∧ (p j).exponent < 1 ∧
        CapAngularShooting.determinant (η j) t (p j).eigenvalue = 0) ∧
      Tendsto (fun j => (p j).eigenvalue) atTop (𝓝 2) ∧
      Tendsto (fun j => (p j).exponent) atTop (𝓝 1) ∧
      (∀ q : AngularPower.Sphere,
        Tendsto (fun j => t⁻¹ • ConicalCapField.angularElectric (p j).exponent (p j).eigenvalue t q)
          atTop (𝓝 (basis 2))) := by
  have ht : 0 < t := by linarith
  obtain ⟨p,hp⟩ := Packet06ModalConeBranch.positive_contrast_angular_branch χ t ht ht1 η hη
  have hroot (j : ℕ) : CapAngularShooting.determinant (η j) t (p j).eigenvalue = 0 := (hp j).2.2.2.2.2.1
  have hell := Packet06ConeRootLimit.eigenvalue_tendsto_two η (fun j => (p j).eigenvalue) t ht0 ht1 hη0
    (fun j => (p j).eigenvalue_bounds) hroot
  have hν : (fun j => (p j).exponent) = fun j => CapAngularShooting.exponent (p j).eigenvalue := by
    funext j
    have h1 := (p j).separation
    have h2 := CapAngularShooting.exponent_equation (p j).eigenvalue (p j).eigenvalue_bounds.1
    have hpos := (CapAngularShooting.exponent_range (p j).eigenvalue ⟨?_,?_⟩).1
    · nlinarith [(p j).exponent_pos]
    · have hpj := hp j
      have h := (p j).separation
      nlinarith [(p j).exponent_pos]
    · have hpj := hp j
      have h := (p j).separation
      nlinarith [hpj.2.2.2.2.1]
  refine ⟨p,fun j => ?_,hell,?_,?_⟩
  · exact ⟨(hp j).1,(hp j).2.1,(hp j).2.2.1,(hp j).2.2.2.1,(hp j).2.2.2.2.1,hroot j⟩
  · rw [hν]
    exact Packet06ConeAngularLimit.exponent_tendsto_one _ hell
  · intro q
    have hfield := Packet06ConeFieldLimit.normalized_angular_electric_tendsto _ hell
      (fun j => (p j).eigenvalue_bounds) t ht ht1 q
    have hv (j : ℕ) : (p j).exponent = CapAngularShooting.exponent (p j).eigenvalue := congrFun hν j
    simpa only [hv] using hfield
#print axioms OQ14.Packet06ActualAngularBranch.convergent_positive_branch
end OQ14.Packet06ActualAngularBranch
