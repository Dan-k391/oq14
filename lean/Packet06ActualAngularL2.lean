import Packet06ConeFieldL2Limit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ActualAngularL2
open MeasureTheory Filter Set OQ14.Maxwell OQ14.AngularPower
open scoped Topology
abbrev Space := Maxwell.Space

theorem convergent_positive_branch (χ : ContDiffBump (0 : Space)) (t : ℝ)
    (ht0 : (1/2 : ℝ) ≤ t) (ht1 : t < 1) (η : ℕ → ℝ)
    (hη : ∀ j, 0 < η j) (hη0 : Tendsto η atTop (𝓝 0)) :
    ∃ p : ℕ → ConicalStaticVolume.Data,
      (∀ j, (p j).cutoff = χ ∧ (p j).contrast = η j ∧ (p j).threshold = t ∧
        0 < (p j).exponent ∧ (p j).exponent < 1 ∧
        CapAngularShooting.determinant (η j) t (p j).eigenvalue = 0) ∧
      Tendsto (fun j => (p j).eigenvalue) atTop (𝓝 2) ∧
      Tendsto (fun j => (p j).exponent) atTop (𝓝 1) ∧
      Tendsto (fun j => ∫ q : AngularPower.Sphere,
        ‖t⁻¹ • ConicalCapField.angularElectric (p j).exponent (p j).eigenvalue t q - basis 2‖^2 ∂angularMeasure)
        atTop (𝓝 0) := by
  obtain ⟨p,hp,hell,hν,_⟩ := Packet06ActualAngularBranch.convergent_positive_branch χ t ht0 ht1 η hη hη0
  have hbound (j : ℕ) : (p j).eigenvalue ∈ Ioo (0 : ℝ) 2 := by
    have hν0 := (hp j).2.2.2.1
    have hν1 := (hp j).2.2.2.2.1
    have hsep := (p j).separation
    constructor <;> nlinarith
  have he (j : ℕ) : (p j).exponent = CapAngularShooting.exponent (p j).eigenvalue := by
    have h1 := (p j).separation
    have h2 := CapAngularShooting.exponent_equation (p j).eigenvalue (hbound j).1.le
    have h3 := (CapAngularShooting.exponent_range (p j).eigenvalue (hbound j)).1
    have h4 := (hp j).2.2.2.1
    nlinarith
  refine ⟨p,hp,hell,hν,?_⟩
  have h := Packet06ConeFieldL2Limit.angular_electric_square_integral_tendsto
    (fun j => (p j).eigenvalue) hell hbound t (by linarith) ht1
  simpa only [← he] using h
#print axioms OQ14.Packet06ActualAngularL2.convergent_positive_branch
end OQ14.Packet06ActualAngularL2
