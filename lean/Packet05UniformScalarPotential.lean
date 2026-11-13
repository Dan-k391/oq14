import Packet05ScalarGraphNorm
import Packet06UniformGreenOperators

/-! Uniform L² representative of the actual scalar Green potential. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05UniformScalarPotential
open MeasureTheory Metric Set OQ14.Maxwell OQ14.Packet06UniformGreenOperators
  OQ14.Packet06ComplexPotential
abbrev V := OQ14.VectorFourier.VectorL2

def representative (z : ℂ) (R S : ℝ) (F : V) : OQ14.NewtonL2.ScalarL2 :=
  gradientOperator z (R+S) 0 (OQ14.NewtonL2.physicalCoordinate F 0) +
  gradientOperator z (R+S) 1 (OQ14.NewtonL2.physicalCoordinate F 1) +
  gradientOperator z (R+S) 2 (OQ14.NewtonL2.physicalCoordinate F 2)

theorem uniform_potential_representative (R S Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, ‖z‖ ≤ Z → ∀ (F : V) (ρ : Fin 3 → Space → ℂ),
      (∀ j, Integrable (ρ j)) →
      (∀ j, OQ14.NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) →
      (∀ j y, y ∉ closedBall 0 S → ρ j y = 0) →
      (∀ᵐ x ∂volume, x ∈ closedBall 0 R → representative z R S F x = potential z ρ x) ∧
      ‖representative z R S F‖ ≤ K*‖F‖ := by
  have hex (j : Fin 3) := gradient_uniform (R+S) Z hZ j
  choose C hC hbound using hex
  let K := C 0+C 1+C 2
  have hK : 0 ≤ K := by dsimp [K]; linarith [hC 0,hC 1,hC 2]
  refine ⟨K,hK,?_⟩
  intro z hz F ρ hρ hF hc
  let U (j : Fin 3) := gradientOperator z (R+S) j (OQ14.NewtonL2.physicalCoordinate F j)
  have hu (j : Fin 3) : ∀ᵐ x ∂volume, x ∈ closedBall 0 R → U j x =
      OQ14.KernelConvolution.response (fun y => OQ14.ComplexGreenKernel.phiGradient z y j) (ρ j) x := by
    exact OQ14.LocalConvolution.operator_ae_on_ball _ (OQ14.ComplexMagneticLocal.gradient_locallyIntegrable z j)
      (ρ j) (hρ j) (OQ14.NewtonL2.physicalCoordinate F j) (hF j) R S (hc j)
  have hn (j : Fin 3) : ‖U j‖ ≤ C j*‖F‖ := by
    have h := (ContinuousLinearMap.le_opNorm (gradientOperator z (R+S) j) (OQ14.NewtonL2.physicalCoordinate F j)).trans
      (mul_le_mul_of_nonneg_right (hbound j z hz) (norm_nonneg _))
    have hcj : ‖OQ14.NewtonL2.physicalCoordinate F j‖ ≤ ‖F‖ := OQ14.DynamicConvolution.component_norm j F
    exact h.trans (mul_le_mul_of_nonneg_left hcj (hC j))
  constructor
  · filter_upwards [hu 0,hu 1,hu 2,Lp.coeFn_add (U 0) (U 1),Lp.coeFn_add (U 0+U 1) (U 2)] with x h0 h1 h2 ha hb hx
    change (U 0+U 1+U 2 : OQ14.NewtonL2.ScalarL2) x = _
    rw [hb]
    simp only [Pi.add_apply]
    rw [ha]
    simp only [Pi.add_apply]
    rw [h0 hx,h1 hx,h2 hx]
    simp only [potential,Fin.sum_univ_three]
  · change ‖U 0+U 1+U 2‖ ≤ K*‖F‖
    have hsum := (norm_add_le (U 0+U 1) (U 2)).trans (add_le_add_right (norm_add_le (U 0) (U 1)) _)
    have h0 := hn 0; have h1 := hn 1; have h2 := hn 2
    dsimp [K]
    nlinarith

end OQ14.Packet05UniformScalarPotential
#print axioms OQ14.Packet05UniformScalarPotential.uniform_potential_representative
