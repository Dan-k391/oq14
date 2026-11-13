import Packet05UniformPhysicalDerivative
import Packet05ChartH2Uniform

/-! Actual scalar potential and graph gradient are uniformly bounded from the material source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05UniformScalarGraph
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.ConicalGradientGraph
  OQ14.Packet05ScalarGraphNorm OQ14.Packet05UniformScalarPotential OQ14.Packet05UniformPhysicalDerivative
  OQ14.Packet05ChartWeakGradient OQ14.Packet05ChartWeakDivergence OQ14.Packet05ChartH2Uniform
  OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphH2Norm OQ14.Packet05GraphPullback
  OQ14.Packet05GraphSlopeMultiplier
abbrev V := OQ14.VectorFourier.VectorL2
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem uniform_actual_scalar_graph (χ : ContDiffBump (0 : Maxwell.Space)) (S Z B : ℝ)
    (hS : 0 ≤ S) (hZ : 0 ≤ Z) (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (hB : ∀ i x, ‖slopeC g i x‖ ≤ B) (up : Bool) (axis : Fin 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, ‖z‖ ≤ Z → ∀ (F : V) (ρ : Fin 3 → Maxwell.Space → ℂ)
      (_hρ : ∀ j, Integrable (ρ j))
      (hF : ∀ j, OQ14.NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j)
      (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0),
      let U := OQ14.Packet06ComplexConePotential.potentialData z S F ρ hc hF
      let v := pullback g hg.continuous (chartPull up axis (value χ U))
      let C := pulledGradient g hg (chartVector up axis (ConicalGradientGraph.gradient χ U)) (fun _ => B) hB
      ‖v‖ ≤ K*‖F‖ ∧ ∀ i, ‖C i‖ ≤ K*‖F‖ := by
  obtain ⟨Kp,hKp,hpotential⟩ := uniform_potential_representative χ.rOut S Z hZ
  obtain ⟨Kd,hKd,hderiv⟩ := uniform_physical_derivative χ.rOut S Z χ.rOut_pos.le hS hZ
  obtain ⟨Kχ,hKχ,hχ⟩ := derivative_bound χ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  let K := max Kp ((1+B)*(Kd+Kχ*Kp))
  have hK : 0 ≤ K := hKp.trans (le_max_left _ _)
  refine ⟨K,hK,?_⟩
  intro z hz F ρ hρ hF hc
  let U := OQ14.Packet06ComplexConePotential.potentialData z S F ρ hc hF
  let P := representative z χ.rOut S F
  let D (i : Fin 3) := electricRepresentative z χ.rOut S F i - correctionRepresentative z χ.rOut S F i
  have hp := hpotential z hz F ρ hρ hF hc
  have hd (i : Fin 3) := hderiv z hz F ρ hρ hF hc i
  have hpval : ∀ᵐ x ∂volume, x ∈ closedBall (0 : Maxwell.Space) χ.rOut → P x = U.potential x := hp.1
  have hdval (i : Fin 3) : ∀ᵐ x ∂volume, x ∈ closedBall (0 : Maxwell.Space) χ.rOut → D i x = U.derivative i x := (hd i).1
  have hn := localized_scalar_norms_with_bound χ U P D hpval hdval Kχ hKχ hχ
  have hU : ‖value χ U‖ ≤ Kp*‖F‖ := hn.1.trans hp.2
  have hDnorm (i : Fin 3) : ‖ConicalGradientGraph.gradient χ U i‖ ≤ (Kd+Kχ*Kp)*‖F‖ := by
    have h1 := (hd i).2
    have h2 := mul_le_mul_of_nonneg_left hp.2 hKχ
    exact (hn.2 i).trans (by nlinarith)
  have hchart (i : Fin 3) : ‖chartVector up axis (ConicalGradientGraph.gradient χ U) i‖ ≤ (Kd+Kχ*Kp)*‖F‖ := by
    simpa only [chartVector,norm_smul,chart_sign_norm,one_mul,chart_pull_norm] using hDnorm (Equiv.swap axis 2 i)
  constructor
  · rw [pullback_norm,chart_pull_norm]
    exact hU.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · intro i
    have h := pulled_gradient_norm g hg (chartVector up axis (ConicalGradientGraph.gradient χ U)) (fun _ => B) hB i
    have h1 := hchart i
    have h2 := hchart 2
    have h3 := mul_le_mul_of_nonneg_left h2 hB0
    have hk := mul_le_mul_of_nonneg_right (le_max_right Kp ((1+B)*(Kd+Kχ*Kp))) (norm_nonneg F)
    exact h.trans (by nlinarith)

end OQ14.Packet05UniformScalarGraph
#print axioms OQ14.Packet05UniformScalarGraph.uniform_actual_scalar_graph
