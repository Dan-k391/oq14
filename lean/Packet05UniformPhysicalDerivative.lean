import Packet05UniformScalarPotential
import Packet06ComplexElectric

/-! Uniform L² representatives for actual electric and correction fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05UniformPhysicalDerivative
open MeasureTheory Metric Set OQ14.Maxwell OQ14.Packet06UniformGreenOperators
abbrev V := OQ14.VectorFourier.VectorL2
abbrev ScalarL2 := OQ14.NewtonL2.ScalarL2

def electricRepresentative (z : ℂ) (R S : ℝ) (F : V) (i : Fin 3) : ScalarL2 :=
  OQ14.NewtonL2.physicalCoordinate (OQ14.NewtonL2.newtonOperator F + OQ14.ComplexConvolutionAnalytic.operator z (R+S) F) i

def correctionRepresentative (z : ℂ) (R S : ℝ) (F : V) (i : Fin 3) : ScalarL2 :=
  z^2 • phiOperator z (R+S) (OQ14.NewtonL2.physicalCoordinate F i)

theorem uniform_physical_derivative (R S Z : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S) (hZ : 0 ≤ Z) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, ‖z‖ ≤ Z → ∀ (F : V) (ρ : Fin 3 → Space → ℂ),
      (∀ j, Integrable (ρ j)) →
      (∀ j, OQ14.NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) →
      (∀ j y, y ∉ closedBall 0 S → ρ j y = 0) →
      ∀ i, (∀ᵐ x ∂volume, x ∈ closedBall 0 R →
        (electricRepresentative z R S F i - correctionRepresentative z R S F i) x =
          OQ14.Packet06ComplexElectric.electric z F ρ x i - OQ14.Packet06ComplexPotential.correction z ρ x i) ∧
        ‖electricRepresentative z R S F i - correctionRepresentative z R S F i‖ ≤ K*‖F‖ := by
  obtain ⟨P,hP,hphi⟩ := phi_uniform (R+S) Z (by linarith) hZ
  have hcont := (OQ14.ComplexConvolutionAnalytic.operator_differentiable (R+S) (by linarith)).continuous.norm
  obtain ⟨A,hA⟩ := (isCompact_closedBall (0 : ℂ) Z).bddAbove_image hcont.continuousOn
  let K := 1+max A 0 + Z^2*P
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  intro z hz F ρ hρ hF hc i
  let E := OQ14.NewtonL2.newtonOperator F + OQ14.ComplexConvolutionAnalytic.operator z (R+S) F
  let Wi := phiOperator z (R+S) (OQ14.NewtonL2.physicalCoordinate F i)
  have he := (ae_restrict_iff' measurableSet_closedBall).mp
    (OQ14.Packet06ComplexElectric.electric_ae_on_ball z S R F ρ hρ hc hF i)
  have hcoord := OQ14.NewtonL2.physicalCoordinate_ae E i
  have hw := OQ14.LocalConvolution.operator_ae_on_ball _ (OQ14.Packet06ComplexScalarKernel.phi_locallyIntegrable z)
    (ρ i) (hρ i) (OQ14.NewtonL2.physicalCoordinate F i) (hF i) R S (hc i)
  have hA' : ‖OQ14.ComplexConvolutionAnalytic.operator z (R+S)‖ ≤ max A 0 :=
    (hA ⟨z,by simpa only [mem_closedBall,dist_zero_right] using hz,rfl⟩).trans (le_max_left _ _)
  have hcoordnorm : ‖OQ14.NewtonL2.physicalCoordinate F i‖ ≤ ‖F‖ := OQ14.DynamicConvolution.component_norm i F
  have heNorm : ‖E‖ ≤ (1+max A 0)*‖F‖ := by
    have hstatic := (ContinuousLinearMap.le_opNorm OQ14.NewtonL2.newtonOperator F).trans
      (mul_le_mul_of_nonneg_right OQ14.NewtonL2.newtonOperator_norm_le (norm_nonneg F))
    have hdyn := (ContinuousLinearMap.le_opNorm (OQ14.ComplexConvolutionAnalytic.operator z (R+S)) F).trans
      (mul_le_mul_of_nonneg_right hA' (norm_nonneg F))
    exact (norm_add_le _ _).trans (by nlinarith)
  have hphiNorm : ‖Wi‖ ≤ P*‖F‖ := by
    have h := (ContinuousLinearMap.le_opNorm (phiOperator z (R+S)) (OQ14.NewtonL2.physicalCoordinate F i)).trans
      (mul_le_mul_of_nonneg_right (hphi z hz) (norm_nonneg _))
    exact h.trans (mul_le_mul_of_nonneg_left hcoordnorm hP)
  have hz2 : ‖z‖^2 ≤ Z^2 := (sq_le_sq₀ (norm_nonneg z) hZ).mpr hz
  have hWnorm : ‖correctionRepresentative z R S F i‖ ≤ Z^2*P*‖F‖ := by
    rw [correctionRepresentative,norm_smul,norm_pow]
    have h := mul_le_mul hz2 hphiNorm (norm_nonneg _) (sq_nonneg Z)
    nlinarith
  have hEnorm : ‖electricRepresentative z R S F i‖ ≤ (1+max A 0)*‖F‖ :=
    (OQ14.DynamicConvolution.component_norm i E).trans heNorm
  constructor
  · filter_upwards [he,hcoord,hw,Lp.coeFn_smul (z^2) Wi,Lp.coeFn_sub (electricRepresentative z R S F i) (correctionRepresentative z R S F i)] with x he hc' hw hs hsub hx
    rw [hsub]
    simp only [Pi.sub_apply]
    change OQ14.NewtonL2.physicalCoordinate E i x - (z^2 • Wi : ScalarL2) x = _
    rw [hc',he hx,hs]
    simp only [Pi.smul_apply,smul_eq_mul, OQ14.Packet06ComplexPotential.correction]
    have hw' := hw hx
    change (Wi : Space → ℂ) x = OQ14.KernelConvolution.response (OQ14.ComplexGreenKernel.phi z) (ρ i) x at hw'
    rw [hw']
  · exact (norm_sub_le _ _).trans (by dsimp [K]; linarith)

end OQ14.Packet05UniformPhysicalDerivative
#print axioms OQ14.Packet05UniformPhysicalDerivative.uniform_physical_derivative
