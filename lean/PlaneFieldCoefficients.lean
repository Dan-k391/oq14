import TransversePlaneFields
import PoloidalPlaneWaveMoment

/-! Actual projected plane coefficients remove the radial projection by tangency. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PlaneFieldCoefficients
open MeasureTheory OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.ComplexVectorSphere
open OQ14.TransversePlaneFields OQ14.VectorHarmonicNormalization
open scoped ComplexInnerProductSpace

theorem embed_inner (v w : Space) :
    ⟪embedVector v,embedVector w⟫=((@inner ℝ Space _ v w : ℝ) : ℂ) := by
  simp only [PiLp.inner_apply,embed_apply,RCLike.inner_apply,Complex.conj_ofReal,
    Complex.ofReal_mul,Complex.ofReal_sum,conj_trivial]

theorem inner_projected (v : Space) (n : Sphere) (i : Fin 3)
    (hv : @inner ℝ Space _ (n : Space) v=0) : ⟪embedVector v,projected i n⟫=(v i : ℂ) := by
  have hn : ⟪embedVector v,normal n⟫=0 := by
    rw [normal,embed_inner,real_inner_comm,hv,Complex.ofReal_zero]
  rw [projected,inner_sub_right,inner_smul_right,hn,mul_zero,sub_zero]
  change ⟪embedVector v,EuclideanSpace.single i 1⟫=(v i : ℂ)
  rw [EuclideanSpace.inner_single_right]
  simp only [embed_apply,Complex.conj_ofReal,mul_one,one_mul]

theorem coefficient_integral (v : RealAmbient) (hv : VectorHarmonicSeparation.IsTangential v)
    (k : ℝ) (x : Space) (i : Fin 3) :
    ⟪realLift v,field k x i⟫=
      ∫ n : Sphere,(v n i : ℂ)*SphereReactionKernel.wave (-k) x n ∂angularMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv,embedVector.coeFn_compLpL v,
    (plane k x i).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n hn he hf
  change realLift v n=embedVector (v n) at he
  change field k x i n=plane k x i n at hf
  rw [he,hf]
  change ⟪embedVector (v n),SphereReactionKernel.wave (-k) x n • projected i n⟫=_
  rw [inner_smul_right,inner_projected (v n) n i hn]
  ring

theorem smul_tangent (a : ℝ) (v : RealAmbient) (hv : VectorHarmonicSeparation.IsTangential v) :
    VectorHarmonicSeparation.IsTangential (a • v) := by
  filter_upwards [hv,Lp.coeFn_smul a v] with n hn he
  rw [he]
  change @inner ℝ Space _ (n : Space) (a • v n)=0
  rw [inner_smul_right,hn,mul_zero]

theorem polarized_tangent (a : PositiveIndex ⊕ PositiveIndex) :
    VectorHarmonicSeparation.IsTangential (polarized a) := by
  cases a with
  | inl a => exact smul_tangent _ _ (TransverseHarmonicBasis.poloidal_tangent ⟨a.1+1,a.2⟩)
  | inr a => exact smul_tangent _ _ (TransverseHarmonicBasis.toroidal_tangent ⟨a.1+1,a.2⟩)

theorem mode_coefficient (a : ComplexTransverseExpansion.ModeIndex)
    (k : ℝ) (x : Space) (i : Fin 3) :
    ⟪ComplexTransverseExpansion.vector a,field k x i⟫=
      ∫ n : Sphere,(polarized a n i : ℂ)*SphereReactionKernel.wave (-k) x n ∂angularMeasure :=
  coefficient_integral _ (polarized_tangent a) k x i

end OQ14.PlaneFieldCoefficients

#print axioms OQ14.PlaneFieldCoefficients.embed_inner
#print axioms OQ14.PlaneFieldCoefficients.inner_projected
#print axioms OQ14.PlaneFieldCoefficients.coefficient_integral
#print axioms OQ14.PlaneFieldCoefficients.smul_tangent
#print axioms OQ14.PlaneFieldCoefficients.polarized_tangent
#print axioms OQ14.PlaneFieldCoefficients.mode_coefficient
