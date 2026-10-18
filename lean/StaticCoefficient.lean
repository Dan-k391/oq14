import VectorFourier
import StaticVolume
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual material multiplication and the positive static block

A bounded measurable nonnegative susceptibility defines actual multiplication
by its real square root on vector L2. The static block uses this multiplication
and the constructed physical longitudinal Fourier projection.
No identification with the Newton convolution is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.StaticCoefficient

open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate

abbrev Space := VectorFourier.Frequency
abbrev Vector := VectorFourier.Vector
abbrev VectorL2 := VectorFourier.VectorL2

structure Coefficient where
  value : Space → ℝ
  bound : ℝ
  measurable : Measurable value
  nonnegative : ∀ x, 0 ≤ value x
  bounded : ∀ x, value x ≤ bound

theorem bound_nonnegative (c : Coefficient) : 0 ≤ c.bound :=
  (c.nonnegative 0).trans (c.bounded 0)

theorem sqrt_value_bound (c : Coefficient) (x : Space) :
    ‖(Real.sqrt (c.value x) : ℂ)‖ ≤ Real.sqrt c.bound := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (c.bounded x)

theorem sqrt_memLp (c : Coefficient) (f : VectorL2) :
    MemLp (fun x => (Real.sqrt (c.value x) : ℂ) • f x) 2 (volume : Measure Space) := by
  apply (Lp.memLp f).of_le_mul
  · exact ((Complex.continuous_ofReal.measurable.comp
      (Real.continuous_sqrt.measurable.comp c.measurable)).aestronglyMeasurable).smul
        (Lp.memLp f).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (sqrt_value_bound c x) (norm_nonneg _)

def applySqrt (c : Coefficient) (f : VectorL2) : VectorL2 :=
  (sqrt_memLp c f).toLp (fun x => (Real.sqrt (c.value x) : ℂ) • f x)

theorem applySqrt_ae (c : Coefficient) (f : VectorL2) :
    applySqrt c f =ᵐ[volume] fun x => (Real.sqrt (c.value x) : ℂ) • f x :=
  (sqrt_memLp c f).coeFn_toLp

theorem applySqrt_add (c : Coefficient) (f g : VectorL2) :
    applySqrt c (f + g) = applySqrt c f + applySqrt c g := by
  apply Lp.ext
  filter_upwards [applySqrt_ae c (f + g), applySqrt_ae c f, applySqrt_ae c g,
    Lp.coeFn_add f g, Lp.coeFn_add (applySqrt c f) (applySqrt c g)] with x hfg hf hg ha hb
  rw [hfg, ha, hb]
  simp only [Pi.add_apply, hf, hg, smul_add]

theorem applySqrt_smul (c : Coefficient) (z : ℂ) (f : VectorL2) :
    applySqrt c (z • f) = z • applySqrt c f := by
  apply Lp.ext
  filter_upwards [applySqrt_ae c (z • f), applySqrt_ae c f,
    Lp.coeFn_smul z f, Lp.coeFn_smul z (applySqrt c f)] with x hzf hf ha hb
  rw [hzf, ha, hb]
  simp only [Pi.smul_apply, hf]
  exact smul_comm _ _ _

theorem applySqrt_norm (c : Coefficient) (f : VectorL2) :
    ‖applySqrt c f‖ ≤ Real.sqrt c.bound * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [applySqrt_ae c f] with x hx
  rw [hx, norm_smul]
  exact mul_le_mul_of_nonneg_right (sqrt_value_bound c x) (norm_nonneg _)

def sqrtLinear (c : Coefficient) : VectorL2 →ₗ[ℂ] VectorL2 where
  toFun := applySqrt c
  map_add' := applySqrt_add c
  map_smul' := applySqrt_smul c

def sqrtMultiplier (c : Coefficient) : VectorL2 →L[ℂ] VectorL2 :=
  (sqrtLinear c).mkContinuous (Real.sqrt c.bound) (applySqrt_norm c)

theorem sqrtMultiplier_ae (c : Coefficient) (f : VectorL2) :
    sqrtMultiplier c f =ᵐ[volume] fun x => (Real.sqrt (c.value x) : ℂ) • f x :=
  applySqrt_ae c f

theorem sqrtMultiplier_norm_le (c : Coefficient) :
    ‖sqrtMultiplier c‖ ≤ Real.sqrt c.bound := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  exact applySqrt_norm c

theorem sqrtMultiplier_symmetric (c : Coefficient) (f g : VectorL2) :
    ⟪sqrtMultiplier c f, g⟫_ℂ = ⟪f, sqrtMultiplier c g⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sqrtMultiplier_ae c f, sqrtMultiplier_ae c g] with x hf hg
  rw [hf, hg]
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

theorem sqrtMultiplier_selfAdjoint (c : Coefficient) : IsSelfAdjoint (sqrtMultiplier c) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (sqrtMultiplier_symmetric c)

theorem sqrtMultiplier_square_ae (c : Coefficient) (f : VectorL2) :
    sqrtMultiplier c (sqrtMultiplier c f) =ᵐ[volume] fun x => (c.value x : ℂ) • f x := by
  filter_upwards [sqrtMultiplier_ae c (sqrtMultiplier c f), sqrtMultiplier_ae c f] with x hff hf
  rw [hff, hf, ← mul_smul, ← Complex.ofReal_mul, Real.mul_self_sqrt (c.nonnegative x)]

def weightedBlock (c : Coefficient) : VectorL2 →L[ℂ] VectorL2 :=
  1 + sqrtMultiplier c ∘L VectorFourier.physicalProjection ∘L sqrtMultiplier c

theorem weightedBlock_eq (c : Coefficient) :
    weightedBlock c = StaticVolume.block VectorFourier.physicalProjection (sqrtMultiplier c) := by
  simp only [weightedBlock, StaticVolume.block, (sqrtMultiplier_selfAdjoint c).adjoint_eq]

theorem weightedBlock_ae (c : Coefficient) (f : VectorL2) :
    weightedBlock c f =ᵐ[volume] fun x => f x +
      (Real.sqrt (c.value x) : ℂ) • VectorFourier.physicalProjection (sqrtMultiplier c f) x := by
  change f + sqrtMultiplier c (VectorFourier.physicalProjection (sqrtMultiplier c f)) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add f (sqrtMultiplier c (VectorFourier.physicalProjection
    (sqrtMultiplier c f))), sqrtMultiplier_ae c (VectorFourier.physicalProjection
    (sqrtMultiplier c f))] with x ha hs
  rw [ha]
  simp only [Pi.add_apply, hs]

theorem weightedBlock_coercive (c : Coefficient) (f : VectorL2) :
    ‖f‖ ^ 2 ≤ (⟪weightedBlock c f, f⟫_ℂ).re := by
  rw [weightedBlock_eq]
  exact StaticVolume.block_coercive _ _ VectorFourier.physicalProjection_positive f

theorem weightedBlock_isUnit (c : Coefficient) : IsUnit (weightedBlock c) := by
  rw [weightedBlock_eq]
  exact StaticVolume.block_isUnit _ _ VectorFourier.physicalProjection_positive

theorem weightedBlock_inverse_norm_le (c : Coefficient) :
    ‖Ring.inverse (weightedBlock c)‖ ≤ 1 := by
  rw [weightedBlock_eq]
  exact StaticVolume.block_inverse_norm_le _ _ VectorFourier.physicalProjection_positive

theorem weightedBlock_perturbation_isUnit (c : Coefficient) (Q : VectorL2 →L[ℂ] VectorL2)
    (hQ : ‖Q‖ < 1) : IsUnit (weightedBlock c - Q) := by
  rw [weightedBlock_eq]
  exact StaticVolume.block_perturbation_isUnit _ _ Q VectorFourier.physicalProjection_positive hQ

theorem weightedBlock_perturbation_inverse (c : Coefficient) (Q : VectorL2 →L[ℂ] VectorL2)
    (hQ : ‖Q‖ < 1) : ‖Ring.inverse (weightedBlock c - Q)‖ ≤ (1 - ‖Q‖)⁻¹ := by
  rw [weightedBlock_eq]
  exact StaticVolume.block_perturbation_inverse_bound _ _ Q
    VectorFourier.physicalProjection_positive hQ

theorem weightedBlock_residual_bound (c : Coefficient) (Q : VectorL2 →L[ℂ] VectorL2)
    (hQ : ‖Q‖ < 1) (u v f : VectorL2) (hsol : (weightedBlock c - Q) u = f) :
    ‖u - v‖ ≤ (1 - ‖Q‖)⁻¹ * ‖f - (weightedBlock c - Q) v‖ := by
  rw [weightedBlock_eq] at hsol ⊢
  exact StaticVolume.polarization_residual_bound _ _ Q
    VectorFourier.physicalProjection_positive hQ u v f hsol

end OQ14.StaticCoefficient

#print axioms OQ14.StaticCoefficient.bound_nonnegative
#print axioms OQ14.StaticCoefficient.sqrt_value_bound
#print axioms OQ14.StaticCoefficient.sqrt_memLp
#print axioms OQ14.StaticCoefficient.applySqrt_ae
#print axioms OQ14.StaticCoefficient.applySqrt_add
#print axioms OQ14.StaticCoefficient.applySqrt_smul
#print axioms OQ14.StaticCoefficient.applySqrt_norm
#print axioms OQ14.StaticCoefficient.sqrtMultiplier_ae
#print axioms OQ14.StaticCoefficient.sqrtMultiplier_norm_le
#print axioms OQ14.StaticCoefficient.sqrtMultiplier_symmetric
#print axioms OQ14.StaticCoefficient.sqrtMultiplier_selfAdjoint
#print axioms OQ14.StaticCoefficient.sqrtMultiplier_square_ae
#print axioms OQ14.StaticCoefficient.weightedBlock_eq
#print axioms OQ14.StaticCoefficient.weightedBlock_ae
#print axioms OQ14.StaticCoefficient.weightedBlock_coercive
#print axioms OQ14.StaticCoefficient.weightedBlock_isUnit
#print axioms OQ14.StaticCoefficient.weightedBlock_inverse_norm_le
#print axioms OQ14.StaticCoefficient.weightedBlock_perturbation_isUnit
#print axioms OQ14.StaticCoefficient.weightedBlock_perturbation_inverse
#print axioms OQ14.StaticCoefficient.weightedBlock_residual_bound
