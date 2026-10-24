import SourcePairedSmallness
import HalfTurnReactionBridge
import ParityMaterialField

/-! On the proper-half-turn-invariant source sector, the clamped central-inversion limit operator of
the paired shells equals the wall-reflection parity reaction operators with gains q^(2n)-1 and
q^(-2n)-1, so the limiting effective inclusion block equals the explicit parity material block with
B = q^n. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace OQ14.SourcePairedWallKernel
open Filter Topology Metric MeasureTheory OQ14.Maxwell OQ14.DynamicConvolution OQ14.SphereReactionKernel
open OQ14.ShellInclusionVolume OQ14.SourcePairedReduction OQ14.HalfTurnMaxwellParity
open PhysicalReactionLimit (Region)
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Space := Maxwell.Space

/-- The actual material source of a weighted vector, as a field. -/
def sourceField (ci : Coefficient) (u : VectorL2) : Field := fun y j => DynamicVolume.source ci u j y

theorem integrable_central (e : Bool) (k : ℝ) (ρ : Field) (hρ : ∀ j, Integrable (fun y => ρ y j))
    (x : Space) (i j : Fin 3) : Integrable (fun y => HalfTurnReactionBridge.central e k x y i j*ρ y j) := by
  have h1 := HalfTurnReactionBridge.integrable_J k ρ hρ x i j
  have h2 : Integrable (fun y => J k (x+y) i j*ρ y j) :=
    (hρ j).bdd_mul ((J_continuous k i j).comp (continuous_const.add continuous_id)).aestronglyMeasurable
      ⟨entryBound k,fun _ => J_bound k _ i j⟩
  have : (fun y => HalfTurnReactionBridge.central e k x y i j*ρ y j)=
      fun y => (Complex.I/2)*(J k (x-y) i j*ρ y j)+((Complex.I/2)*(if e then 1 else -1 : ℂ))*(J k (x+y) i j*ρ y j) := by
    funext y
    simp only [HalfTurnReactionBridge.central]
    ring
  rw [this]
  exact (h1.const_mul _).add (h2.const_mul _)

section Inclusion
variable (q : ℝ) (hq : 1≤q) (n : ℕ) (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
  (b : ℝ) (hb : 0<b) (hcar : ∀ x ∈ d.carrier,‖x‖ ≤ b)
include hcar

/-- On invariant sources the clamped central-inversion limit operator is the gain combination of the
wall-reflection parity reaction operators. -/
theorem limitingOperator_invariant (u : VectorL2) (hinv : Invariant (sourceField ci u)) :
    SourcePairedCore.limitingOperator ci d q hq n b hb u=
      (((q^(2*n) : ℝ) : ℂ)-1) • ParityReactionVolume.operator d true 1 u+
        ((((q^(2*n))⁻¹ : ℝ) : ℂ)-1) • ParityReactionVolume.operator d false 1 u := by
  apply MaterialVolumeConverse.vector_ext
  intro i
  have hs : ∀ j, Integrable (fun y => sourceField ci u y j) := fun j =>
    DynamicVolume.source_integrable ci u b (inclusion_vanish ci d b hcar) j
  have hL := BoundedMaterialKernel.component_operator_ae d
    (fun i j => CompactCoreKernel.extension b hb (SourcePairedCore.limitMap q hq n b i j)) u i
  have hT := ParityReactionVolume.operator_actual d true 1 u i
  have hF := ParityReactionVolume.operator_actual d false 1 u i
  filter_upwards [hL,NewtonL2.physicalCoordinate_ae
      ((((q^(2*n) : ℝ) : ℂ)-1) • ParityReactionVolume.operator d true 1 u+
        ((((q^(2*n))⁻¹ : ℝ) : ℂ)-1) • ParityReactionVolume.operator d false 1 u) i,
    VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
      (Lp.coeFn_add ((((q^(2*n) : ℝ) : ℂ)-1) • ParityReactionVolume.operator d true 1 u)
        (((((q^(2*n))⁻¹ : ℝ) : ℂ)-1) • ParityReactionVolume.operator d false 1 u)),
    VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
      (Lp.coeFn_smul ((((q^(2*n) : ℝ) : ℂ)-1)) (ParityReactionVolume.operator d true 1 u)),
    VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
      (Lp.coeFn_smul (((((q^(2*n))⁻¹ : ℝ) : ℂ)-1)) (ParityReactionVolume.operator d false 1 u)),
    hT,hF] with x e0 e1 e2 e3 e4 eT eF
  change component i (BoundedMaterialKernel.operator d
    (fun i j => CompactCoreKernel.extension b hb (SourcePairedCore.limitMap q hq n b i j)) u) x=_
  rw [e0,e1,e2,Pi.add_apply,e3,e4]
  simp only [Pi.smul_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  rw [eT,eF]
  by_cases hxc : x ∈ d.carrier
  · have hker : ∀ j, (∫ y, (CompactCoreKernel.extension b hb (SourcePairedCore.limitMap q hq n b i j)).value x y*
        component j (StaticCoefficient.sqrtMultiplier ci u) y)=
        (((q^(2*n) : ℝ) : ℂ)-1)*(∫ y, HalfTurnReactionBridge.central true 1 x y i j*DynamicVolume.source ci u j y)+
          ((((q^(2*n))⁻¹ : ℝ) : ℂ)-1)*(∫ y, HalfTurnReactionBridge.central false 1 x y i j*DynamicVolume.source ci u j y) := by
      intro j
      have hiT := (integrable_central true 1 (sourceField ci u) hs x i j).const_mul ((((q^(2*n) : ℝ) : ℂ)-1))
      have hiF := (integrable_central false 1 (sourceField ci u) hs x i j).const_mul (((((q^(2*n))⁻¹ : ℝ) : ℂ)-1))
      simp only [sourceField] at hiT hiF
      rw [← integral_const_mul,← integral_const_mul,← integral_add hiT hiF]
      apply integral_congr_ae
      filter_upwards [StaticNewton.material_source_ae ci u j] with y hy
      rw [component_apply,hy]
      by_cases hyc : y ∈ d.carrier
      · have hp : (x,y) ∈ closedBall (0 : Space × Space) b :=
          SourceCoreOperator.pair_mem_region b x y (hcar x hxc) (hcar y hyc)
        rw [CompactCoreKernel.extension_actual b hb _ ⟨(x,y),hp⟩,
          SourcePairedCore.limitMap_apply q hq n b hb.le i j ⟨(x,y),hp⟩,
          HalfTurnReactionBridge.paired_kernel]
        simp only [sourceField,DynamicVolume.source]
        ring
      · simp only [sourceField,DynamicVolume.source,d.carrierZero y hyc,Real.sqrt_zero,Complex.ofReal_zero,
          zero_mul,mul_zero,add_zero]
    have hcwT := HalfTurnReactionBridge.central_eq_wall true 1 (sourceField ci u) hs hinv x i
    have hcwF := HalfTurnReactionBridge.central_eq_wall false 1 (sourceField ci u) hs hinv x i
    simp only [sourceField] at hcwT hcwF
    rw [← hcwT,← hcwF]
    simp only [hker,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl (fun j _ => by ring)
  · simp [d.carrierZero x hxc]

/-- On invariant sources the limiting effective inclusion block is the explicit parity material block
with gain parameter B = q^n at unit frequency. -/
theorem limitEffective_invariant (u : VectorL2) (hinv : Invariant (sourceField ci u)) :
    limitEffective q hq n ci d b hb u=ParityMaterialField.block d 1 (q^n) u := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hB2 : (((q^n)^2-1 : ℝ) : ℂ)=((q^(2*n) : ℝ) : ℂ)-1 := by
    push_cast
    rw [← pow_mul,mul_comm]
  have hBi : (((q^n)⁻¹^2-1 : ℝ) : ℂ)=(((q^(2*n))⁻¹ : ℝ) : ℂ)-1 := by
    push_cast
    rw [inv_pow,← pow_mul,mul_comm]
  rw [ParityMaterialField.block_eq,limitEffective,ContinuousLinearMap.sub_apply,
    limitingOperator_invariant q hq n ci d b hb hcar u hinv,
    ShellInclusionTruncation.volumeBlock_radius_independent ci 1 b d.radius (inclusion_vanish ci d b hcar) d.ballZero,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply,hB2,hBi]
  abel

/-- A parity solution of invariant weighted source solves the limiting effective equation. -/
theorem limitEffective_of_parity (u f : VectorL2) (hinv : Invariant (sourceField ci u))
    (hu : ParityMaterialField.block d 1 (q^n) u=f) : limitEffective q hq n ci d b hb u=f := by
  rw [limitEffective_invariant q hq n ci d b hb hcar u hinv,hu]

/-- When the limiting effective block is a unit, the limiting effective solution of a datum equals any
parity solution of that datum whose weighted source is invariant. -/
theorem limit_solution_eq_parity (hL : IsUnit (limitEffective q hq n ci d b hb)) (u f : VectorL2)
    (hinv : Invariant (sourceField ci u)) (hu : ParityMaterialField.block d 1 (q^n) u=f) :
    Ring.inverse (limitEffective q hq n ci d b hb) f=u := by
  rw [← limitEffective_of_parity q hq n ci d b hb hcar u f hinv hu]
  exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L u)
    (Ring.inverse_mul_cancel (limitEffective q hq n ci d b hb) hL)

end Inclusion
end OQ14.SourcePairedWallKernel
#print axioms OQ14.SourcePairedWallKernel.integrable_central
#print axioms OQ14.SourcePairedWallKernel.limitingOperator_invariant
#print axioms OQ14.SourcePairedWallKernel.limitEffective_invariant
#print axioms OQ14.SourcePairedWallKernel.limitEffective_of_parity
#print axioms OQ14.SourcePairedWallKernel.limit_solution_eq_parity
