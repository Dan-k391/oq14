import Packet06MaterialHolomorphic
import Packet06LocalPencil

/-! The norm-convergent material pencil is an exact preconditioning of the
actual electric volume equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace OQ14.Packet06ReducedPencil
open MeasureTheory Filter Set Metric Packet06MaterialStatic Packet06MaterialPencil
open Packet06LocalPencil StaticCoefficient
open scoped Topology
abbrev V := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

def reduced (c : Coefficient) (z : ℂ) (R : ℝ) : V →L[ℂ] V :=
  1-compactPart c z R

theorem unweighted_split (c : Coefficient) (z : ℂ) (R : ℝ) :
    unweighted c z R = staticBlock c-ComplexConvolutionAnalytic.operator z (2*R)*materialMultiplier c := by
  unfold unweighted kernel staticBlock materialMultiplier NewtonL2.newtonOperator
  rw [show R+R=2*R by ring]
  noncomm_ring

theorem actual_factorization (c : Coefficient) (z : ℂ) (R : ℝ) :
    staticBlock c * reduced c z R = unweighted c z R := by
  rw [reduced,mul_sub,mul_one,compactPart,←mul_assoc,←mul_assoc,
    Ring.mul_inverse_cancel _ (staticBlock_isUnit c),one_mul,←unweighted_split]

theorem reduced_isUnit_iff (c : Coefficient) (z : ℂ) (R : ℝ) :
    IsUnit (reduced c z R) ↔ IsUnit (unweighted c z R) := by
  constructor
  · intro h
    rw [←actual_factorization]
    exact (staticBlock_isUnit c).mul h
  · intro h
    have he : reduced c z R = Ring.inverse (staticBlock c) * unweighted c z R := by
      rw [←actual_factorization,←mul_assoc,Ring.inverse_mul_cancel _ (staticBlock_isUnit c),one_mul]
    rw [he]
    exact (staticBlock_isUnit c).ringInverse.mul h

theorem weighted_isUnit_iff_reduced (c : Coefficient) (z : ℂ) (R : ℝ) :
    IsUnit (ComplexConvolutionAnalytic.volumeBlock c z R) ↔ IsUnit (reduced c z R) := by
  rw [reduced_isUnit_iff,weighted_block_eq,unweighted]
  simpa only [mul_assoc] using Packet06WeightedTransport.isUnit_switch
    (StaticCoefficient.sqrtMultiplier c) (kernel z R R*StaticCoefficient.sqrtMultiplier c)

theorem kernel_iff (c : Coefficient) (z : ℂ) (R : ℝ) (u : V) :
    reduced c z R u = 0 ↔ unweighted c z R u = 0 := by
  constructor
  · intro h
    rw [←actual_factorization,ContinuousLinearMap.mul_apply,h,map_zero]
  · intro h
    have he := congrArg (fun v : V => Ring.inverse (staticBlock c) v) h
    rw [←actual_factorization] at he
    have hi := congrArg (fun L : V →L[ℂ] V => L (reduced c z R u))
      (Ring.inverse_mul_cancel _ (staticBlock_isUnit c))
    change Ring.inverse (staticBlock c) (staticBlock c (reduced c z R u)) = reduced c z R u at hi
    simpa only [ContinuousLinearMap.mul_apply,hi,map_zero] using he

theorem reduced_differentiable (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) :
    Differentiable ℂ (fun z => reduced c z R) :=
  (differentiable_const _).sub (Packet06MaterialHolomorphic.compactPart_differentiable c R hR)

theorem reduced_locally_uniform (c : ℕ → Coefficient) (c₀ : Coefficient) (D R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (n : ℕ) (x : Maxwell.Space), x ∉ closedBall 0 R → (c n).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c₀.value (VectorFourier.coordinateMap x) = 0) :
    TendstoLocallyUniformlyOn (fun n z => reduced (c n) z R) (fun z => reduced c₀ z R) atTop univ := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mpr
  intro A _ hA
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [compactPart_uniform c c₀ D R hR hb hb₀ ha hc hc₀ A hA ε hε] with n hn z hz
  have he : reduced c₀ z R-reduced (c n) z R = compactPart (c n) z R-compactPart c₀ z R := by
    unfold reduced
    abel
  simpa only [dist_eq_norm,he] using hn z hz

end OQ14.Packet06ReducedPencil
#print axioms OQ14.Packet06ReducedPencil.unweighted_split
#print axioms OQ14.Packet06ReducedPencil.actual_factorization
#print axioms OQ14.Packet06ReducedPencil.reduced_isUnit_iff
#print axioms OQ14.Packet06ReducedPencil.weighted_isUnit_iff_reduced
#print axioms OQ14.Packet06ReducedPencil.kernel_iff
#print axioms OQ14.Packet06ReducedPencil.reduced_differentiable
#print axioms OQ14.Packet06ReducedPencil.reduced_locally_uniform
