import HerglotzPointTail

/-! Genuine mixed point-source and regular Herglotz kernel tails. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.MixedPointTail
open MeasureTheory Metric Set SphereReactionKernel SphereMagneticKernel HerglotzPointTail
open Maxwell (conjugate)
open scoped ComplexConjugate Topology

def electricRegular (k : ℝ) (x y z : Space) (j m : Fin 3) : ℂ :=
  crossProduct (fun i => DyadicKernel.dyadic k (x-y) i j)
    (conjugate (fun i => K k (x-z) i m)) 2

def regularMagnetic (k : ℝ) (x y z : Space) (j m : Fin 3) : ℂ :=
  crossProduct (fun i => J k (x-y) i j)
    (conjugate (fun i => magneticDyadic k (x-z) i m)) 2

theorem electric_expansion (k : ℝ) (x y z : Space) (hk : k ≠ 0) (hz : x-z ≠ 0) (j m : Fin 3) :
    electricRegular k x y z j m = (Complex.I/2)*
      (outgoingFlux k k x y z j m+outgoingFlux k (-k) x y z j m) := by
  unfold electricRegular outgoingFlux
  change DyadicKernel.dyadic k (x-y) 0 j*star (K k (x-z) 1 m)-
    DyadicKernel.dyadic k (x-y) 1 j*star (K k (x-z) 0 m)=_
  rw [K_magnetic k (x-z) hk hz 1 m, K_magnetic k (x-z) hk hz 0 m]
  simp [cross_apply, conjugate, Complex.star_def, Complex.conj_I, Complex.conj_ofNat]
  field_simp
  ring_nf
  norm_num [Complex.I_sq, Complex.conj_ofNat]
  ring

theorem magnetic_expansion (k : ℝ) (x y z : Space) (hk : k ≠ 0) (hy : x-y ≠ 0) (j m : Fin 3) :
    regularMagnetic k x y z j m = -(Complex.I/2)*
      (outgoingFlux k k x y z j m-outgoingFlux (-k) k x y z j m) := by
  unfold regularMagnetic outgoingFlux
  change J k (x-y) 0 j*star (magneticDyadic k (x-z) 1 m)-
    J k (x-y) 1 j*star (magneticDyadic k (x-z) 0 m)=_
  rw [SphereDyadicTransform.J_dyadic k (x-y) hk hy 0 j,
    SphereDyadicTransform.J_dyadic k (x-y) hk hy 1 j]
  simp [cross_apply, conjugate]
  field_simp
  ring_nf
  norm_num [Complex.I_sq]
  ring

private theorem norm_half_add (a b : ℂ) (C : ℝ) (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) :
    ‖(Complex.I/2)*(a+b)‖ ≤ C := by
  rw [norm_mul, show ‖(Complex.I/2)‖=(1/2 : ℝ) by norm_num [norm_div]]
  have hn := norm_add_le a b
  linarith

private theorem norm_half_sub (a b : ℂ) (C : ℝ) (ha : ‖a‖ ≤ C) (hb : ‖b‖ ≤ C) :
    ‖-(Complex.I/2)*(a-b)‖ ≤ C := by
  rw [norm_mul, norm_neg, show ‖(Complex.I/2)‖=(1/2 : ℝ) by norm_num [norm_div]]
  have hn := norm_sub_le a b
  linarith

theorem electric_tail (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0) (x y z : Space)
    (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (hp : x 2=0)
    (hy : y ∈ closedBall 0 R) (hz : z ∈ closedBall 0 R) (j m : Fin 3) :
    ‖electricRegular k x y z j m‖ ≤ PointMaxwellTail.tailConstant k k R/‖x‖^3 := by
  have hxz := (ScalarRadiation.distance_lower_bound R hR x z hx hz).2.1
  rw [electric_expansion k x y z hk hxz j m]
  apply norm_half_add
  · exact PointMaxwellTail.flux_tail k k R hR x y z hx hx₂ hp hy hz j m
  · simpa only [PointMaxwellTail.tailConstant, MaxwellPlaneTail.electricErrorConstant,
      MaxwellPlaneTail.magneticErrorConstant, MaxwellPlaneTail.leadingConstant, neg_sq, abs_neg] using
        PointMaxwellTail.flux_tail k (-k) R hR x y z hx hx₂ hp hy hz j m

theorem magnetic_tail (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0) (x y z : Space)
    (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (hp : x 2=0)
    (hy : y ∈ closedBall 0 R) (hz : z ∈ closedBall 0 R) (j m : Fin 3) :
    ‖regularMagnetic k x y z j m‖ ≤ PointMaxwellTail.tailConstant k k R/‖x‖^3 := by
  have hxy := (ScalarRadiation.distance_lower_bound R hR x y hx hy).2.1
  rw [magnetic_expansion k x y z hk hxy j m]
  apply norm_half_sub
  · exact PointMaxwellTail.flux_tail k k R hR x y z hx hx₂ hp hy hz j m
  · simpa only [PointMaxwellTail.tailConstant, MaxwellPlaneTail.electricErrorConstant,
      MaxwellPlaneTail.magneticErrorConstant, MaxwellPlaneTail.leadingConstant, neg_sq, abs_neg] using
        PointMaxwellTail.flux_tail (-k) k R hR x y z hx hx₂ hp hy hz j m

end OQ14.MixedPointTail
#print axioms OQ14.MixedPointTail.electric_expansion
#print axioms OQ14.MixedPointTail.magnetic_expansion
#print axioms OQ14.MixedPointTail.electric_tail
#print axioms OQ14.MixedPointTail.magnetic_tail
