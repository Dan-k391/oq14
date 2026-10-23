import HalfTurnMaxwellParity
import HarmonicHalfTurn
import SphereAngularSymmetry
import VectorLimitIdentification

/-! Orthogonal covariance of the literal sphere tensor and its actual volume potential. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.HalfTurnReactionKernel
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SphereReactionKernel
open OQ14.SphereAngularSymmetry OQ14.HalfTurnMaxwellParity
open scoped Topology InnerProductSpace
abbrev Space := Maxwell.Space

theorem rotation_eq (x : Space) : HarmonicHalfTurn.rotation x=halfTurn x := by
  rw [HarmonicHalfTurn.rotation_apply,halfTurn_apply]

theorem rotation_coordinate (x : Space) (i : Fin 3) :
    HarmonicHalfTurn.rotation x i= -sign i*x i := by
  rw [HarmonicHalfTurn.rotation_apply]
  change -(sign i*x i)= -sign i*x i
  ring

theorem J_rotation (k : ℝ) (x : Space) (i j : Fin 3) :
    J k (HarmonicHalfTurn.rotation x) i j=(sign i : ℂ)*(sign j : ℂ)*J k x i j := by
  have ha (θ : Sphere) : amplitude (sphereMap HarmonicHalfTurn.rotation θ) i j=
      (sign i : ℂ)*(sign j : ℂ)*amplitude θ i j := by
    change (if i=j then 1 else 0 : ℂ)-
      ((HarmonicHalfTurn.rotation θ i : ℝ) : ℂ)*((HarmonicHalfTurn.rotation θ j : ℝ) : ℂ)=_
    simp only [rotation_coordinate,Complex.ofReal_mul,Complex.ofReal_neg]
    fin_cases i <;> fin_cases j <;> simp [amplitude,sign]
  have hw (θ : Sphere) : wave k (HarmonicHalfTurn.rotation x) (sphereMap HarmonicHalfTurn.rotation θ)=wave k x θ := by
    unfold wave
    congr 3
    exact congrArg (fun t : ℝ => k*t) (HarmonicHalfTurn.rotation.inner_map_map θ x)
  have hc := (measurePreserving_sphereMap HarmonicHalfTurn.rotation).integral_comp
    (sphereMap HarmonicHalfTurn.rotation).measurableEmbedding
    (fun θ => amplitude θ i j*wave k (HarmonicHalfTurn.rotation x) θ)
  change (∫ θ : Sphere, amplitude (sphereMap HarmonicHalfTurn.rotation θ) i j*
    wave k (HarmonicHalfTurn.rotation x) (sphereMap HarmonicHalfTurn.rotation θ) ∂surface)=_ at hc
  simp only [ha,hw,mul_assoc,integral_const_mul] at hc
  change (sign i : ℂ)*((sign j : ℂ)*(∫ θ : Sphere, amplitude θ i j*wave k x θ ∂surface))=
    ∫ θ : Sphere, amplitude θ i j*wave k (HarmonicHalfTurn.rotation x) θ ∂surface at hc
  unfold J
  rw [←hc]
  ring

theorem J_neg (k : ℝ) (x : Space) (i j : Fin 3) : J k (-x) i j=J k x i j := by
  let L := LinearIsometryEquiv.neg ℝ (E := Space)
  have ha (θ : Sphere) : amplitude (sphereMap L θ) i j=amplitude θ i j := by
    change (if i=j then 1 else 0 : ℂ)-((-θ.val i : ℝ) : ℂ)*((-θ.val j : ℝ) : ℂ)=_
    simp [amplitude]
  have hw (θ : Sphere) : wave k (-x) (sphereMap L θ)=wave k x θ := by
    unfold wave
    change Complex.exp (((k*⟪-θ.val,-x⟫_ℝ : ℝ) : ℂ)*Complex.I)=_
    rw [inner_neg_neg]
  have hc := (measurePreserving_sphereMap L).integral_comp (sphereMap L).measurableEmbedding
    (fun θ => amplitude θ i j*wave k (-x) θ)
  change (∫ θ : Sphere, amplitude (sphereMap L θ) i j*wave k (-x) (sphereMap L θ) ∂surface)=_ at hc
  simp only [ha,hw] at hc
  change (∫ θ : Sphere, amplitude θ i j*wave k x θ ∂surface)=
    ∫ θ : Sphere, amplitude θ i j*wave k (-x) θ ∂surface at hc
  unfold J
  rw [hc]

def potential (k : ℝ) (ρ : Field) : Field := fun x i =>
  ∑ j : Fin 3, ∫ y : Space, J k (x-y) i j*ρ y j

theorem potential_invariant (k : ℝ) (ρ : Field) (hρ : Invariant ρ) : Invariant (potential k ρ) := by
  intro x i
  change (∑ j : Fin 3, ∫ y : Space, J k (halfTurn x-y) i j*ρ y j)=_
  have he (j : Fin 3) : (∫ y : Space, J k (halfTurn x-y) i j*ρ y j)=
      -(sign i : ℂ)*(∫ y : Space, J k (x-y) i j*ρ y j) := by
    have hc := HarmonicHalfTurn.rotation.measurePreserving.integral_comp
      HarmonicHalfTurn.rotation.toHomeomorph.measurableEmbedding
      (fun y : Space => J k (halfTurn x-y) i j*ρ y j)
    rw [←hc]
    have hi (y : Space) : J k (halfTurn x-HarmonicHalfTurn.rotation y) i j*
        ρ (HarmonicHalfTurn.rotation y) j= -(sign i : ℂ)*(J k (x-y) i j*ρ y j) := by
      rw [←rotation_eq,←map_sub,J_rotation,rotation_eq,hρ]
      have hs : (sign j : ℂ)^2=1 := by unfold sign; split_ifs <;> norm_num
      linear_combination -((sign i : ℂ)*J k (x-y) i j*ρ y j)*hs
    simp_rw [hi]
    rw [integral_const_mul]
  simp_rw [he]
  rw [←Finset.mul_sum]
  rfl

end OQ14.HalfTurnReactionKernel
#print axioms OQ14.HalfTurnReactionKernel.rotation_eq
#print axioms OQ14.HalfTurnReactionKernel.rotation_coordinate
#print axioms OQ14.HalfTurnReactionKernel.J_rotation
#print axioms OQ14.HalfTurnReactionKernel.J_neg
#print axioms OQ14.HalfTurnReactionKernel.potential_invariant
