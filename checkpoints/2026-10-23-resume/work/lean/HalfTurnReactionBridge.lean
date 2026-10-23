import HalfTurnReactionKernel
import ParityMaterialField

/-! Literal central and wall reaction integrals agree in the proper-half-turn source sector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.HalfTurnReactionBridge
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SphereReactionKernel
open OQ14.HalfTurnMaxwellParity OQ14.HalfTurnReactionKernel
abbrev Space := Maxwell.Space

def central (e : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) : ℂ :=
  (Complex.I/2)*(J k (x-y) i j+(if e then 1 else -1 : ℂ)*J k (x+y) i j)

theorem integrable_J (k : ℝ) (ρ : Field) (hρ : ∀ j, Integrable (fun y => ρ y j))
    (x : Space) (i j : Fin 3) : Integrable (fun y => J k (x-y) i j*ρ y j) :=
  (hρ j).bdd_mul ((J_continuous k i j).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    ⟨entryBound k,fun _ => J_bound k _ i j⟩

theorem potential_neg (k : ℝ) (ρ : Field) (x : Space) (i : Fin 3) :
    potential k ρ (-x) i=∑ j : Fin 3, ∫ y : Space, J k (x+y) i j*ρ y j := by
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards with y
  rw [show -x-y= -(x+y) by abel,J_neg]

theorem central_integral (e : Bool) (k : ℝ) (ρ : Field) (hρ : ∀ j, Integrable (fun y => ρ y j))
    (x : Space) (i : Fin 3) :
    (∑ j : Fin 3, ∫ y : Space, central e k x y i j*ρ y j)=
      (Complex.I/2)*(potential k ρ x i+(if e then 1 else -1 : ℂ)*potential k ρ (-x) i) := by
  have he (j : Fin 3) : (∫ y : Space, central e k x y i j*ρ y j)=
      (Complex.I/2)*((∫ y : Space, J k (x-y) i j*ρ y j)+
        (if e then 1 else -1 : ℂ)*(∫ y : Space, J k (x+y) i j*ρ y j)) := by
    have hp : Integrable (fun y : Space => J k (x+y) i j*ρ y j) :=
      (hρ j).bdd_mul ((J_continuous k i j).comp (continuous_const.add continuous_id)).aestronglyMeasurable
        ⟨entryBound k,fun _ => J_bound k _ i j⟩
    simp_rw [central,mul_assoc,add_mul]
    simp_rw [mul_assoc]
    rw [integral_const_mul,integral_add (integrable_J k ρ hρ x i j) (hp.const_mul _),integral_const_mul]
  simp_rw [he]
  rw [potential_neg]
  simp only [potential,Finset.mul_sum,Finset.sum_add_distrib,mul_add]

theorem wall_integral (e : Bool) (k : ℝ) (ρ : Field) (hρ : ∀ j, Integrable (fun y => ρ y j))
    (x : Space) (i : Fin 3) :
    (∑ j : Fin 3, ∫ y : Space, reaction e k x y i j*ρ y j)=
      (Complex.I/2)*(potential k ρ x i+(if e then -1 else 1 : ℂ)*(sign i : ℂ)*potential k ρ (reflect x) i) := by
  have he (j : Fin 3) : (∫ y : Space, reaction e k x y i j*ρ y j)=
      (Complex.I/2)*((∫ y : Space, J k (x-y) i j*ρ y j)+
        ((if e then -1 else 1 : ℂ)*(sign i : ℂ))*(∫ y : Space, J k (reflect x-y) i j*ρ y j)) := by
    simp_rw [reaction,mul_assoc,add_mul]
    simp_rw [mul_assoc]
    rw [integral_const_mul,integral_add (integrable_J k ρ hρ x i j)
      (((integrable_J k ρ hρ (reflect x) i j).const_mul _).const_mul _),integral_const_mul,integral_const_mul]
  simp_rw [he]
  simp only [potential,Finset.mul_sum,Finset.sum_add_distrib,mul_add]

theorem central_eq_wall (e : Bool) (k : ℝ) (ρ : Field) (hρ : ∀ j, Integrable (fun y => ρ y j))
    (hs : Invariant ρ) (x : Space) (i : Fin 3) :
    (∑ j : Fin 3, ∫ y : Space, central e k x y i j*ρ y j)=
      ∑ j : Fin 3, ∫ y : Space, reaction e k x y i j*ρ y j := by
  rw [central_integral e k ρ hρ,wall_integral e k ρ hρ,
    inversion_wall _ (potential_invariant k ρ hs)]
  cases e <;> simp

theorem paired_kernel (q : ℝ) (n : ℕ) (x y : Space) (i j : Fin 3) :
    VectorLimitIdentification.kernel q n i j (x,y)=
      (((q^(2*n) : ℝ) : ℂ)-1)*central true 1 x y i j+
        ((((q^(2*n))⁻¹ : ℝ) : ℂ)-1)*central false 1 x y i j := by
  simp only [VectorLimitIdentification.kernel,CentralReactionExpansion.evenKernel,
    CentralReactionExpansion.oddKernel,central,if_true,Bool.false_eq_true,if_false,sub_neg_eq_add]
  ring

end OQ14.HalfTurnReactionBridge
#print axioms OQ14.HalfTurnReactionBridge.integrable_J
#print axioms OQ14.HalfTurnReactionBridge.potential_neg
#print axioms OQ14.HalfTurnReactionBridge.central_integral
#print axioms OQ14.HalfTurnReactionBridge.wall_integral
#print axioms OQ14.HalfTurnReactionBridge.central_eq_wall
#print axioms OQ14.HalfTurnReactionBridge.paired_kernel
