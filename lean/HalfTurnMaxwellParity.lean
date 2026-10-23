import SymmetricScalarWaves
import SolidWaveParity

/-! Actual proper half-turn covariance and the central-inversion wall projection bridge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.HalfTurnMaxwellParity
open OQ14.Maxwell
open OQ14.SphereReactionKernel (reflect sign)

def halfTurn : Space →L[ℝ] Space := -SphereMagneticParity.reflection

theorem halfTurn_apply (x : Space) : halfTurn x= -reflect x := by
  simp only [halfTurn,ContinuousLinearMap.neg_apply,SphereMagneticParity.reflection_apply]

theorem halfTurn_basis (i : Fin 3) : halfTurn (basis i)=(-sign i) • basis i := by
  simp only [halfTurn,ContinuousLinearMap.neg_apply,SphereMagneticParity.reflection_basis,neg_smul]

theorem reflect_reflect (x : Space) : reflect (reflect x)=x := by
  ext i
  fin_cases i <;> simp [reflect,sign]

def Invariant (F : Field) : Prop := ∀ x i,F (halfTurn x) i= -(sign i : ℂ)*F x i

theorem partial_covariant (f : Space → ℂ) (hf : Differentiable ℝ f) (c : ℂ)
    (hc : ∀ x,f (halfTurn x)=c*f x) (x : Space) (i : Fin 3) :
    dcoord f (halfTurn x) i= -(sign i : ℂ)*c*dcoord f x i := by
  have he : (fun y => f (halfTurn y))=(fun y => c*f y) := funext hc
  have hd := ((hf (halfTurn x)).hasFDerivAt.comp x halfTurn.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f (halfTurn y)) x=_ at hd
  rw [he,((hf x).hasFDerivAt.const_mul c).fderiv] at hd
  have hv := congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) hd
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,halfTurn_basis,
    map_smul,smul_eq_mul,Complex.real_smul,Complex.ofReal_neg] at hv
  change c*dcoord f x i= -(sign i : ℂ)*dcoord f (halfTurn x) i at hv
  have hs : (sign i : ℂ)^2=1 := by
    simp only [sign]
    split_ifs <;> norm_num
  calc
    dcoord f (halfTurn x) i=(sign i : ℂ)^2*dcoord f (halfTurn x) i := by rw [hs,one_mul]
    _= -(sign i : ℂ)*c*dcoord f x i := by linear_combination (sign i : ℂ)*hv

theorem curl_invariant (F : Field) (hf : ∀ j,Differentiable ℝ (fun x => F x j))
    (hF : Invariant F) : Invariant (curl F) := by
  intro x i
  have hp (a b : Fin 3) := partial_covariant (fun y => F y b) (hf b) (-(sign b : ℂ))
    (fun y => hF y b) x a
  fin_cases i <;> simp [curl,pd,hp,sign] <;> ring

theorem toroidal_invariant (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : ∀ x,f (halfTurn x)=f x) : Invariant (DebyeCalculus.toroidal f) := by
  apply curl_invariant
  · intro j x
    exact (DebyeCalculus.radialVector_smooth f x hf.contDiffAt j).differentiableAt (by simp)
  · intro x i
    have hi : halfTurn x i= -sign i*x i := by
      rw [halfTurn_apply]
      change -(sign i*x i)= -sign i*x i
      ring
    simp only [DebyeCalculus.radialVector,hs,hi,Complex.ofReal_mul,Complex.ofReal_neg]
    ring

theorem electric_invariant (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hs : ∀ x,f (halfTurn x)=f x) : Invariant (DebyeMaxwell.tmElectric f) := by
  apply curl_invariant
  · intro j x
    exact (DebyeCalculus.toroidal_smooth f x hf.contDiffAt j).differentiableAt (by simp)
  · exact toroidal_invariant f hf hs

theorem inversion_wall (F : Field) (hF : Invariant F) (x : Space) (i : Fin 3) :
    F (-x) i= -(sign i : ℂ)*F (reflect x) i := by
  have h := hF (reflect x) i
  simpa only [halfTurn_apply,reflect_reflect] using h

theorem even_wall_projection (F : Field) (hF : Invariant F) (x : Space) (i : Fin 3) :
    (F x i+F (-x) i)/2=(F x i-(sign i : ℂ)*F (reflect x) i)/2 := by
  rw [inversion_wall F hF]
  ring

theorem odd_wall_projection (F : Field) (hF : Invariant F) (x : Space) (i : Fin 3) :
    (F x i-F (-x) i)/2=(F x i+(sign i : ℂ)*F (reflect x) i)/2 := by
  rw [inversion_wall F hF]
  ring

theorem symmetric_te_invariant (a b c : ℝ) :
    Invariant (DebyeMaxwell.teElectric (SymmetricScalarWaves.scalar a b c)) :=
  toroidal_invariant _ (SymmetricScalarWaves.scalar_smooth a b c)
    (fun x => by simpa only [halfTurn_apply] using SymmetricScalarWaves.half_turn_even a b c x)

end OQ14.HalfTurnMaxwellParity

#print axioms OQ14.HalfTurnMaxwellParity.halfTurn_apply
#print axioms OQ14.HalfTurnMaxwellParity.halfTurn_basis
#print axioms OQ14.HalfTurnMaxwellParity.reflect_reflect
#print axioms OQ14.HalfTurnMaxwellParity.partial_covariant
#print axioms OQ14.HalfTurnMaxwellParity.curl_invariant
#print axioms OQ14.HalfTurnMaxwellParity.toroidal_invariant
#print axioms OQ14.HalfTurnMaxwellParity.electric_invariant
#print axioms OQ14.HalfTurnMaxwellParity.inversion_wall
#print axioms OQ14.HalfTurnMaxwellParity.even_wall_projection
#print axioms OQ14.HalfTurnMaxwellParity.odd_wall_projection
#print axioms OQ14.HalfTurnMaxwellParity.symmetric_te_invariant
