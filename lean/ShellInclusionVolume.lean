import ShellInclusionBlocks
import MaterialField

/-! The actual dynamic volume block of a shell-plus-inclusion susceptibility with disjoint supports
reduces exactly to the shell block and the effective inclusion block. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
namespace OQ14.ShellInclusionVolume
open MeasureTheory
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Operator := VectorL2 →L[ℂ] VectorL2

/-- Sum of two actual coefficients. -/
def add (c₁ c₂ : Coefficient) : Coefficient where
  value x := c₁.value x+c₂.value x
  bound := c₁.bound+c₂.bound
  measurable := c₁.measurable.add c₂.measurable
  nonnegative x := add_nonneg (c₁.nonnegative x) (c₂.nonnegative x)
  bounded x := add_le_add (c₁.bounded x) (c₂.bounded x)

/-- Pointwise disjoint supports. -/
def Disjoint (c₁ c₂ : Coefficient) : Prop := ∀ x, c₁.value x=0 ∨ c₂.value x=0

theorem Disjoint.symm {c₁ c₂ : Coefficient} (h : Disjoint c₁ c₂) : Disjoint c₂ c₁ :=
  fun x => (h x).symm

theorem sqrt_add_of_disjoint (a b : ℝ) (h : a=0 ∨ b=0) : Real.sqrt (a+b)=Real.sqrt a+Real.sqrt b := by
  rcases h with h | h <;> simp [h]

theorem sqrtMultiplier_add (c₁ c₂ : Coefficient) (h : Disjoint c₁ c₂) :
    StaticCoefficient.sqrtMultiplier (add c₁ c₂)=
      StaticCoefficient.sqrtMultiplier c₁+StaticCoefficient.sqrtMultiplier c₂ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [StaticCoefficient.sqrtMultiplier_ae (add c₁ c₂) f,StaticCoefficient.sqrtMultiplier_ae c₁ f,
    StaticCoefficient.sqrtMultiplier_ae c₂ f,
    Lp.coeFn_add (StaticCoefficient.sqrtMultiplier c₁ f) (StaticCoefficient.sqrtMultiplier c₂ f)] with x h0 h1 h2 h3
  rw [ContinuousLinearMap.add_apply,h3,Pi.add_apply,h0,h1,h2]
  change (Real.sqrt (c₁.value x+c₂.value x) : ℂ) • f x=_
  rw [sqrt_add_of_disjoint _ _ (h x)]
  push_cast
  rw [add_smul]

theorem sqrtMultiplier_mul_zero (c₁ c₂ : Coefficient) (h : Disjoint c₁ c₂) :
    StaticCoefficient.sqrtMultiplier c₁*StaticCoefficient.sqrtMultiplier c₂=0 := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.mul_apply,ContinuousLinearMap.zero_apply]
  apply Lp.ext
  filter_upwards [StaticCoefficient.sqrtMultiplier_ae c₁ (StaticCoefficient.sqrtMultiplier c₂ f),
    StaticCoefficient.sqrtMultiplier_ae c₂ f,Lp.coeFn_zero VectorFourier.Vector 2 volume] with x h1 h2 h0
  rw [h1,h2,h0,Pi.zero_apply]
  rcases h x with hx | hx <;> simp [hx]

/-- The coefficient-independent dynamic-minus-static kernel operator at frequency k and enclosing radius R. -/
def kernel (k R : ℝ) : Operator :=
  DynamicConvolution.operator k (2*R)-VectorFourier.physicalProjection

theorem volumeBlock_eq_sandwich (c : Coefficient) (k R : ℝ) :
    DynamicVolume.volumeBlock c k R=
      1-StaticCoefficient.sqrtMultiplier c*kernel k R*StaticCoefficient.sqrtMultiplier c := by
  rw [DynamicVolume.volumeBlock,StaticNewton.volumeBlock_eq,StaticCoefficient.weightedBlock,
    DynamicVolume.weightedRemainder,kernel]
  simp only [← ContinuousLinearMap.mul_def]
  noncomm_ring

section Reduction
variable (cs ci : Coefficient) (k R : ℝ)

theorem shell_eq : DynamicVolume.volumeBlock cs k R=
    ShellInclusionBlocks.shell (StaticCoefficient.sqrtMultiplier cs) (kernel k R) :=
  volumeBlock_eq_sandwich cs k R

theorem green_left (hs : IsUnit (DynamicVolume.volumeBlock cs k R)) :
    (1-kernel k R*(StaticCoefficient.sqrtMultiplier cs*StaticCoefficient.sqrtMultiplier cs))*
      ShellInclusionAlgebra.green (StaticCoefficient.sqrtMultiplier cs) (kernel k R)=kernel k R :=
  ShellInclusionAlgebra.green_left_unit _ _ (by rwa [shell_eq] at hs)

theorem green_right (hs : IsUnit (DynamicVolume.volumeBlock cs k R)) :
    ShellInclusionAlgebra.green (StaticCoefficient.sqrtMultiplier cs) (kernel k R)*
      (1-(StaticCoefficient.sqrtMultiplier cs*StaticCoefficient.sqrtMultiplier cs)*kernel k R)=kernel k R :=
  ShellInclusionAlgebra.green_right_unit _ _ (by rwa [shell_eq] at hs)

variable (h : Disjoint cs ci)
include h

theorem combined_eq :
    DynamicVolume.volumeBlock (add cs ci) k R=
      ShellInclusionBlocks.combined (StaticCoefficient.sqrtMultiplier cs)
        (StaticCoefficient.sqrtMultiplier ci) (kernel k R) := by
  rw [volumeBlock_eq_sandwich,sqrtMultiplier_add cs ci h]
  rfl

/-- Whenever u solves the combined volume equation with datum f, the inclusion quantity
`Si T (Ss+Si) u` solves the effective inclusion equation with datum `Si G (Ss+Si) f`. -/
theorem effective_of_solution (hs : IsUnit (DynamicVolume.volumeBlock cs k R)) (u f : VectorL2)
    (hu : DynamicVolume.volumeBlock (add cs ci) k R u=f) :
    ShellInclusionBlocks.effective (StaticCoefficient.sqrtMultiplier cs)
        (StaticCoefficient.sqrtMultiplier ci) (kernel k R)
      (StaticCoefficient.sqrtMultiplier ci (kernel k R
        ((StaticCoefficient.sqrtMultiplier cs+StaticCoefficient.sqrtMultiplier ci) u)))=
      StaticCoefficient.sqrtMultiplier ci
        (ShellInclusionAlgebra.green (StaticCoefficient.sqrtMultiplier cs) (kernel k R)
          ((StaticCoefficient.sqrtMultiplier cs+StaticCoefficient.sqrtMultiplier ci) f)) := by
  have hid := ShellInclusionBlocks.effective_mul (StaticCoefficient.sqrtMultiplier cs)
    (StaticCoefficient.sqrtMultiplier ci) (kernel k R) (by rwa [shell_eq] at hs)
    (sqrtMultiplier_mul_zero cs ci h) (sqrtMultiplier_mul_zero ci cs h.symm)
  have happ := congrArg (fun L : Operator => L u) hid
  simp only [ContinuousLinearMap.mul_apply] at happ
  rw [combined_eq cs ci k R h] at hu
  rw [hu] at happ
  exact happ

theorem combined_isUnit (hs : IsUnit (DynamicVolume.volumeBlock cs k R))
    (hE : IsUnit (ShellInclusionBlocks.effective (StaticCoefficient.sqrtMultiplier cs)
      (StaticCoefficient.sqrtMultiplier ci) (kernel k R))) :
    IsUnit (DynamicVolume.volumeBlock (add cs ci) k R) := by
  rw [combined_eq cs ci k R h]
  exact ShellInclusionBlocks.combined_isUnit _ _ _ (by rwa [shell_eq] at hs)
    (sqrtMultiplier_mul_zero cs ci h) (sqrtMultiplier_mul_zero ci cs h.symm) hE

theorem combined_inverse (hs : IsUnit (DynamicVolume.volumeBlock cs k R))
    (hE : IsUnit (ShellInclusionBlocks.effective (StaticCoefficient.sqrtMultiplier cs)
      (StaticCoefficient.sqrtMultiplier ci) (kernel k R))) :
    Ring.inverse (DynamicVolume.volumeBlock (add cs ci) k R)=
      ShellInclusionBlocks.combinedInverse (StaticCoefficient.sqrtMultiplier cs)
        (StaticCoefficient.sqrtMultiplier ci) (kernel k R) := by
  rw [combined_eq cs ci k R h]
  exact ShellInclusionBlocks.combined_inverse _ _ _ (by rwa [shell_eq] at hs)
    (sqrtMultiplier_mul_zero cs ci h) (sqrtMultiplier_mul_zero ci cs h.symm) hE

/-- The actual material solution of the combined susceptibility is the explicit inverse formula
applied to the datum. -/
theorem solution_eq (hs : IsUnit (DynamicVolume.volumeBlock cs k R))
    (hE : IsUnit (ShellInclusionBlocks.effective (StaticCoefficient.sqrtMultiplier cs)
      (StaticCoefficient.sqrtMultiplier ci) (kernel k R))) (f : VectorL2) :
    MaterialField.solution (add cs ci) k R f=
      ShellInclusionBlocks.combinedInverse (StaticCoefficient.sqrtMultiplier cs)
        (StaticCoefficient.sqrtMultiplier ci) (kernel k R) f := by
  unfold MaterialField.solution
  rw [combined_inverse cs ci k R h hs hE]

end Reduction
end OQ14.ShellInclusionVolume
#print axioms OQ14.ShellInclusionVolume.sqrt_add_of_disjoint
#print axioms OQ14.ShellInclusionVolume.sqrtMultiplier_add
#print axioms OQ14.ShellInclusionVolume.sqrtMultiplier_mul_zero
#print axioms OQ14.ShellInclusionVolume.volumeBlock_eq_sandwich
#print axioms OQ14.ShellInclusionVolume.shell_eq
#print axioms OQ14.ShellInclusionVolume.green_left
#print axioms OQ14.ShellInclusionVolume.green_right
#print axioms OQ14.ShellInclusionVolume.combined_eq
#print axioms OQ14.ShellInclusionVolume.effective_of_solution
#print axioms OQ14.ShellInclusionVolume.combined_isUnit
#print axioms OQ14.ShellInclusionVolume.combined_inverse
#print axioms OQ14.ShellInclusionVolume.solution_eq
