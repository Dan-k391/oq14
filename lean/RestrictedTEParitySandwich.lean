import ShellInclusionVolume
import ParityMaterialField
import RestrictedTEDatumLinear

/-! The parity material block is a shell block: `block d k B = 1 - S c * T_B * S c` with `T_B` a bounded operator
that depends on the coefficient only through the radius of its support ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEParitySandwich
open MeasureTheory Metric
abbrev Space := FourierL2.Space
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Operator := VectorL2 →L[ℂ] VectorL2
attribute [local instance] Classical.propDecidable

/-- The indicator coefficient of the closed ball of radius `R` (value one inside, zero outside). -/
def ballCoefficient (R : ℝ) : Coefficient where
  value z := if VectorFourier.coordinateMap.symm z ∈ closedBall (0 : Space) R then 1 else 0
  bound := 1
  measurable := Measurable.ite (isClosed_closedBall.measurableSet.preimage
    VectorFourier.coordinateMap.symm.measurable) measurable_const measurable_const
  nonnegative z := by split_ifs <;> norm_num
  bounded z := by split_ifs <;> norm_num

theorem ballCoefficient_value (R : ℝ) (x : Space) :
    (ballCoefficient R).value (VectorFourier.coordinateMap x)=if x∈closedBall (0 : Space) R then 1 else 0 := by
  simp only [ballCoefficient,MeasurableEquiv.symm_apply_apply]

/-- Support data of the ball coefficient: the closed ball itself. -/
def ballSupport (R : ℝ) : BoundedMaterialKernel.SupportData (ballCoefficient R) where
  radius := R
  carrier := closedBall 0 R
  measurable := measurableSet_closedBall
  finite := (isCompact_closedBall (0 : Space) R).measure_lt_top.ne
  ballZero x hx := by rw [ballCoefficient_value]; simp [hx]
  carrierZero x hx := by rw [ballCoefficient_value]; simp [hx]

/-- The compression to the ball of radius `R` of the reaction kernel `SphereReactionKernel.reaction e k`: the
literal kernel integral operator `S 1_B * K * S 1_B` of the ball indicator `1_B`. It depends only on `R`, `e`, `k`. -/
def reactionBall (R : ℝ) (e : Bool) (k : ℝ) : Operator :=
  BoundedMaterialKernel.operator (ballSupport R) (ParityReactionVolume.entries e k)

/-- The explicit bounded operator `T_B` of the parity block. -/
def parityKernel (R k B : ℝ) : Operator :=
  ShellInclusionVolume.kernel k R+((B^2-1 : ℝ) : ℂ) • reactionBall R true k+
    ((B⁻¹^2-1 : ℝ) : ℂ) • reactionBall R false k

theorem comp_ae (F : VectorL2) (i : Fin 3) :
    ∀ᵐ x : Space, DynamicConvolution.component i F x=F (VectorFourier.coordinateMap x) i :=
  NewtonL2.physicalCoordinate_ae F i

theorem sqrt_apply_ae (c : Coefficient) (F : VectorL2) (i : Fin 3) :
    ∀ᵐ x : Space, StaticCoefficient.sqrtMultiplier c F (VectorFourier.coordinateMap x) i=
      (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*F (VectorFourier.coordinateMap x) i := by
  have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c F)
  filter_upwards [h] with x hx
  rw [hx]
  rfl

theorem sqrt_mul_ball (c : Coefficient) (R : ℝ)
    (hc : ∀ x : Space, x∉closedBall (0 : Space) R → c.value (VectorFourier.coordinateMap x)=0) (x : Space) :
    (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*
      (Real.sqrt ((ballCoefficient R).value (VectorFourier.coordinateMap x)) : ℂ)=
      (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) := by
  by_cases hx : x∈closedBall (0 : Space) R
  · rw [ballCoefficient_value]
    simp [hx]
  · rw [hc x hx]
    simp

/-- The reaction operator of the parity block is the sandwich of the ball-compressed kernel operator. -/
theorem operator_sandwich {c : Coefficient} (d : BoundedMaterialKernel.SupportData c) (e : Bool) (k : ℝ) :
    ParityReactionVolume.operator d e k=
      StaticCoefficient.sqrtMultiplier c*reactionBall d.radius e k*StaticCoefficient.sqrtMultiplier c := by
  apply ContinuousLinearMap.ext
  intro u
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  let w : VectorL2 := StaticCoefficient.sqrtMultiplier c u
  let K := reactionBall d.radius e k
  have hcj (j : Fin 3) : DynamicConvolution.component j
      (StaticCoefficient.sqrtMultiplier (ballCoefficient d.radius) w)=ᵐ[volume]
      DynamicConvolution.component j w := by
    filter_upwards [comp_ae (StaticCoefficient.sqrtMultiplier (ballCoefficient d.radius) w) j,
      sqrt_apply_ae (ballCoefficient d.radius) w j,comp_ae w j,
      sqrt_apply_ae c u j] with y h1 h2 h3 h4
    rw [h1,h2,← h3]
    by_cases hy : y∈closedBall (0 : Space) d.radius
    · rw [ballCoefficient_value]
      simp [hy]
    · have hz : c.value (VectorFourier.coordinateMap y)=0 := d.ballZero y hy
      have hw : w (VectorFourier.coordinateMap y) j=0 := by
        change StaticCoefficient.sqrtMultiplier c u (VectorFourier.coordinateMap y) j=0
        rw [h4,hz]
        simp
      have hw' : DynamicConvolution.component j w y=0 := h3.trans hw
      rw [hw']
      simp
  have hL := BoundedMaterialKernel.component_operator_ae d (ParityReactionVolume.entries e k) u i
  have hR := BoundedMaterialKernel.component_operator_ae (ballSupport d.radius)
    (ParityReactionVolume.entries e k) w i
  have hint (x : Space) (j : Fin 3) :
      (∫ y, (ParityReactionVolume.entries e k i j).value x y*DynamicConvolution.component j
        (StaticCoefficient.sqrtMultiplier (ballCoefficient d.radius) w) y)=
      ∫ y, (ParityReactionVolume.entries e k i j).value x y*DynamicConvolution.component j w y := by
    apply integral_congr_ae
    filter_upwards [hcj j] with y hy
    rw [hy]
  filter_upwards [sqrt_apply_ae c (K w) i,comp_ae (K w) i,comp_ae (ParityReactionVolume.operator d e k u) i,
    hL,hR] with x h1 h2 h3 hl hr
  change (ParityReactionVolume.operator d e k u) (VectorFourier.coordinateMap x) i=
    StaticCoefficient.sqrtMultiplier c (K w) (VectorFourier.coordinateMap x) i
  rw [← h3]
  change DynamicConvolution.component i (BoundedMaterialKernel.operator d
    (ParityReactionVolume.entries e k) u) x=_
  rw [hl,h1,← h2]
  change _=(Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*
    DynamicConvolution.component i (BoundedMaterialKernel.operator (ballSupport d.radius)
      (ParityReactionVolume.entries e k) w) x
  rw [hr]
  simp only [hint]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← mul_assoc,sqrt_mul_ball c d.radius d.ballZero x]

/-- The parity block is the sandwich `1 - S c * T_B * S c` with the explicit bounded operator `T_B`. -/
theorem block_sandwich {c : Coefficient} (d : BoundedMaterialKernel.SupportData c) (k B : ℝ) :
    ParityMaterialField.block d k B=
      1-StaticCoefficient.sqrtMultiplier c*parityKernel d.radius k B*StaticCoefficient.sqrtMultiplier c := by
  rw [ParityMaterialField.block_eq,ShellInclusionVolume.volumeBlock_eq_sandwich,
    operator_sandwich d true k,operator_sandwich d false k]
  unfold parityKernel
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
  abel

/-- The parity block is an instance of the shell block of root's shell-plus-inclusion algebra. -/
theorem block_eq_shell {c : Coefficient} (d : BoundedMaterialKernel.SupportData c) (k B : ℝ) :
    ParityMaterialField.block d k B=
      ShellInclusionBlocks.shell (StaticCoefficient.sqrtMultiplier c) (parityKernel d.radius k B) :=
  block_sandwich d k B

/-- Support data of a sum of coefficients with a common enclosing radius. -/
def addSupport {cs ci : Coefficient} (ds : BoundedMaterialKernel.SupportData cs)
    (di : BoundedMaterialKernel.SupportData ci) (hr : di.radius=ds.radius) :
    BoundedMaterialKernel.SupportData (ShellInclusionVolume.add cs ci) where
  radius := ds.radius
  carrier := ds.carrier ∪ di.carrier
  measurable := ds.measurable.union di.measurable
  finite := (measure_union_le _ _).trans_lt
    (ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr ds.finite,lt_top_iff_ne_top.mpr di.finite⟩) |>.ne
  ballZero x hx := by
    simp only [ShellInclusionVolume.add,ds.ballZero x hx,di.ballZero x (hr ▸ hx),add_zero]
  carrierZero x hx := by
    have h1 : x∉ds.carrier := fun h => hx (Or.inl h)
    have h2 : x∉di.carrier := fun h => hx (Or.inr h)
    simp only [ShellInclusionVolume.add,ds.carrierZero x h1,di.carrierZero x h2,add_zero]

/-- The parity block of a shell plus a disjoint inclusion (common enclosing radius) is the combined block of
root's shell-plus-inclusion algebra with the same bounded operator `T_B`. -/
theorem block_add_eq_combined {cs ci : Coefficient} (ds : BoundedMaterialKernel.SupportData cs)
    (di : BoundedMaterialKernel.SupportData ci) (hr : di.radius=ds.radius)
    (h : ShellInclusionVolume.Disjoint cs ci) (k B : ℝ) :
    ParityMaterialField.block (addSupport ds di hr) k B=
      ShellInclusionBlocks.combined (StaticCoefficient.sqrtMultiplier cs)
        (StaticCoefficient.sqrtMultiplier ci) (parityKernel ds.radius k B) := by
  rw [block_sandwich,ShellInclusionVolume.sqrtMultiplier_add cs ci h]
  rfl

end OQ14.RestrictedTEParitySandwich
#print axioms OQ14.RestrictedTEParitySandwich.ballCoefficient_value
#print axioms OQ14.RestrictedTEParitySandwich.comp_ae
#print axioms OQ14.RestrictedTEParitySandwich.sqrt_apply_ae
#print axioms OQ14.RestrictedTEParitySandwich.sqrt_mul_ball
#print axioms OQ14.RestrictedTEParitySandwich.operator_sandwich
#print axioms OQ14.RestrictedTEParitySandwich.block_sandwich
#print axioms OQ14.RestrictedTEParitySandwich.block_eq_shell
#print axioms OQ14.RestrictedTEParitySandwich.block_add_eq_combined
