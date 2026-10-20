import DynamicVolume
import LocalVolumeResponse

/-! # Actual dielectric material self-consistency

The volume unknown is the square-root-weighted electric field. Multiplying its
actual spatial equation by the same square root gives rho = chi E without
dividing by chi. An incident field needs only an actual L2 weighted datum, not
global L2 integrability.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.MaterialField

open MeasureTheory Metric OQ14.Maxwell

abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

def scattered (c : Coefficient) (k : ℝ) (u : VectorL2) : Field :=
  FieldResponse.electric k (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u)

def total (c : Coefficient) (k : ℝ) (u : VectorL2) (incident : Field) : Field :=
  fun x i => incident x i + scattered c k u x i

theorem source_compact (c : Coefficient) (u : VectorL2) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) : HasCompactSupport (DynamicVolume.source c u i) := by
  apply HasCompactSupport.intro' (isCompact_closedBall 0 R) isClosed_closedBall
  intro x hx
  exact DynamicVolume.source_zero c u R hc i x hx

theorem scattered_actual (c : Coefficient) (k : ℝ) (u : VectorL2) (i : Fin 3) :
    (fun x => scattered c k u x i) =ᵐ[volume] fun x =>
      StaticNewton.response c u (VectorFourier.coordinateMap x) i +
        ∑ j, ∫ y, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c u j y := by
  filter_upwards [NewtonL2.physicalCoordinate_ae
    (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u)) i] with x hx
  unfold scattered FieldResponse.electric
  rw [hx]
  change StaticNewton.response c u (VectorFourier.coordinateMap x) i + _ = _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold KernelConvolution.response
  apply integral_congr_ae
  filter_upwards with y
  ring

theorem scattered_memLp_ball (c : Coefficient) (k R T : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    MemLp (fun x => scattered c k u x i) 2 (volume.restrict (closedBall 0 T)) :=
  LocalVolumeResponse.electric_memLp_ball k T R (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u R hc)
    (DynamicVolume.source_zero c u R hc) (StaticNewton.material_source_ae c u) i

theorem scattered_locallyIntegrable (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) : LocallyIntegrable (fun x => scattered c k u x i) :=
  LocalVolumeResponse.electric_locallyIntegrable k R (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u R hc)
    (DynamicVolume.source_zero c u R hc) (StaticNewton.material_source_ae c u) i

/-- The actual material polarization equals chi times the total electric field.
No division by a possibly vanishing material coefficient is used. -/
theorem material_relation (c : Coefficient) (k R : ℝ) (u f : VectorL2)
    (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * incident x i)
    (hsol : DynamicVolume.volumeBlock c k R u = f) (i : Fin 3) :
    DynamicVolume.source c u i =ᵐ[volume] fun x =>
      (c.value (VectorFourier.coordinateMap x) : ℂ) * total c k u incident x i := by
  filter_upwards [DynamicVolume.volumeBlock_actual c u k R hc i,
    hincident i, scattered_actual c k u i] with x hx hi hs
  rw [hsol, hi] at hx
  rw [← hs] at hx
  have hp : (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)^2 =
      (c.value (VectorFourier.coordinateMap x) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (c.nonnegative (VectorFourier.coordinateMap x))
  unfold DynamicVolume.source total
  rw [← hp]
  linear_combination -(Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * hx

def solution (c : Coefficient) (k R : ℝ) (f : VectorL2) : VectorL2 :=
  Ring.inverse (DynamicVolume.volumeBlock c k R) f

theorem solution_equation (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hsmall : DynamicVolume.errorBound c k R < 1) (f : VectorL2) :
    DynamicVolume.volumeBlock c k R (solution c k R f) = f := by
  have hunit := DynamicVolume.volumeBlock_isUnit c k R hR hsmall
  exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L f)
    (Ring.mul_inverse_cancel (DynamicVolume.volumeBlock c k R) hunit)

theorem solution_material_relation (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hsmall : DynamicVolume.errorBound c k R < 1) (f : VectorL2) (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * incident x i)
    (i : Fin 3) :
    DynamicVolume.source c (solution c k R f) i =ᵐ[volume] fun x =>
      (c.value (VectorFourier.coordinateMap x) : ℂ) *
        total c k (solution c k R f) incident x i :=
  material_relation c k R _ f incident hc hincident (solution_equation c k R hR hsmall f) i

end OQ14.MaterialField

#print axioms OQ14.MaterialField.source_compact
#print axioms OQ14.MaterialField.scattered_actual
#print axioms OQ14.MaterialField.scattered_memLp_ball
#print axioms OQ14.MaterialField.scattered_locallyIntegrable
#print axioms OQ14.MaterialField.material_relation
#print axioms OQ14.MaterialField.solution_equation
#print axioms OQ14.MaterialField.solution_material_relation
