import FullChannelFreeMap
import ConicalMaterialRunge

/-! Quantitative L² localization of arbitrary transverse Herglotz fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FullChannelBoundedDatum
open MeasureTheory Metric Maxwell FullChannelFreeMap ConicalRungeBall
open scoped Topology

def component (R : ℝ) (i : Fin 3) (F : transverse) : ScalarBall R :=
  (FullChannelHerglotz.electric_memLp (-1) R F.val F.property i).toLp
    (fun x => HerglotzAngularL2.value (-1) x i F.val)

theorem component_actual (R : ℝ) (i : Fin 3) (F : transverse) :
    (component R i F : Maxwell.Space → ℂ) =ᵐ[volume.restrict (closedBall 0 R)]
      fun x => HerglotzAngularL2.value (-1) x i F.val :=
  (FullChannelHerglotz.electric_memLp (-1) R F.val F.property i).coeFn_toLp

theorem component_add (R : ℝ) (i : Fin 3) (F G : transverse) :
    component R i (F+G) = component R i F + component R i G := by
  apply Lp.ext
  filter_upwards [component_actual R i (F+G), component_actual R i F, component_actual R i G,
    Lp.coeFn_add (component R i F) (component R i G)] with x h1 h2 h3 h4
  rw [h1, h4]
  simp only [Pi.add_apply, h2, h3]
  change HerglotzAngularL2.value (-1) x i (F.val + G.val) = _
  exact map_add _ _ _

theorem component_smul (R : ℝ) (i : Fin 3) (z : ℂ) (F : transverse) :
    component R i (z • F) = z • component R i F := by
  apply Lp.ext
  filter_upwards [component_actual R i (z • F), component_actual R i F,
    Lp.coeFn_smul z (component R i F)] with x h1 h2 h3
  rw [h1, h3]
  simp only [Pi.smul_apply, smul_eq_mul, h2]
  change HerglotzAngularL2.value (-1) x i (z • F.val) = _
  simp

/-- A pointwise uniform plane-wave bound gives a norm bound on each material-ball component. -/
theorem component_bound (R : ℝ) (i : Fin 3) (F : transverse) :
    ‖component R i F‖ ≤
      ((measureUnivNNReal (volume.restrict (closedBall (0 : Maxwell.Space) R)) : ℝ) ^
        ((2 : ENNReal).toReal⁻¹) * HerglotzAngularL2.bound) * ‖F‖ := by
  have h := Lp.norm_le_of_ae_bound (f := component R i F)
    (mul_nonneg HerglotzAngularL2.bound_nonnegative (norm_nonneg F))
    ((component_actual R i F).mono (fun x hx => by
      rw [hx]
      exact HerglotzAngularL2.value_norm_le (-1) x i F.val))
  exact h.trans_eq (by ring)

/-- The restriction to any material ball is a bounded linear map in each coordinate. -/
def componentCLM (R : ℝ) (i : Fin 3) : transverse →L[ℂ] ScalarBall R :=
  ({ toFun := component R i, map_add' := component_add R i, map_smul' := component_smul R i } :
    transverse →ₗ[ℂ] ScalarBall R).mkContinuous
      (((measureUnivNNReal (volume.restrict (closedBall (0 : Maxwell.Space) R)) : ℝ) ^
        ((2 : ENNReal).toReal⁻¹)) * HerglotzAngularL2.bound) (component_bound R i)

/-- The three electric components form one bounded vector-valued material-ball input. -/
def ballCLM (R : ℝ) : transverse →L[ℂ] BallL2 R :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ScalarBall R)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => componentCLM R i))

theorem ballCLM_actual (R : ℝ) (F : transverse) (i : Fin 3) :
    (ballCLM R F i : Maxwell.Space → ℂ) =ᵐ[volume.restrict (closedBall 0 R)]
      fun x => HerglotzAngularL2.value (-1) x i F.val := by
  exact component_actual R i F

/-- The actual power-normalized weighted material datum as a bounded operator. -/
def datumCLM (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c) :
    transverse →L[ℂ] VectorFourier.VectorL2 :=
  ((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I)) •
    (ConicalBallExtension.weighted c d.radius).comp (ballCLM d.radius)

/-- The bounded operator is exactly the previously constructed physical datum. -/
theorem datumCLM_eq (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : transverse) : datumCLM c d F = FullChannelTEMatch.normalizedDatum c d F.val F.property := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_smul ((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I))
      (ConicalBallExtension.weighted c d.radius (ballCLM d.radius F)))
  have hw := ConicalMaterialRunge.weighted_actual c d.radius (ballCLM d.radius F)
    (fun x i => HerglotzAngularL2.value (-1) x i F.val) d.ballZero (ballCLM_actual d.radius F) i
  filter_upwards [hs, hw, FullChannelTEMatch.normalized_datum_actual c d F.val F.property i] with x hs hw hd
  change (((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I)) •
      ConicalBallExtension.weighted c d.radius (ballCLM d.radius F)) (VectorFourier.coordinateMap x) i = _
  rw [hs]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hw, hd]
  dsimp [FullChannelTEMatch.normalizedElectric]
  ring

end OQ14.FullChannelBoundedDatum
#print axioms OQ14.FullChannelBoundedDatum.component_actual
#print axioms OQ14.FullChannelBoundedDatum.component_add
#print axioms OQ14.FullChannelBoundedDatum.component_smul
#print axioms OQ14.FullChannelBoundedDatum.component_bound

#print axioms OQ14.FullChannelBoundedDatum.ballCLM_actual
#print axioms OQ14.FullChannelBoundedDatum.datumCLM_eq
