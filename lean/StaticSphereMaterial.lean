import StaticBallCentered
import ParityMaterialField

/-! # Exact static sphere response in the existing material-weighted space -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticSphereMaterial

open MeasureTheory Metric Set StaticBallNewton
open scoped Topology
attribute [local instance] Classical.propDecidable

def coefficient (c : Space) (R χ : ℝ) (hχ : 0 ≤ χ) : StaticCoefficient.Coefficient where
  value x := if VectorFourier.coordinateMap.symm x ∈ ball c R then χ else 0
  bound := χ
  measurable := Measurable.ite (measurableSet_ball.preimage VectorFourier.coordinateMap.symm.measurable)
    measurable_const measurable_const
  nonnegative x := by split_ifs <;> first | exact hχ | exact le_rfl
  bounded x := by split_ifs <;> first | exact le_rfl | exact hχ

theorem coefficient_value (c : Space) (R χ : ℝ) (hχ : 0 ≤ χ) (x : Space) :
    (coefficient c R χ hχ).value (VectorFourier.coordinateMap x) =
      if x ∈ ball c R then χ else 0 := by
  simp only [coefficient, MeasurableEquiv.symm_apply_apply]

theorem vector_ext_physical (F G : VectorL2)
    (h : ∀ i : Fin 3, (fun x => F (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => G (VectorFourier.coordinateMap x) i) : F = G := by
  apply VectorFourier.components.injective
  apply PiLp.ext
  intro i
  change VectorFourier.coordinate i F = VectorFourier.coordinate i G
  apply VectorFourier.scalarCoordinates.injective
  apply Lp.ext
  exact (NewtonL2.physicalCoordinate_ae F i).trans ((h i).trans
    (NewtonL2.physicalCoordinate_ae G i).symm)

theorem sqrt_source (c : Space) (R χ : ℝ) (hχ : 0 ≤ χ) (P : Vector) :
    StaticCoefficient.sqrtMultiplier (coefficient c R χ hχ) (StaticBallCentered.source c R P) =
      StaticBallCentered.source c R ((Real.sqrt χ : ℂ) • P) := by
  apply vector_ext_physical
  intro i
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae (coefficient c R χ hχ) (StaticBallCentered.source c R P))
  filter_upwards [hs, StaticBallCentered.source_ae c R P i,
    StaticBallCentered.source_ae c R ((Real.sqrt χ : ℂ) • P) i] with x hs hp hq
  rw [hs]
  change (Real.sqrt ((coefficient c R χ hχ).value (VectorFourier.coordinateMap x)) : ℂ) *
    StaticBallCentered.source c R P (VectorFourier.coordinateMap x) i = _
  rw [coefficient_value, hp, hq]
  by_cases hm : x ∈ ball c R <;> simp [hm]

def trialVector (χ : ℝ) (E : Vector) : Vector :=
  ((3*Real.sqrt χ/(χ+3) : ℝ) : ℂ) • E

def trial (c : Space) (R χ : ℝ) (E : Vector) : VectorL2 :=
  StaticBallCentered.source c R (trialVector χ E)

def forcing (c : Space) (R χ : ℝ) (E : Vector) : VectorL2 :=
  StaticBallCentered.source c R ((Real.sqrt χ : ℂ) • E)

theorem trial_physical_vector (χ : ℝ) (hχ : 0 ≤ χ) (E : Vector) :
    (Real.sqrt χ : ℂ) • trialVector χ E = StaticSpherePolarization.polarization χ E := by
  unfold trialVector StaticSpherePolarization.polarization
  rw [smul_smul]
  congr 1
  have he : Real.sqrt χ * (3*Real.sqrt χ/(χ+3)) = 3*χ/(χ+3) := by
    have hd : χ+3 ≠ 0 := by linarith
    field_simp [hd]
    nlinarith [Real.sq_sqrt hχ]
  exact_mod_cast he

theorem physical_source (c : Space) (R χ : ℝ) (hχ : 0 ≤ χ) (E : Vector) :
    StaticCoefficient.sqrtMultiplier (coefficient c R χ hχ) (trial c R χ E) =
      StaticBallCentered.source c R (StaticSpherePolarization.polarization χ E) := by
  rw [trial, sqrt_source c R χ hχ, trial_physical_vector χ hχ E]

theorem trial_scalar_identity (χ : ℝ) (hχ : 0 ≤ χ) (E : Vector) (i : Fin 3) :
    trialVector χ E i - (Real.sqrt χ : ℂ) *
      (-StaticSpherePolarization.polarization χ E i/3) = (Real.sqrt χ : ℂ)*E i := by
  have hd : ((χ : ℂ)+3) ≠ 0 := by
    have hh : χ+3 ≠ 0 := by linarith
    exact_mod_cast hh
  change ((3*Real.sqrt χ/(χ+3) : ℝ) : ℂ)*E i - (Real.sqrt χ : ℂ)*
    (-(((3*χ/(χ+3) : ℝ) : ℂ)*E i)/3) = _
  push_cast
  field_simp [hd]
  ring

theorem weightedBlock_trial (c : Space) (R : ℝ) (hR : 0 < R) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : Vector) :
    StaticCoefficient.weightedBlock (coefficient c R χ hχ) (trial c R χ E) = forcing c R χ E := by
  rw [← StaticNewton.volumeBlock_eq]
  apply vector_ext_physical
  intro i
  have hb := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticNewton.volumeBlock_ae (coefficient c R χ hχ) (trial c R χ E))
  filter_upwards [hb, StaticBallCentered.source_ae c R (trialVector χ E) i,
    StaticBallCentered.source_ae c R ((Real.sqrt χ : ℂ) • E) i,
    StaticBallCentered.newton_source_interior c R hR
      (StaticSpherePolarization.polarization χ E) i] with x hb hu hf hn
  rw [hb]
  change trial c R χ E (VectorFourier.coordinateMap x) i -
    (Real.sqrt ((coefficient c R χ hχ).value (VectorFourier.coordinateMap x)) : ℂ) *
      StaticNewton.response (coefficient c R χ hχ) (trial c R χ E)
        (VectorFourier.coordinateMap x) i = _
  have he : StaticNewton.response (coefficient c R χ hχ) (trial c R χ E) =
      NewtonL2.newtonOperator (StaticBallCentered.source c R
        (StaticSpherePolarization.polarization χ E)) := by
    change NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier _ _) = _
    rw [physical_source]
  rw [he, coefficient_value]
  change trial c R χ E (VectorFourier.coordinateMap x) i = _ at hu
  change forcing c R χ E (VectorFourier.coordinateMap x) i = _ at hf
  rw [hu, hf]
  by_cases hm : x ∈ ball c R
  · rw [if_pos hm, indicator_of_mem hm, indicator_of_mem hm, hn hm]
    exact trial_scalar_identity χ hχ E i
  · simp [hm]

theorem inverse_forcing (c : Space) (R : ℝ) (hR : 0 < R) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : Vector) :
    Ring.inverse (StaticCoefficient.weightedBlock (coefficient c R χ hχ)) (forcing c R χ E) =
      trial c R χ E := by
  rw [← weightedBlock_trial c R hR χ hχ E]
  have he := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (trial c R χ E))
    (Ring.inverse_mul_cancel _ (StaticCoefficient.weightedBlock_isUnit (coefficient c R χ hχ)))
  exact he

end OQ14.StaticSphereMaterial

#print axioms OQ14.StaticSphereMaterial.coefficient_value
#print axioms OQ14.StaticSphereMaterial.vector_ext_physical
#print axioms OQ14.StaticSphereMaterial.sqrt_source
#print axioms OQ14.StaticSphereMaterial.trial_physical_vector
#print axioms OQ14.StaticSphereMaterial.physical_source
#print axioms OQ14.StaticSphereMaterial.trial_scalar_identity
#print axioms OQ14.StaticSphereMaterial.weightedBlock_trial
#print axioms OQ14.StaticSphereMaterial.inverse_forcing
