import MaterialField

/-! # Actual L2 incident datum from local incident regularity

The incoming field itself need not belong to global L2. Only its components
on the compact material ball are used to construct the weighted volume datum.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.IncidentLocalization

open MeasureTheory Metric OQ14.Maxwell

abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

def weighted (c : Coefficient) (incident : Field) (i : Fin 3) (x : Space) : ℂ :=
  (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * incident x i

theorem weighted_memLp (c : Coefficient) (R : ℝ) (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, MemLp (fun x => incident x i) 2
      (volume.restrict (closedBall 0 R))) (i : Fin 3) :
    MemLp (weighted c incident i) 2 volume := by
  let g : Space → ℂ := (closedBall 0 R).indicator (fun x => incident x i)
  have hg : MemLp g 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (hincident i)
  have hm : Measurable (fun x : Space =>
      (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (Real.continuous_sqrt.measurable.comp
        (c.measurable.comp VectorFourier.coordinateMap_preserving.measurable))
  have hp : MemLp (fun x : Space =>
      (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * g x) 2 volume := by
    apply hg.of_le_mul (hm.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    filter_upwards with x
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (StaticCoefficient.sqrt_value_bound c (VectorFourier.coordinateMap x)) (norm_nonneg _)
  apply hp.ae_eq
  filter_upwards with x
  by_cases hx : x ∈ closedBall (0 : Space) R
  · simp [g, weighted, hx]
  · simp [g, weighted, hx, hc x hx]

def scalarDatum (c : Coefficient) (R : ℝ) (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, MemLp (fun x => incident x i) 2
      (volume.restrict (closedBall 0 R))) (i : Fin 3) : FourierL2.ScalarL2 :=
  (weighted_memLp c R incident hc hincident i).toLp (weighted c incident i)

theorem scalarDatum_ae (c : Coefficient) (R : ℝ) (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, MemLp (fun x => incident x i) 2
      (volume.restrict (closedBall 0 R))) (i : Fin 3) :
    (scalarDatum c R incident hc hincident i : Space → ℂ) =ᵐ[volume]
      weighted c incident i :=
  (weighted_memLp c R incident hc hincident i).coeFn_toLp

def datum (c : Coefficient) (R : ℝ) (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, MemLp (fun x => incident x i) 2
      (volume.restrict (closedBall 0 R))) : VectorL2 :=
  ∑ i : Fin 3, DynamicConvolution.insert i (scalarDatum c R incident hc hincident i)

theorem coordinate_datum (c : Coefficient) (R : ℝ) (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, MemLp (fun x => incident x i) 2
      (volume.restrict (closedBall 0 R))) (i : Fin 3) :
    NewtonL2.physicalCoordinate (datum c R incident hc hincident) i =
      scalarDatum c R incident hc hincident i := by
  change DynamicConvolution.component i
    (∑ j : Fin 3, DynamicConvolution.insert j (scalarDatum c R incident hc hincident j)) = _
  simp only [map_sum, DynamicConvolution.component_insert]
  simp

theorem datum_actual (c : Coefficient) (R : ℝ) (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, MemLp (fun x => incident x i) 2
      (volume.restrict (closedBall 0 R))) (i : Fin 3) :
    (fun x => datum c R incident hc hincident (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      weighted c incident i := by
  have h := (NewtonL2.physicalCoordinate_ae (datum c R incident hc hincident) i).symm
  rw [coordinate_datum] at h
  exact h.trans (scalarDatum_ae c R incident hc hincident i)

theorem actual_solution_material_relation (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hsmall : DynamicVolume.errorBound c k R < 1) (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, MemLp (fun x => incident x i) 2
      (volume.restrict (closedBall 0 R))) (i : Fin 3) :
    DynamicVolume.source c (MaterialField.solution c k R (datum c R incident hc hincident)) i
      =ᵐ[volume] fun x => (c.value (VectorFourier.coordinateMap x) : ℂ) *
        MaterialField.total c k (MaterialField.solution c k R (datum c R incident hc hincident))
          incident x i :=
  MaterialField.solution_material_relation c k R hR hsmall _ incident hc
    (datum_actual c R incident hc hincident) i

end OQ14.IncidentLocalization

#print axioms OQ14.IncidentLocalization.weighted_memLp
#print axioms OQ14.IncidentLocalization.scalarDatum_ae
#print axioms OQ14.IncidentLocalization.coordinate_datum
#print axioms OQ14.IncidentLocalization.datum_actual
#print axioms OQ14.IncidentLocalization.actual_solution_material_relation
