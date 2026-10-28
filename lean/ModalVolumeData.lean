import ModalCoreAnalytic
import CompactFieldDatum
import ModalWeightedMode

/-! Actual compact weighted sphere data, entire in the complex frequency. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace OQ14.ModalVolumeData
open MeasureTheory Metric OQ14.Maxwell OQ14.ModalOrigin
open scoped Topology

abbrev Core := CompactFieldDatum.Core
abbrev ScalarContinuous := C(Core, ℂ)
abbrev VectorL2 := VectorFourier.VectorL2

def localized (v : Fin 3 → ScalarContinuous) : VectorL2 :=
  ∑ i : Fin 3, DynamicConvolution.insert i (CompactFieldDatum.scalarMap (v i))

theorem localized_coordinate (v : Fin 3 → ScalarContinuous) (i : Fin 3) :
    NewtonL2.physicalCoordinate (localized v) i = CompactFieldDatum.scalarMap (v i) := by
  change DynamicConvolution.component i (∑ j : Fin 3,
    DynamicConvolution.insert j (CompactFieldDatum.scalarMap (v j))) = _
  simp only [map_sum, DynamicConvolution.component_insert]
  simp

theorem localized_actual (v : Fin 3 → ScalarContinuous) (i : Fin 3) :
    (fun x : Space => localized v (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      CompactFieldDatum.extension (v i) := by
  have h := (NewtonL2.physicalCoordinate_ae (localized v) i).symm
  rw [localized_coordinate] at h
  exact h.trans (CompactFieldDatum.scalarMap_ae (v i))

def weighted (c : StaticCoefficient.Coefficient) (v : Fin 3 → ScalarContinuous) : VectorL2 :=
  StaticCoefficient.sqrtMultiplier c (localized v)

theorem weighted_actual (c : StaticCoefficient.Coefficient) (v : Fin 3 → ScalarContinuous)
    (E : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x) = 0)
    (hE : ∀ x : Core, ∀ i : Fin 3, v i x = E x.val i) (i : Fin 3) :
    (fun x : Space => weighted c v (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * E x i := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c (localized v))
  filter_upwards [hs, localized_actual v i] with x hx hv
  change (StaticCoefficient.sqrtMultiplier c (localized v)) (VectorFourier.coordinateMap x) i = _
  rw [hx]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [hv]
  by_cases h : x ∈ closedBall (0 : Space) 1
  · rw [CompactFieldDatum.extension_on (v i) x h, hE ⟨x,h⟩ i]
  · simp [hc x h]

theorem localized_analytic (v : ℂ → Fin 3 → ScalarContinuous) (k : ℂ)
    (hv : ∀ i, AnalyticAt ℂ (fun z => v z i) k) :
    AnalyticAt ℂ (fun z => localized (v z)) k := by
  have hi (i : Fin 3) : AnalyticAt ℂ (fun z =>
      DynamicConvolution.insert i (CompactFieldDatum.scalarMap (v z i))) k :=
    ((DynamicConvolution.insert i).analyticAt _).comp
      ((CompactFieldDatum.scalarMap.analyticAt _).comp (hv i))
  simpa only [localized, Fin.sum_univ_three] using ((hi 0).add (hi 1)).add (hi 2)

theorem weighted_analytic (c : StaticCoefficient.Coefficient)
    (v : ℂ → Fin 3 → ScalarContinuous) (k : ℂ)
    (hv : ∀ i, AnalyticAt ℂ (fun z => v z i) k) :
    AnalyticAt ℂ (fun z => weighted c (v z)) k :=
  ((StaticCoefficient.sqrtMultiplier c).analyticAt _).comp (localized_analytic v k hv)

def incident (n : ℝ) (hn : 1 < n) (k : ℂ) : VectorL2 :=
  weighted (ModalWeightedMode.coefficient n hn) (ModalCoreAnalytic.electric k)

def numerator (n : ℝ) (hn : 1 < n) (k : ℂ) : VectorL2 :=
  weighted (ModalWeightedMode.coefficient n hn) (ModalCoreAnalytic.numerator (n : ℂ) k)

theorem incident_analytic (n : ℝ) (hn : 1 < n) (k : ℂ) :
    AnalyticAt ℂ (incident n hn) k :=
  weighted_analytic _ ModalCoreAnalytic.electric k (fun i => ModalCoreAnalytic.electric_analytic i k)

theorem numerator_analytic (n : ℝ) (hn : 1 < n) (k : ℂ) :
    AnalyticAt ℂ (numerator n hn) k :=
  weighted_analytic _ (ModalCoreAnalytic.numerator (n : ℂ)) k
    (fun i => ModalCoreAnalytic.numerator_analytic (n : ℂ) i k)

theorem incident_actual (n : ℝ) (hn : 1 < n) (k : ℂ) (i : Fin 3) :
    (fun x : Space => incident n hn k (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt ((ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) *
        centerE k x i :=
  weighted_actual _ _ (centerE k) (ModalWeightedMode.coefficient_support n hn)
    (ModalCoreAnalytic.electric_actual k) i

theorem numerator_actual (n : ℝ) (hn : 1 < n) (k : ℂ) (i : Fin 3) :
    (fun x : Space => numerator n hn k (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt ((ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) *
        ((Complex.I/(n : ℂ))*centerE ((n : ℂ)*k) x i) :=
  weighted_actual _ _ (fun x i => (Complex.I/(n : ℂ))*centerE ((n : ℂ)*k) x i)
    (ModalWeightedMode.coefficient_support n hn) (ModalCoreAnalytic.numerator_actual (n : ℂ) k) i

theorem numerator_source (n : ℝ) (hn : 1 < n) (k : ℂ) (i : Fin 3) :
    DynamicVolume.source (ModalWeightedMode.coefficient n hn) (numerator n hn k) i =ᵐ[volume]
      fun x => (((ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) *
        ((Complex.I/(n : ℂ))*centerE ((n : ℂ)*k) x i) :=
  MaterialVolumeConverse.source_from_weighted _ _ _ (numerator_actual n hn k) i

theorem numerator_ne_zero (n : ℝ) (hn : 1 < n) (k : ℂ) (hk : k ≠ 0) :
    numerator n hn k ≠ 0 := by
  intro hzero
  have he := ae_restrict_of_ae (numerator_actual n hn k 2)
    (s := ball (0 : Space) 1)
  have hz := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_zero VectorFourier.Vector 2 (volume : Measure VectorFourier.Frequency))
  have haez : (fun x : Space => (Real.sqrt (n^2-1) : ℂ) *
      ((Complex.I/(n : ℂ))*centerE ((n : ℂ)*k) x 2))
      =ᵐ[volume.restrict (ball (0 : Space) 1)] fun _ => (0 : ℂ) := by
    filter_upwards [he, ae_restrict_of_ae hz, ae_restrict_mem measurableSet_ball] with x hx hz hxball
    have hnorm : ‖x‖ < 1 := by simpa using hxball
    rw [hzero, hz] at hx
    rw [ModalWeightedMode.coefficient_value, if_pos hnorm] at hx
    simpa only [PiLp.zero_apply] using hx.symm
  have hc : Continuous (fun x : Space => (Real.sqrt (n^2-1) : ℂ) *
      ((Complex.I/(n : ℂ))*centerE ((n : ℂ)*k) x 2)) :=
    continuous_const.mul (continuous_const.mul (centerE_continuous ((n : ℂ)*k) 2))
  have heq := Measure.eqOn_open_of_ae_eq haez isOpen_ball hc.continuousOn
    continuous_const.continuousOn
  have hcenter := heq (show (0 : Space) ∈ ball (0 : Space) 1 by simp)
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hs : (Real.sqrt (n^2-1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (ModalWeightedMode.contrast_pos n hn)).ne'
  have hv : (Real.sqrt (n^2-1) : ℂ) *
      ((Complex.I/(n : ℂ))*(2*((n : ℂ)*k)^2/3)) ≠ 0 :=
    mul_ne_zero hs (mul_ne_zero (div_ne_zero Complex.I_ne_zero hn0)
      (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero hn0 hk)))
        (by norm_num)))
  exact hv (by simpa [centerE_zero] using hcenter)

end OQ14.ModalVolumeData

#print axioms OQ14.ModalVolumeData.localized_coordinate
#print axioms OQ14.ModalVolumeData.localized_actual
#print axioms OQ14.ModalVolumeData.weighted_actual
#print axioms OQ14.ModalVolumeData.localized_analytic
#print axioms OQ14.ModalVolumeData.weighted_analytic
#print axioms OQ14.ModalVolumeData.incident_analytic
#print axioms OQ14.ModalVolumeData.numerator_analytic
#print axioms OQ14.ModalVolumeData.incident_actual
#print axioms OQ14.ModalVolumeData.numerator_actual
#print axioms OQ14.ModalVolumeData.numerator_source
#print axioms OQ14.ModalVolumeData.numerator_ne_zero
