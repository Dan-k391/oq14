import ModalDrivenSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ModalDrivenRepresentation
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ModalDriven
  OQ14.ModalDrivenScattering OQ14.ModalWeightedMode OQ14.ModalVolumeData
open scoped Topology

theorem response (n : ℝ) (hn : 1 < n) (k : ℝ) (hk : 0 < k) :
    scatteredE (n : ℂ) k =ᵐ[volume]
      MaterialField.scattered (ModalWeightedMode.coefficient n hn) k (ModalVolumeData.numerator n hn k) := by
  let c := ModalWeightedMode.coefficient n hn
  let u := ModalVolumeData.numerator n hn k
  let ρ := DynamicVolume.source c u
  have hs : ∀ j y, y ∉ closedBall (0 : Space) 1 → ρ j y = 0 :=
    DynamicVolume.source_zero c u 1 (ModalWeightedMode.coefficient_support n hn)
  have hF (j : Fin 3) : (NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c u) j : Space → ℂ) =ᵐ[volume] ρ j :=
    StaticNewton.material_source_ae c u j
  have hm := RadiatingSourceRepresentation.actual_response k hk 1 (by norm_num)
    (StaticCoefficient.sqrtMultiplier c u) ρ
    (DynamicVolume.source_integrable c u 1 (ModalWeightedMode.coefficient_support n hn)) hs hF
    (scatteredE (n : ℂ) k) (scatteredH (n : ℂ) k)
    (fun T i => (scattered_local_L2 (n : ℂ) k (ofReal_ne_zero.mpr hk.ne') T i).1)
    (fun T i => (scattered_local_L2 (n : ℂ) k (ofReal_ne_zero.mpr hk.ne') T i).2)
    (ModalDrivenSource.forced n hn k hk.ne')
    (fun i x hx => scattered_smooth_exterior (n : ℂ) k (ofReal_ne_zero.mpr hk.ne') i x hx)
    (ModalDrivenRadiation.trace (n : ℂ) k hk.ne')
  exact hm.1

theorem volume_equation (n : ℝ) (hn : 1 < n) (k : ℝ) (hk : 0 < k) :
    DynamicVolume.volumeBlock (ModalWeightedMode.coefficient n hn) k 1
      (ModalVolumeData.numerator n hn k) =
        ModalDriven.determinant (n : ℂ) k • ModalVolumeData.incident n hn k := by
  let d := ModalDriven.determinant (n : ℂ) k
  let f := ModalVolumeData.incident n hn k
  let E := ModalDriven.electric (n : ℂ) k
  let EI : Field := fun x => d • ModalOrigin.centerE k x
  have hf (i : Fin 3) : (fun x => (d • f) (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt ((ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) * EI x i := by
    have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul d f)
    filter_upwards [hs, ModalVolumeData.incident_actual n hn k i] with x hs hi
    change (d • f) (VectorFourier.coordinateMap x) i = _
    rw [hs]
    simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
    dsimp [f]
    rw [hi]
    dsimp [EI]
    ring
  have he (i : Fin 3) : (fun x => MaterialField.scattered (ModalWeightedMode.coefficient n hn) k
      (ModalVolumeData.numerator n hn k) x i) =ᵐ[volume] fun x => E x i - EI x i := by
    filter_upwards [(response n hn k hk).symm] with x hx
    have h := congrFun hx i
    simpa [scatteredE, E, EI, d, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  exact MaterialVolumeConverse.volume_equation _ k 1 _ _ E EI
    (ModalWeightedMode.coefficient_support n hn)
    (ModalDrivenSource.weighted_actual n hn k (ofReal_ne_zero.mpr hk.ne')) hf he

#print axioms OQ14.ModalDrivenRepresentation.volume_equation
#print axioms OQ14.ModalDrivenRepresentation.response
end OQ14.ModalDrivenRepresentation


