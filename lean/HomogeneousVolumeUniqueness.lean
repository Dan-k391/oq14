import HomogeneousVolumePower

/-! # Actual closing identities for homogeneous volume uniqueness

The physical field components are globally locally integrable by their proved
L2 bounds on every finite ball. If the actual homogeneous electric field is AE
zero, material self-consistency makes the actual source zero, hence the genuine
square-root-weighted L2 unknown is zero. The actual volume equation then forces
the original unknown to vanish, without dividing by a material coefficient.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace OQ14.HomogeneousVolumeUniqueness

open MeasureTheory Metric OQ14.Maxwell

abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

theorem locallyIntegrable_of_memLp_closedBalls (f : Space → ℂ)
    (hf : ∀ T : ℝ, MemLp f 2 (volume.restrict (closedBall 0 T))) :
    LocallyIntegrable f := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨T,hT⟩ := hK.isBounded.subset_closedBall (0 : Space)
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) T)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 T).measure_ne_top
  have hi : IntegrableOn f (closedBall 0 T) :=
    (hf T).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  exact hi.mono_set hT

theorem electric_locallyIntegrable (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) : LocallyIntegrable (fun x => HomogeneousVolumePower.electric c k R u x i) :=
  locallyIntegrable_of_memLp_closedBalls _
    (fun T => HomogeneousVolumePower.electric_memLp_ball c k R T u hc i)

theorem magnetic_locallyIntegrable (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) : LocallyIntegrable (fun x => HomogeneousVolumePower.magnetic c k u x i) :=
  locallyIntegrable_of_memLp_closedBalls _
    (fun T => HomogeneousVolumePower.magnetic_memLp_ball c k R T u hc i)

theorem source_zero_of_electric_zero (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hsol : DynamicVolume.volumeBlock c k R u = 0)
    (hE : HomogeneousVolumePower.electric c k R u =ᵐ[volume] 0) (i : Fin 3) :
    DynamicVolume.source c u i =ᵐ[volume] 0 := by
  have hI : ∀ j : Fin 3,
      (fun x : Space => (0 : VectorL2) (VectorFourier.coordinateMap x) j) =ᵐ[volume]
        fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*(0 : ℂ) := by
    intro j
    simpa only [mul_zero] using HomogeneousVolumePower.zero_datum_coordinate_ae j
  have hm := ExteriorMaterial.material_relation c k R u 0 (fun _ _ => 0) hc hI hsol i
  filter_upwards [hm,hE] with x hx he
  change DynamicVolume.source c u i x = 0
  rw [hx]
  change (c.value (VectorFourier.coordinateMap x) : ℂ)*
    (0+ExteriorMaterial.scattered c k R u x i) = 0
  change ExteriorMaterial.scattered c k R u x = 0 at he
  rw [he]
  simp only [Pi.zero_apply, zero_add, mul_zero]

theorem weighted_unknown_zero_of_source_zero (c : Coefficient) (u : VectorL2)
    (hρ : ∀ i : Fin 3, DynamicVolume.source c u i =ᵐ[volume] 0) :
    StaticCoefficient.sqrtMultiplier c u = 0 := by
  have hm := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c u)
  have hcoord : (fun x : Space => (StaticCoefficient.sqrtMultiplier c u)
      (VectorFourier.coordinateMap x)) =ᵐ[volume] 0 := by
    filter_upwards [hm,ae_all_iff.mpr hρ] with x hx hs
    funext i
    have hi := congrFun hx i
    change (StaticCoefficient.sqrtMultiplier c u) (VectorFourier.coordinateMap x) i = 0
    rw [hi]
    exact hs i
  have hf := (MeasurePreserving.symm VectorFourier.coordinateMap
    VectorFourier.coordinateMap_preserving).quasiMeasurePreserving.ae hcoord
  apply Lp.ext
  filter_upwards [hf,Lp.coeFn_zero VectorFourier.Vector 2
    (volume : Measure VectorFourier.Frequency)] with ξ hξ hzero
  simpa only [MeasurableEquiv.apply_symm_apply, Function.comp_apply] using hξ.trans hzero.symm

theorem volumeBlock_eq_unknown_of_weighted_zero (c : Coefficient) (k R : ℝ)
    (u : VectorL2) (hu : StaticCoefficient.sqrtMultiplier c u = 0) :
    DynamicVolume.volumeBlock c k R u = u := by
  change (u-StaticCoefficient.sqrtMultiplier c
    (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u))) -
      StaticCoefficient.sqrtMultiplier c
        (DynamicConvolution.operator k (2*R) (StaticCoefficient.sqrtMultiplier c u)) = u
  simp only [hu,map_zero,sub_zero]

theorem unknown_zero_of_electric_zero (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hsol : DynamicVolume.volumeBlock c k R u = 0)
    (hE : HomogeneousVolumePower.electric c k R u =ᵐ[volume] 0) : u = 0 := by
  have hw := weighted_unknown_zero_of_source_zero c u
    (source_zero_of_electric_zero c k R u hc hsol hE)
  calc
    u = DynamicVolume.volumeBlock c k R u :=
      (volumeBlock_eq_unknown_of_weighted_zero c k R u hw).symm
    _ = 0 := hsol

end OQ14.HomogeneousVolumeUniqueness
