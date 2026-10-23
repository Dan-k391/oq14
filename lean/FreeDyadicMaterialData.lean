import WeightedAnnulusDatum
import PiecewiseScattering

/-! Actual free-dyadic modal data converge in the material L2 Hilbert space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FreeDyadicMaterialData
open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.SphereHarmonicBasis
open OQ14.VectorHarmonicNormalization OQ14.OutgoingSpatialSeries OQ14.OutgoingGeometricTail
open OQ14.WeightedAnnulusDatum
open scoped Topology

theorem annulus_inner (R X : ℝ) (x : annulus R X) : R≤‖(x : Space)‖ := by
  have hn := x.property.2
  simpa only [mem_ball,dist_zero_right,not_lt] using hn

def mode (R X : ℝ) (hR : 0<R) (a : PositiveIndex) (y : Space) (i j : Fin 3) : C(annulus R X,ℂ) where
  toFun x := term a x y i j
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx : (x : Space)≠0 := norm_pos_iff.mp (hR.trans_le (annulus_inner R X x))
    exact (OutgoingFiniteHelmholtz.term_smooth a y i j x hx).continuousAt.comp continuous_subtype_val.continuousAt

def free (R X : ℝ) (y : Space) (hy : ‖y‖<R) (i j : Fin 3) : C(annulus R X,ℂ) where
  toFun x := DyadicKernel.dyadic 1 ((x : Space)-y) i j
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx : (x : Space)≠y := by
      intro he
      have hn := annulus_inner R X x
      rw [he] at hn
      linarith
    exact (PointDyadicHelmholtz.translated_smooth y x hx i j).continuousAt.comp continuous_subtype_val.continuousAt

theorem mode_hasSum (b B T R X : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hT : 2≤T)
    (hBT : 2*(B*AngularExteriorBounds.base)≤T) (hR : 0<R) (hTR : T<R)
    (y : Space) (hy : ‖y‖≤b) (hyR : ‖y‖<R) (i j : Fin 3) :
    HasSum (fun a : PositiveIndex => mode R X hR a y i j) (free R X y hyR i j) := by
  have hC := prefactor_nonnegative b T hb
  have hs : Summable (fun a : PositiveIndex => mode R X hR a y i j) := by
    apply Summable.of_norm_bounded (majorant b T) (majorant_summable b T hb)
    intro a
    have hM : 0≤majorant b T a := by dsimp [majorant];positivity
    rw [(mode R X hR a y i j).norm_le hM]
    intro x
    exact term_bound a b B T hb hB hscale hT hBT x y
      (hTR.le.trans (annulus_inner R X x)) hy i j
  have he : (∑' a : PositiveIndex,mode R X hR a y i j)=free R X y hyR i j := by
    ext x
    have hx := (hs.hasSum.mapL (ContinuousMap.evalCLM ℂ x)).tsum_eq
    change (∑' a : PositiveIndex,term a x y i j)=(∑' a : PositiveIndex,mode R X hR a y i j) x at hx
    rw [←hx]
    exact OutgoingFreeDyadic.actual_free_dyadic b B T hb hB hscale hT hBT y hy i j x
      (max_lt_iff.mpr ⟨hTR.trans_le (annulus_inner R X x),hyR.trans_le (annulus_inner R X x)⟩)
  exact he ▸ hs.hasSum

def datum (c : Coefficient) (R X : ℝ) (f : Fin 3 → C(annulus R X,ℂ)) : VectorFourier.VectorL2 :=
  ∑ i : Fin 3,DynamicConvolution.insert i (scalarMap c R X (f i))

theorem datum_coordinate (c : Coefficient) (R X : ℝ) (f : Fin 3 → C(annulus R X,ℂ)) (i : Fin 3) :
    NewtonL2.physicalCoordinate (datum c R X f) i=scalarMap c R X (f i) := by
  change DynamicConvolution.component i (∑ j : Fin 3,DynamicConvolution.insert j (scalarMap c R X (f j)))=_
  simp only [map_sum,DynamicConvolution.component_insert]
  simp

theorem datum_actual (c : Coefficient) (R X : ℝ) (f : Fin 3 → C(annulus R X,ℂ))
    (incident : Field) (hi : ∀ (i : Fin 3) (x : annulus R X),f i x=incident x i)
    (hc : ∀ x : Space,x∉annulus R X → c.value (VectorFourier.coordinateMap x)=0) (i : Fin 3) :
    (fun x => datum c R X f (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      (fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*incident x i) := by
  have h := (NewtonL2.physicalCoordinate_ae (datum c R X f) i).symm
  rw [datum_coordinate] at h
  exact h.trans (scalarMap_actual c R X (f i) (fun x => incident x i) (hi i) hc)

theorem datum_hasSum (c : Coefficient) (b B T R X : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hT : 2≤T)
    (hBT : 2*(B*AngularExteriorBounds.base)≤T) (hR : 0<R) (hTR : T<R)
    (y : Space) (hy : ‖y‖≤b) (hyR : ‖y‖<R) (j : Fin 3) :
    HasSum (fun a : PositiveIndex => datum c R X (fun i => mode R X hR a y i j))
      (datum c R X (fun i => free R X y hyR i j)) := by
  apply hasSum_sum
  intro i _
  exact (mode_hasSum b B T R X hb hB hscale hT hBT hR hTR y hy hyR i j).mapL
    ((DynamicConvolution.insert i).comp (scalarMap c R X))

theorem solution_hasSum (c : Coefficient) (b B T R X : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hT : 2≤T)
    (hBT : 2*(B*AngularExteriorBounds.base)≤T) (hR : 0<R) (hTR : T<R)
    (y : Space) (hy : ‖y‖≤b) (hyR : ‖y‖<R) (j : Fin 3) :
    HasSum (fun a : PositiveIndex => MaterialField.solution c 1 X
      (datum c R X (fun i => mode R X hR a y i j)))
      (MaterialField.solution c 1 X (datum c R X (fun i => free R X y hyR i j))) :=
  (datum_hasSum c b B T R X hb hB hscale hT hBT hR hTR y hy hyR j).mapL
    (Ring.inverse (DynamicVolume.volumeBlock c 1 X))


theorem free_datum_actual (c : Coefficient) (R X : ℝ) (y : Space) (hyR : ‖y‖<R)
    (hc : ∀ x : Space,x∉annulus R X → c.value (VectorFourier.coordinateMap x)=0) (i j : Fin 3) :
    (fun x => datum c R X (fun h => free R X y hyR h j) (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      (fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*DyadicKernel.dyadic 1 (x-y) i j) :=
  datum_actual c R X _ (fun x i => DyadicKernel.dyadic 1 (x-y) i j) (fun _ _ => rfl) hc i

theorem mode_datum_actual (c : Coefficient) (R X : ℝ) (hR : 0<R) (a : PositiveIndex) (y : Space)
    (hc : ∀ x : Space,x∉annulus R X → c.value (VectorFourier.coordinateMap x)=0) (i j : Fin 3) :
    (fun x => datum c R X (fun h => mode R X hR a y h j) (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      (fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*term a x y i j) :=
  datum_actual c R X _ (fun x i => term a x y i j) (fun _ _ => rfl) hc i

theorem partial_solution_limit (c : Coefficient) (b B T R X : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hT : 2≤T)
    (hBT : 2*(B*AngularExteriorBounds.base)≤T) (hR : 0<R) (hTR : T<R)
    (y : Space) (hy : ‖y‖≤b) (hyR : ‖y‖<R) (j : Fin 3) :
    Tendsto (fun s : Finset PositiveIndex => MaterialField.solution c 1 X
      (∑ a∈s,datum c R X (fun i => mode R X hR a y i j))) atTop
      (𝓝 (MaterialField.solution c 1 X (datum c R X (fun i => free R X y hyR i j)))) := by
  have h := solution_hasSum c b B T R X hb hB hscale hT hBT hR hTR y hy hyR j
  change Tendsto (fun s : Finset PositiveIndex => ∑ a∈s,MaterialField.solution c 1 X
    (datum c R X (fun i => mode R X hR a y i j))) atTop _ at h
  simpa only [MaterialField.solution,map_sum] using h

theorem physical_solution_series {ι : Type*} (c : Coefficient) (b B T R X : ℝ)
    (hb : 0≤b) (hB : 0≤B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hT : 2≤T)
    (hBT : 2*(B*AngularExteriorBounds.base)≤T) (hR : 0<R) (hTR : T<R) (hX : 0≤X)
    (hc : ∀ x : Space,x∉annulus R X → c.value (VectorFourier.coordinateMap x)=0)
    (p : PiecewiseMaxwellUniqueness.Partition ι (MaterialMaxwell.dielectric c))
    (i₀ : ι) (x₀ : Space) (hx₀ : x₀∈p.cell i₀) (hout : X<‖x₀‖)
    (y : Space) (hy : ‖y‖≤b) (hyR : ‖y‖<R) (j : Fin 3) :
    HasSum (fun a : PositiveIndex => MaterialField.solution c 1 X
      (datum c R X (fun i => mode R X hR a y i j)))
      (MaterialField.solution c 1 X (datum c R X (fun i => free R X y hyR i j))) ∧
    DynamicVolume.volumeBlock c 1 X
      (MaterialField.solution c 1 X (datum c R X (fun i => free R X y hyR i j)))=
      datum c R X (fun i => free R X y hyR i j) := by
  have hcX : ∀ x : Space,x∉closedBall 0 X → c.value (VectorFourier.coordinateMap x)=0 := by
    intro x hx
    exact hc x (fun ha => hx ha.1)
  have hu := PiecewiseMaxwellUniqueness.volumeBlock_isUnit c 1 (by norm_num) X hX hcX p i₀ x₀ hx₀ hout
  refine ⟨solution_hasSum c b B T R X hb hB hscale hT hBT hR hTR y hy hyR j,?_⟩
  exact congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 =>
    L (datum c R X (fun i => free R X y hyR i j)))
    (Ring.mul_inverse_cancel (DynamicVolume.volumeBlock c 1 X) hu)
end OQ14.FreeDyadicMaterialData

#print axioms OQ14.FreeDyadicMaterialData.annulus_inner
#print axioms OQ14.FreeDyadicMaterialData.mode_hasSum
#print axioms OQ14.FreeDyadicMaterialData.datum_coordinate
#print axioms OQ14.FreeDyadicMaterialData.datum_actual
#print axioms OQ14.FreeDyadicMaterialData.datum_hasSum
#print axioms OQ14.FreeDyadicMaterialData.solution_hasSum
#print axioms OQ14.FreeDyadicMaterialData.free_datum_actual
#print axioms OQ14.FreeDyadicMaterialData.mode_datum_actual
#print axioms OQ14.FreeDyadicMaterialData.partial_solution_limit
#print axioms OQ14.FreeDyadicMaterialData.physical_solution_series
