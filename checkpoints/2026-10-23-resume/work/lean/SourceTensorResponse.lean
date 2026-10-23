import SourceModeReaction

/-! Actual infinite-mode core tensor response of a finite physical dielectric stack. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceTensorResponse
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem
open OQ14.SourceModeDatum OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization

def freeDatum (c : Coefficient) (d : Data) (y : Space) (hy : ‖y‖<d.R) (j : Fin 3) :
    VectorFourier.VectorL2 :=
  FreeDyadicMaterialData.datum c d.R d.X (fun i => FreeDyadicMaterialData.free d.R d.X y hy i j)

def reaction (c : Coefficient) (d : Data) (y : Space) (hy : ‖y‖<d.R) (x : Space) (i j : Fin 3) : ℂ :=
  ∑ h : Fin 3, ∫ z : Space, DynamicVolume.source c
    (MaterialField.solution c 1 d.X (freeDatum c d y hy j)) h z*DyadicKernel.dyadic 1 (x-z) i h

theorem freeDatum_actual (c : Coefficient) (d : Data)
    (hm : ∀ x : Space,(c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (y : Space) (hy : ‖y‖<d.R) (i j : Fin 3) :
    (fun x => freeDatum c d y hy j (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*DyadicKernel.dyadic 1 (x-y) i j :=
  FreeDyadicMaterialData.free_datum_actual c d.R d.X y hy
    (annulus_support c d (SourceWeightedDatum.material_outer c d hm) (SourceWeightedDatum.material_inner c d hm)) i j

theorem actual_hasSum (c : Coefficient) (d : Data)
    (hm : ∀ x : Space,(c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.X))
    (b B T : ℝ) (hb : 0≤b) (hB : 0≤B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B)
    (hT : 2≤T) (hBT : 2*(B*AngularExteriorBounds.base)≤T) (hTR : T<d.R)
    (x y : Space) (hx : ‖x‖<d.R) (hy : ‖y‖≤b) (hyR : ‖y‖<d.R) (i j : Fin 3) :
    HasSum (fun a : PositiveIndex => SourceModeReaction.term d a x y i j) (reaction c d y hyR x i j) := by
  let hc := SourceWeightedDatum.material_outer c d hm
  let hi := SourceWeightedDatum.material_inner c d hm
  have hs := CoreMaterialEvaluation.core_hasSum c d.R d.X (annulus_support c d hc hi) x hx i _ _
    (FreeDyadicMaterialData.solution_hasSum c b B T d.R d.X hb hB hscale hT hBT d.hR hTR y hy hyR j)
  convert hs using 1
  funext a
  exact (SourceModeReaction.mode_core c d hm hdisp hu hc hi a x y hx i j).symm

theorem physical_hasSum (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ)
    (b B T : ℝ) (hb : 0≤b) (hB : 0≤B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B)
    (hT : 2≤T) (hBT : 2*(B*AngularExteriorBounds.base)≤T) (hTR : T<d.R)
    (x y : Space) (hx : ‖x‖<d.R) (hy : ‖y‖≤b) (hyR : ‖y‖<d.R) (i j : Fin 3) :
    HasSum (fun a : PositiveIndex => SourceModeReaction.term d a x y i j)
      (reaction (SourceMaterialCoefficient.coefficient d M hM hs) d y hyR x i j) :=
  actual_hasSum _ d (SourceMaterialCoefficient.value_complex d M hM hs) hdisp
    (SourceMaterialPartition.volumeBlock_isUnit d M hM hs 1 (by norm_num))
    b B T hb hB hscale hT hBT hTR x y hx hy hyR i j

theorem physical_tsum (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ)
    (b B T : ℝ) (hb : 0≤b) (hB : 0≤B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B)
    (hT : 2≤T) (hBT : 2*(B*AngularExteriorBounds.base)≤T) (hTR : T<d.R)
    (x y : Space) (hx : ‖x‖<d.R) (hy : ‖y‖≤b) (hyR : ‖y‖<d.R) (i j : Fin 3) :
    (∑' a : PositiveIndex,SourceModeReaction.term d a x y i j)=
      reaction (SourceMaterialCoefficient.coefficient d M hM hs) d y hyR x i j :=
  (physical_hasSum d M hM hs hdisp b B T hb hB hscale hT hBT hTR x y hx hy hyR i j).tsum_eq

end OQ14.SourceTensorResponse
#print axioms OQ14.SourceTensorResponse.freeDatum_actual
#print axioms OQ14.SourceTensorResponse.actual_hasSum
#print axioms OQ14.SourceTensorResponse.physical_hasSum
#print axioms OQ14.SourceTensorResponse.physical_tsum
