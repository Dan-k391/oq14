import FullChannelClosedTE
import Mathlib.MeasureTheory.Function.LpOrder

/-! The physical transverse angular L² space and its closed TE sector
are complete Hilbert spaces. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.FullChannelTEHilbert
open Set Filter MeasureTheory FullChannelFreeMap FullChannelClosedTE
open scoped Topology

theorem transverse_closed : IsClosed (transverse : Set ComplexVectorSphere.Ambient) := by
  apply IsSeqClosed.isClosed
  intro F G hF hFG
  obtain ⟨φ,hφ,hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hFG).exists_seq_tendsto_ae
  have ht : ∀ᵐ x ∂SphereHarmonicBasis.angularMeasure, ∀ n, inner (ComplexVectorSphere.embedVector ((x : SphereHarmonicBasis.Sphere) : Maxwell.Space)) (F n x) = (0 : ℂ) :=
    ae_all_iff.mpr hF
  filter_upwards [ht,hpoint] with x hx hp
  have hc : Continuous (fun v : ComplexVectorSphere.Vector => @inner ℂ ComplexVectorSphere.Vector _ (ComplexVectorSphere.embedVector ((x : SphereHarmonicBasis.Sphere) : Maxwell.Space)) v) :=
    continuous_const.inner continuous_id
  have hlim : Tendsto (fun n => inner (ComplexVectorSphere.embedVector ((x : SphereHarmonicBasis.Sphere) : Maxwell.Space)) (F (φ n) x)) atTop
      (𝓝 (inner (ComplexVectorSphere.embedVector ((x : SphereHarmonicBasis.Sphere) : Maxwell.Space)) (G x))) :=
    hc.continuousAt.tendsto.comp hp
  have hzero : (fun n => inner (ComplexVectorSphere.embedVector ((x : SphereHarmonicBasis.Sphere) : Maxwell.Space)) (F (φ n) x)) = fun _ => (0 : ℂ) := by
    funext n
    exact hx (φ n)
  rw [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

instance transverse_complete : CompleteSpace transverse := transverse_closed.completeSpace_coe
instance sector_complete : CompleteSpace inputSector := (Submodule.isClosed_topologicalClosure _).completeSpace_coe

end OQ14.FullChannelTEHilbert
#print axioms OQ14.FullChannelTEHilbert.transverse_closed
#print axioms OQ14.FullChannelTEHilbert.transverse_complete
#print axioms OQ14.FullChannelTEHilbert.sector_complete
