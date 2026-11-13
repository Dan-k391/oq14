import HelmholtzProjection
import WeakPotentialProjection
import WeakPoynting.InteriorTestDensity
import WeakPoynting.DivCurlCompact

/-! The actual transverse Fourier projection is divergence free as an L²
field against compact C¹ tests. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05TransverseDivergence
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.PartialSmoothing OQ14.HelmholtzProjection
  OQ14.WeakPotentialProjection OQ14.NewtonL2
open scoped Topology SchwartzMap InnerProductSpace

def transverse (F : VectorFourier.VectorL2) : VectorFourier.VectorL2 :=
  F - VectorFourier.physicalProjection F

def transverseCoordinates (F : VectorFourier.VectorL2) : L2Vector :=
  fun i => physicalCoordinate (transverse F) i

theorem transverse_projection_zero (F : VectorFourier.VectorL2) :
    VectorFourier.physicalProjection (transverse F) = 0 := by
  simp [transverse, VectorFourier.physicalProjection_idempotent_apply]

theorem transverse_schwartz_divergence_zero (F : VectorFourier.VectorL2) (f : 𝓢(Maxwell.Space, ℂ)) :
    ∑ i : Fin 3, scalarProduct (transverseCoordinates F i)
      (FourierL2.embed (GradientProjection.pderivative i f)) = 0 := by
  have h := ((gradient_annihilator_iff (transverse F)).2 (transverse_projection_zero F)) (NewtonL2.conjugate f)
  rw [gradient_inner_pairing] at h
  have hc : NewtonL2.conjugate (NewtonL2.conjugate f) = f := by
    ext x
    simp [NewtonL2.conjugate_apply]
  rw [hc] at h
  simpa only [scalarProduct_embed, transverseCoordinates] using h

theorem transverse_weak_divergence (F : VectorFourier.VectorL2) :
    HasWeakDivergence (transverseCoordinates F) 0 := by
  intro φ
  let ψ : DomainCurl.Test Set.univ := ⟨φ, Set.subset_univ _⟩
  obtain ⟨K, f, hK, _, hfK, hf, hd⟩ := InteriorTestDensity.interior_test_approximation isOpen_univ ψ
  have hn (n : ℕ) : scalarProduct (transverseCoordinates F 0)
      (FourierL2.embed (GradientProjection.pderivative 0 (f n))) +
    scalarProduct (transverseCoordinates F 1)
      (FourierL2.embed (GradientProjection.pderivative 1 (f n))) +
    scalarProduct (transverseCoordinates F 2)
      (FourierL2.embed (GradientProjection.pderivative 2 (f n))) = 0 := by
    simpa only [Fin.sum_univ_three] using transverse_schwartz_divergence_zero F (f n)
  have hlim := (((scalarProduct (transverseCoordinates F 0)).continuous.tendsto _ |>.comp (hd 0)).add
    ((scalarProduct (transverseCoordinates F 1)).continuous.tendsto _ |>.comp (hd 1))).add
    ((scalarProduct (transverseCoordinates F 2)).continuous.tendsto _ |>.comp (hd 2))
  have hz := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (hn n).symm)))
  simpa only [ψ, testDerivativeL2, scalarProduct_continuousL2, valuePair, derivativePair, map_zero, zero_add] using hz

end OQ14.Packet05TransverseDivergence
#print axioms OQ14.Packet05TransverseDivergence.transverse_projection_zero
#print axioms OQ14.Packet05TransverseDivergence.transverse_schwartz_divergence_zero
#print axioms OQ14.Packet05TransverseDivergence.transverse_weak_divergence
