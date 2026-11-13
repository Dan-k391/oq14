import FullChannelFarBound

/-! Bounded global scattering operator for the actual compact material. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FullChannelContinuous
open MeasureTheory FullChannelFreeMap

/-- The full physical scattering formula is a bounded complex-linear operator on
    the entire transverse incoming angular L² space. -/
def scatteringCLM (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c) :
    transverse →L[ℂ] ComplexVectorSphere.Ambient :=
  (-(Lp.compMeasurePreservingₗᵢ ℂ antipode antipode_preserving).toContinuousLinearMap).comp transverse.subtypeL +
    (1 / (Real.sqrt 2 : ℂ)) • (FullChannelFarBound.farCLM c d).comp
      ((Ring.inverse (DynamicVolume.volumeBlock c 1 d.radius)).comp (FullChannelBoundedDatum.datumCLM c d))

/-- The bounded operator is exactly the established actual physical formula. -/
theorem scatteringCLM_eq (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : transverse) : scatteringCLM c d F = scatteringLinear c d F := by
  change freeMap F.val + (1 / (Real.sqrt 2 : ℂ)) •
    ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ
      (ChannelScatteringMap.farMap c d
        (Ring.inverse (DynamicVolume.volumeBlock c 1 d.radius) (FullChannelBoundedDatum.datumCLM c d F))) = _
  rw [FullChannelBoundedDatum.datumCLM_eq]
  rfl

/-- The actual global physical scattering formula is continuous. -/
theorem scatteringLinear_continuous (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c) :
    Continuous (scatteringLinear c d) := by
  have h : (fun F => scatteringLinear c d F) = fun F => scatteringCLM c d F := by
    funext F
    exact (scatteringCLM_eq c d F).symm
  change Continuous (fun F => scatteringLinear c d F)
  rw [h]
  exact (scatteringCLM c d).continuous

/-- The bounded global operator reproduces the complete physical output for every finite TE incident field. -/
theorem scatteringCLM_on_TE (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    scatteringCLM c d ⟨RestrictedTEInput.input A, RestrictedTEInput.input_transverse A⟩ =
      ChannelScatteringMap.scatterMap c d A := by
  rw [scatteringCLM_eq]
  exact scatteringLinear_on_TE c d A

end OQ14.FullChannelContinuous
#print axioms OQ14.FullChannelContinuous.scatteringCLM_eq
#print axioms OQ14.FullChannelContinuous.scatteringLinear_continuous

#print axioms OQ14.FullChannelContinuous.scatteringCLM_on_TE
