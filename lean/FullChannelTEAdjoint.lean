import FullChannelTEHilbert
import FullChannelPhysicalPassivity
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Exact Hilbert-space adjoint identity for the complete physical output
of the counted channel device on its selected incoming TE sector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.FullChannelTEAdjoint
open FullChannelFreeMap FullChannelContinuous FullChannelClosedTE FullChannelTEHilbert

theorem actual_scattering_adjoint (c : StaticCoefficient.Coefficient)
    (d : BoundedMaterialKernel.SupportData c)
    (out : (SymmetricHarmonicJets.Index →₀ ℂ) →ₗ[ℂ] ComplexVectorSphere.Ambient)
    (hmatch : (scatteringCLM c d).toLinearMap.comp teInput = out)
    (hpower : ∀ A, ‖out A‖^2 = RestrictedTEIncoming.physicalPower A) :
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := inputSector) (F := ComplexVectorSphere.Ambient) (restrictedScattering c d)).comp (restrictedScattering c d) = (1 : inputSector →L[ℂ] inputSector) := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
  exact (FullChannelCountedTEPassivity.counted_device_sector_isometric c d out hmatch hpower).2.2.1

theorem isometry_adjoint (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (hiso : ∀ F : inputSector, ‖restrictedScattering c d F‖ = ‖F‖) :
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := inputSector) (F := ComplexVectorSphere.Ambient) (restrictedScattering c d)).comp (restrictedScattering c d) = (1 : inputSector →L[ℂ] inputSector) :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp hiso
end OQ14.FullChannelTEAdjoint
#print axioms OQ14.FullChannelTEAdjoint.actual_scattering_adjoint
#print axioms OQ14.FullChannelTEAdjoint.isometry_adjoint
