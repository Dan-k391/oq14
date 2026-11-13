import FullChannelClosedTE

/-! The exact finite-TE power identity and the global physical matching
identity from the counted-device witness imply Hilbert-space passivity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FullChannelCountedTEPassivity
open FullChannelFreeMap FullChannelContinuous FullChannelClosedTE

theorem counted_device_sector_isometric (c : StaticCoefficient.Coefficient)
    (d : BoundedMaterialKernel.SupportData c)
    (out : (SymmetricHarmonicJets.Index →₀ ℂ) →ₗ[ℂ] ComplexVectorSphere.Ambient)
    (hmatch : (scatteringCLM c d).toLinearMap.comp teInput = out)
    (hpower : ∀ A, ‖out A‖^2 = RestrictedTEIncoming.physicalPower A) :
    (∀ A, teInput A ∈ inputSector) ∧
    (∀ A, restrictedScattering c d ⟨teInput A,finite_mem A⟩ = out A) ∧
    (∀ F : inputSector, ‖restrictedScattering c d F‖ = ‖F‖) ∧
    (∀ F : inputSector, ‖restrictedScattering c d F‖ ≤ ‖F‖) := by
  have hm (A : SymmetricHarmonicJets.Index →₀ ℂ) : scatteringCLM c d (teInput A)=out A := by
    exact LinearMap.congr_fun hmatch A
  have hp (A : SymmetricHarmonicJets.Index →₀ ℂ) :
      ‖scatteringCLM c d (teInput A)‖^2 = RestrictedTEIncoming.physicalPower A := by
    rw [hm]
    exact hpower A
  exact ⟨finite_mem,hm,sector_isometric c d hp,sector_contractive c d hp⟩
end OQ14.FullChannelCountedTEPassivity
#print axioms OQ14.FullChannelCountedTEPassivity.counted_device_sector_isometric
