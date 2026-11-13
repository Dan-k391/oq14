import FullChannelTEAdjoint

/-! The actual counted witness admits a contractive complete-output
scattering operator on its closed physical incoming TE Hilbert sector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace OQ14.FullChannelPassiveCountedFinal
open Filter Topology MeasureTheory Maxwell MaterialMaxwell FrequencyScalingMaxwell FrequencyScalingFlux
  FrequencyScalingPower FrequencyScalingDevice PhysicalFieldIdentification
  RestrictedTEActualDevice RestrictedTEActualCounting RestrictedTEPassageTransfer RestrictedTEActualSquare
  RestrictedTEDipoleProfile RestrictedTEConcreteDevice RestrictedTEPartnerSmallness ChannelMaterialThroughput
  RestrictedTEActualPiecewise RestrictedTEBackgroundOutside PhysicalCountedSubspaces
  FullChannelFreeMap FullChannelContinuous FullChannelClosedTE FullChannelCountedTEPassivity
abbrev Input := SymmetricHarmonicJets.Index →₀ ℂ

theorem unrestricted_counted_adjoint_identity (k : ℝ) (hk : 0 < k) (εp : ℝ) (hεp : 1 < εp)
    (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (L : ℝ) (hL : 0 < L) (N : ℕ) :
    FullChannelPowerFinal.PowerGlobalWitness k εp η δ τ L N ∧
    ∃ (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
      (out : Input →ₗ[ℂ] ComplexVectorSphere.Ambient) (A : Fin N → Input) (P B : Input → ℝ),
      Orthonormal ℂ (fun j => RestrictedTEInput.input (A j)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      IsCounted (Submodule.span ℂ (Set.range A)) out P B τ η δ ∧
      (∀ a, teInput a ∈ inputSector) ∧
      (∀ a, restrictedScattering c d ⟨teInput a,finite_mem a⟩ = out a) ∧
      (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := inputSector) (F := ComplexVectorSphere.Ambient)
        (restrictedScattering c d)).comp (restrictedScattering c d) = (1 : inputSector →L[ℂ] inputSector) := by
  obtain ⟨hw,c,d,out,A,P,B,ho,hd,hcount,hmem,hmatch,hiso⟩ :=
    FullChannelPhysicalPassivity.unrestricted_counted_passive_sector k hk εp hεp η δ hη hηδ τ hτ0 hτ1 L hL N
  exact ⟨hw,c,d,out,A,P,B,ho,hd,hcount,hmem,hmatch,FullChannelTEAdjoint.isometry_adjoint c d hiso⟩
end OQ14.FullChannelPassiveCountedFinal
#print axioms OQ14.FullChannelPassiveCountedFinal.unrestricted_counted_adjoint_identity
