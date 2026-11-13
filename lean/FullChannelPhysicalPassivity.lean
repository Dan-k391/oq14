import FullChannelCountedTEPassivity

/-! The actual counted witness admits a contractive complete-output
scattering operator on its closed physical incoming TE Hilbert sector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace OQ14.FullChannelPhysicalPassivity
open Filter Topology MeasureTheory Maxwell MaterialMaxwell FrequencyScalingMaxwell FrequencyScalingFlux
  FrequencyScalingPower FrequencyScalingDevice PhysicalFieldIdentification
  RestrictedTEActualDevice RestrictedTEActualCounting RestrictedTEPassageTransfer RestrictedTEActualSquare
  RestrictedTEDipoleProfile RestrictedTEConcreteDevice RestrictedTEPartnerSmallness ChannelMaterialThroughput
  RestrictedTEActualPiecewise RestrictedTEBackgroundOutside PhysicalCountedSubspaces
  FullChannelFreeMap FullChannelContinuous FullChannelClosedTE FullChannelCountedTEPassivity
abbrev Input := SymmetricHarmonicJets.Index →₀ ℂ

theorem actual_witness_has_passive_sector (k εp η δ τ L : ℝ) (N : ℕ)
    (hw : FullChannelPowerFinal.PowerGlobalWitness k εp η δ τ L N) :
    ∃ (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
      (out : Input →ₗ[ℂ] ComplexVectorSphere.Ambient) (A : Fin N → Input) (P B : Input → ℝ),
      Orthonormal ℂ (fun j => RestrictedTEInput.input (A j)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      IsCounted (Submodule.span ℂ (Set.range A)) out P B τ η δ ∧
      (∀ a, teInput a ∈ inputSector) ∧
      (∀ a, restrictedScattering c d ⟨teInput a,finite_mem a⟩ = out a) ∧
      (∀ F : inputSector, ‖restrictedScattering c d F‖ = ‖F‖) := by
  obtain ⟨q,hq,χ,hχ,ρ,h,R,hρ,hρh,hR,hi,A,n,r,hqb,hχb,horth,hdim,hdim2,hinc,hmat,hiso,hunit,
    ⟨d,hmatch,hfield,hfar⟩,hcount,hint,hid⟩ := hw
  have hp := counted_device_sector_isometric _ d _ hmatch hiso
  exact ⟨_,d,_,A,_,_,horth,hdim,hcount,hp.1,hp.2.1,hp.2.2.1⟩

theorem unrestricted_counted_passive_sector (k : ℝ) (hk : 0 < k) (εp : ℝ) (hεp : 1 < εp)
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
      ∀ F : inputSector, ‖restrictedScattering c d F‖ = ‖F‖ := by
  have hw : FullChannelPowerFinal.PowerGlobalWitness k εp η δ τ L N :=
    FullChannelPowerFinal.unrestricted_counted_power_global k hk εp hεp η δ hη hηδ τ hτ0 hτ1 L hL N
  exact ⟨hw,actual_witness_has_passive_sector k εp η δ τ L N hw⟩
end OQ14.FullChannelPhysicalPassivity
#print axioms OQ14.FullChannelPhysicalPassivity.actual_witness_has_passive_sector
#print axioms OQ14.FullChannelPhysicalPassivity.unrestricted_counted_passive_sector
