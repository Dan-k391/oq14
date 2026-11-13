import FullChannelActualBridge
import FullChannelFrequency

/-! Full unrestricted-channel counted-device endpoint and global physical scattering extension. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.FullChannelEndpoint
open Filter Topology MeasureTheory Maxwell MaterialMaxwell FrequencyScalingMaxwell FrequencyScalingFlux
  FrequencyScalingPower FrequencyScalingDevice PhysicalFieldIdentification
  RestrictedTEActualDevice RestrictedTEActualCounting RestrictedTEPassageTransfer RestrictedTEActualSquare
  RestrictedTEDipoleProfile RestrictedTEConcreteDevice RestrictedTEPartnerSmallness ChannelMaterialThroughput
  RestrictedTEActualPiecewise RestrictedTEBackgroundOutside PhysicalCountedSubspaces FullChannelFreeMap

/-- The complete actual counted-device witness, its physical L² dimension and its
    restriction identity with the global full-output scattering formula. -/
def DeviceWitness (k εp η δ τ L : ℝ) (N : ℕ) : Prop :=
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (hρh : ρ < h) (_ : 0 ≤ R)
      (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
        ‖RestrictedTEDipoleProfile.abovePoint
          (RestrictedTEConcreteDevice.hpoint (-(k * (L / 2))) (RestrictedTEActualSquare.ysq N (k * (L / 2))) l) (h * a)‖ + ρ ≤ R)
      (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ) (n r : ℕ),
      q ^ 2 ≤ εp ∧ 1 + χ ≤ εp ∧
      Orthonormal ℂ (fun j => RestrictedTEInput.input (A j)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range (fun j => RestrictedTEInput.input (A j)))) = N ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      (∀ a : SymmetricHarmonicJets.Index →₀ ℂ,
        TestMaxwell k (fun _ => 1) (scaleField k (RestrictedTEPlaneLocal.electric a))
          (scaleField k (RestrictedTEPlaneLocal.magnetic a)) ∧
        Tendsto (scaledInwardPower k a) atTop (𝓝 (RestrictedTEIncoming.physicalPower a))) ∧
      (max R 1 ≤ (SourcePairedInclusion.data q hq.le n r).R ∧
        ∀ x : FourierL2.Space,
          1 ≤ MaterialMaxwell.dielectric (scaleCoeff k (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a))
              ρ χ hχ.le q n))) x ∧
          MaterialMaxwell.dielectric (scaleCoeff k (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a))
              ρ χ hχ.le q n))) x ≤ εp) ∧
      (∀ a : SymmetricHarmonicJets.Index →₀ ℂ,
        ‖actualScatter (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ R
          (max R 1) hρ hχ.le (le_max_left R 1) hi q hq n r a‖ ^ 2 = RestrictedTEIncoming.physicalPower a) ∧
      IsCounted (Submodule.span ℂ (Set.range A))
        (actualScatter (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ R
          (max R 1) hρ hχ.le (le_max_left R 1) hi q hq n r)
        (fun a => PhysicalPlaneFlux.passage volume (Dsq (L / 2)) (flux k (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh q hq n r a))
        (fun a => PhysicalPlaneFlux.bypass volume (Dsq (L / 2)) (flux k (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh q hq n r a)) τ η δ ∧
      (∀ a ∈ Submodule.span ℂ (Set.range A),
        Integrable (flux k (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh q hq n r a) volume ∧
        Integrable (fun ξ => (flux k (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh q hq n r a ξ).re / 2) volume ∧
        Integrable (fun ξ => |(flux k (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh q hq n r a ξ).re| / 2) volume) ∧
      (∀ j : Fin N,
        PhysicallyIdentifiedAt k q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)
            (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (max R 1) (A j) ∧
          TestMaxwell k (MaterialMaxwell.dielectric (scaleCoeff k (pairedCoeff q hq.le n r
              (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))))
            (scaleField k (physE q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)
              (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j)))
            (scaleField k (physH q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)
              (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j))) ∧
          (∀ ξ : PlaneInverseCube.Plane, ‖ξ‖ ≠ RadialPhaseLimit.radius r / k →
            scaleMap k (deviceFieldsE (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh hq
                (le_max_left R 1) (OQ14.RestrictedTEBackgroundOutside.outFieldE q hq.le
                  (devRadE (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hq)) n r) (A j) ξ =
              scaleField k (spaceFieldE q hq.le n r
                (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)
                (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (max R 1) (A j))
                (MaxwellPlaneTail.planePoint ξ) ∧
            scaleMap k (deviceFieldsH (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh hq
                (le_max_left R 1) (OQ14.RestrictedTEBackgroundOutside.outFieldH q hq.le
                  (devRadH (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hq)) n r) (A j) ξ =
              scaleField k (spaceFieldH q hq.le n r
                (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)
                (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (max R 1) (A j))
                (MaxwellPlaneTail.planePoint ξ)) ∧
          ((∀ i : Fin 3, (fun y => scaleField k (physE q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j)) y i) =ᵐ[volume]
              fun y => MaterialField.total (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))) k
                (MaterialField.solution (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))) k
              ((SourcePairedInclusion.data q hq.le n r).X / k)
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r (A j) +
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j))))
                (scaleField k (RestrictedTEPlaneLocal.electric (A j))) y i) ∧
            (∀ (y : Maxwell.Space) (i : Fin 3),
              scaleField k (physH q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j)) y i =
                MaterialMaxwell.totalMagnetic (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))) k
                  (MaterialField.solution (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))) k
              ((SourcePairedInclusion.data q hq.le n r).X / k)
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r (A j) +
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j))))
                  (scaleField k (RestrictedTEPlaneLocal.magnetic (A j))) y i) ∧
            SourcePairedPlaneIdentification.IsDatum (scaleCoeff k (SourcePairedInclusion.shell q hq.le n r))
              (scaleField k (RestrictedTEPlaneLocal.electric (A j)))
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r (A j))) ∧
            SourcePairedPlaneIdentification.IsDatum (scaleCoeff k (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))
              (scaleField k (RestrictedTEPlaneLocal.electric (A j)))
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j))) ∧
            OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r (A j) +
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j)) =
              OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r (A j)) +
                OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j)) ∧
            (IsUnit (DynamicVolume.volumeBlock (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n))) k
                ((SourcePairedInclusion.data q hq.le n r).X / k)) ↔
              IsUnit (DynamicVolume.volumeBlock (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)) 1
                (SourcePairedInclusion.data q hq.le n r).X))) ∧
          SourcePairedPlaneIdentification.IsDatum (scaleCoeff k (pairedCoeff q hq.le n r (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n)))
              (scaleField k (RestrictedTEPlaneLocal.electric (A j)))
              (OQ14.DilationL2.dilate k (OQ14.RestrictedTEActualCore.fsLin q hq.le n r (A j) +
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j)))) ∧
      ∃ d : BoundedMaterialKernel.SupportData (ChannelMaterialThroughput.pairedCoeff q hq.le n r
        (RestrictedTEPartnerSmallness.deviceCoeff
          (fun a l => RestrictedTEDipoleProfile.abovePoint
            (RestrictedTEConcreteDevice.hpoint (-(k * (L / 2))) (RestrictedTEActualSquare.ysq N (k * (L / 2))) l) (h * a))
          ρ χ hχ.le q n)),
        (scatteringLinear _ d).comp teInput =
          actualScatter (fun a l => RestrictedTEDipoleProfile.abovePoint
            (RestrictedTEConcreteDevice.hpoint (-(k * (L / 2))) (RestrictedTEActualSquare.ysq N (k * (L / 2))) l) (h * a))
          ρ χ R (max R 1) hρ hχ.le (le_max_left R 1) hi q hq n r

/-- Unrestricted counted-device endpoint with the actual bounded full-input scattering
    extension, all-input weak material Maxwell fields, and power-normalized frequency-k
    radiated far amplitudes. The all-input material equation explicitly uses the physical
    volume-block invertibility hypothesis; the device witness itself is unconditional. -/
theorem full_unrestricted (k : ℝ) (hk : 0 < k) (εp : ℝ) (hεp : 1 < εp)
    (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (L : ℝ) (hL : 0 < L) (N : ℕ) :
    DeviceWitness k εp η δ τ L N ∧
    (∀ (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
      (F : transverse),
      FullChannelContinuous.scatteringCLM c d F = scatteringLinear c d F ∧
      ComplexVectorSphere.IsTangential (FullChannelContinuous.scatteringCLM c d F)) ∧
    (∀ (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
      (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F),
      IsUnit (DynamicVolume.volumeBlock c 1 d.radius) →
      TestMaxwell k (dielectric (scaleCoeff k c))
        (PuncturedMaxwellScaling.fieldAtFrequency k
          (MaterialField.total c 1 (FullChannelTEMatch.normalizedSolution c d F hF) (FullChannelTEMatch.normalizedElectric F)))
        (PuncturedMaxwellScaling.fieldAtFrequency k
          (totalMagnetic c 1 (FullChannelTEMatch.normalizedSolution c d F hF) (FullChannelMaterialMaxwell.normalizedMagnetic F)))) ∧
    (∀ (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
      (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F)
      (n : Maxwell.Space), ‖n‖ = 1 →
      Tendsto (fun r : ℝ => MaxwellFarField.factor k r •
        scaleField k (ExteriorContinuity.electric 1
          (DynamicVolume.source c (FullChannelTEMatch.normalizedSolution c d F hF))) (r • n)) atTop
        (𝓝 (MaxwellFarField.electricAmplitude 1
          (DynamicVolume.source c (FullChannelTEMatch.normalizedSolution c d F hF)) n))) := by
  refine ⟨every_dimension_global k hk εp hεp η δ hη hηδ τ hτ0 hτ1 L hL N, ?_, ?_, ?_⟩
  · intro c d F
    exact ⟨FullChannelContinuous.scatteringCLM_eq c d F, by
      rw [FullChannelContinuous.scatteringCLM_eq]
      exact scatteringLinear_tangential c d F⟩
  · intro c d F hF hu
    exact FullChannelFrequency.material_maxwell_at_frequency k hk c d F hF hu
  · intro c d F hF n hn
    exact FullChannelFrequency.radiated_far_at_frequency k hk c d F hF n hn

/-- No finite uniform dimension bound can hold for the actual counted-device family. -/
theorem no_uniform_bound (k : ℝ) (hk : 0 < k) (εp : ℝ) (hεp : 1 < εp)
    (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (L : ℝ) (hL : 0 < L) :
    ¬ ∃ B : ℕ, ∀ N, DeviceWitness k εp η δ τ L N → N ≤ B := by
  rintro ⟨B, hB⟩
  have h := hB (B+1) (every_dimension_global k hk εp hεp η δ hη hηδ τ hτ0 hτ1 L hL (B+1))
  omega

end OQ14.FullChannelEndpoint
#print axioms OQ14.FullChannelEndpoint.full_unrestricted
#print axioms OQ14.FullChannelEndpoint.no_uniform_bound
