import FullChannelTEAdjoint

/-! The exact physical counted-device witness with its complete-output
adjoint identity attached to the very same material and scattering map. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 10000
namespace OQ14.FullChannelExactPassiveWitness
open Filter Topology MeasureTheory Maxwell MaterialMaxwell FrequencyScalingMaxwell FrequencyScalingFlux
  FrequencyScalingPower FrequencyScalingDevice PhysicalFieldIdentification
  RestrictedTEActualDevice RestrictedTEActualCounting RestrictedTEPassageTransfer RestrictedTEActualSquare
  RestrictedTEDipoleProfile RestrictedTEConcreteDevice RestrictedTEPartnerSmallness ChannelMaterialThroughput
  RestrictedTEActualPiecewise RestrictedTEBackgroundOutside PhysicalCountedSubspaces

def PowerPassiveWitness (k εp η δ τ L : ℝ) (N : ℕ) : Prop :=
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (hρh : ρ < h) (_ : 0 ≤ R)
      (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
        ‖abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)‖ + ρ ≤ R)
      (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ) (n r : ℕ),
      q ^ 2 ≤ εp ∧ 1 + χ ≤ εp ∧
      Orthonormal ℂ (fun j => RestrictedTEInput.input (A j)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range (fun j => RestrictedTEInput.input (A j)))) = N ∧
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
      IsUnit (DynamicVolume.volumeBlock (pairedCoeff q hq.le n r
        (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a))
          ρ χ hχ.le q n)) 1 (SourcePairedInclusion.data q hq.le n r).X) ∧
      (∃ d : BoundedMaterialKernel.SupportData (pairedCoeff q hq.le n r (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ hχ.le q n)),
        (FullChannelContinuous.scatteringCLM _ d).toLinearMap.comp FullChannelFreeMap.teInput =
          actualScatter (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ R (max R 1) hρ hχ.le (le_max_left R 1) hi q hq n r ∧
        ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := FullChannelClosedTE.inputSector)
            (F := ComplexVectorSphere.Ambient) (FullChannelClosedTE.restrictedScattering _ d)).comp
          (FullChannelClosedTE.restrictedScattering _ d) = (1 : FullChannelClosedTE.inputSector →L[ℂ] FullChannelClosedTE.inputSector)) ∧
        (∀ (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F),
          TestMaxwell k (dielectric (scaleCoeff k (pairedCoeff q hq.le n r (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ hχ.le q n))))
            (FrequencyScalingMaxwell.scaleField k
              (MaterialField.total (pairedCoeff q hq.le n r (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ hχ.le q n)) 1 (FullChannelTEMatch.normalizedSolution _ d F hF) (FullChannelTEMatch.normalizedElectric F)))
            (FrequencyScalingMaxwell.scaleField k
              (totalMagnetic (pairedCoeff q hq.le n r (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ hχ.le q n)) 1 (FullChannelTEMatch.normalizedSolution _ d F hF) (FullChannelMaterialMaxwell.normalizedMagnetic F)))) ∧
        (∀ (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F)
          (v : Maxwell.Space), ‖v‖ = 1 →
          Tendsto (fun t : ℝ => MaxwellFarField.factor k t •
            scaleField k (ExteriorContinuity.electric 1
              (DynamicVolume.source (pairedCoeff q hq.le n r (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ hχ.le q n)) (FullChannelTEMatch.normalizedSolution _ d F hF))) (t • v)) atTop
            (𝓝 (MaxwellFarField.electricAmplitude 1
              (DynamicVolume.source (pairedCoeff q hq.le n r (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ hχ.le q n)) (FullChannelTEMatch.normalizedSolution _ d F hF)) v)))) ∧
      IsCounted (Submodule.span ℂ (Set.range A))
        (actualScatter (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ R
          (max R 1) hρ hχ.le (le_max_left R 1) hi q hq n r)
        (fun a => PhysicalPlaneFlux.passage volume (Dsq (L / 2)) (flux k (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh q hq n r a))
        (fun a => PhysicalPlaneFlux.bypass volume (Dsq (L / 2)) (flux k (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh q hq n r a)) τ η δ ∧
      (∀ a ∈ Submodule.span ℂ (Set.range A),
        Integrable (flux k (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh q hq n r a) volume ∧
        Integrable (fun ξ => (flux k (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh q hq n r a ξ).re / 2) volume ∧
        Integrable (fun ξ => |(flux k (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh q hq n r a ξ).re| / 2) volume) ∧
      ∀ j : Fin N,
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
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j)))

/-- No finite number uniformly bounds these actual physical counted-channel dimensions. -/
theorem witness_passive (k εp η δ τ L : ℝ) (N : ℕ)
    (hw : FullChannelPowerFinal.PowerGlobalWitness k εp η δ τ L N) : PowerPassiveWitness k εp η δ τ L N := by
  obtain ⟨q,hq,χ,hχ,ρ,h,R,hρ,hρh,hR,hi,A,n,r,hqb,hχb,horth,hdim,hdim2,hinc,hmat,hiso,hunit,
    ⟨d,hmatch,hfield,hfar⟩,hcount,hint,hid⟩ := hw
  have ha := FullChannelTEAdjoint.actual_scattering_adjoint _ d _ hmatch hiso
  exact ⟨q,hq,χ,hχ,ρ,h,R,hρ,hρh,hR,hi,A,n,r,hqb,hχb,horth,hdim,hdim2,hinc,hmat,hiso,hunit,
    ⟨d,hmatch,ha,hfield,hfar⟩,hcount,hint,hid⟩

theorem unrestricted_exact_passive (k : ℝ) (hk : 0 < k) (εp : ℝ) (hεp : 1 < εp)
    (η δ : ℝ) (hη : 0 < η) (hηδ : η < δ) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (L : ℝ) (hL : 0 < L) (N : ℕ) : PowerPassiveWitness k εp η δ τ L N :=
  witness_passive k εp η δ τ L N
    (FullChannelPowerFinal.unrestricted_counted_power_global k hk εp hεp η δ hη hηδ τ hτ0 hτ1 L hL N)
end OQ14.FullChannelExactPassiveWitness
#print axioms OQ14.FullChannelExactPassiveWitness.witness_passive
#print axioms OQ14.FullChannelExactPassiveWitness.unrestricted_exact_passive
