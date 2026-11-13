import FullChannelEndpoint

/-! Counted-device construction with actual volume-inverse invertibility retained. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.FullChannelDeviceUnit
open Filter Topology MeasureTheory MaterialMaxwell FrequencyScalingMaxwell FrequencyScalingFlux
  FrequencyScalingPower FrequencyScalingDevice PhysicalFieldIdentification
  RestrictedTEActualDevice RestrictedTEActualCounting RestrictedTEPassageTransfer
  RestrictedTEActualSquare RestrictedTEDipoleProfile RestrictedTEConcreteDevice
  RestrictedTEPartnerSmallness ChannelMaterialThroughput RestrictedTEActualPiecewise
  RestrictedTEBackgroundOutside PhysicalCountedSubspaces

theorem counted_subspaces_physical_unit (k : ℝ) (hk : 0 < k) (εp : ℝ) (hεp : 1 < εp) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (L : ℝ) (hL : 0 < L) (N : ℕ) :
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (hρh : ρ < h) (_ : 0 ≤ R)
      (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
        ‖abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)‖ + ρ ≤ R)
      (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ) (n r : ℕ),
      q ^ 2 ≤ εp ∧ 1 + χ ≤ εp ∧
      Orthonormal ℂ (fun j => RestrictedTEInput.input (A j)) ∧
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
      IsUnit (DynamicVolume.volumeBlock (pairedCoeff q hq.le n r
        (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a))
          ρ χ hχ.le q n)) 1 (SourcePairedInclusion.data q hq.le n r).X) ∧
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
                OQ14.RestrictedTEActualCore.fiLin (devCoeff (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h hχ q n) (devData (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi q hq n) (A j))) := by
  have _hτ := hτ0
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    CountedSubspacesVolume.counted_subspaces_at_frequency_volume k hk εp hεp N (2 * η) (2 * δ)
      (by positivity) (by linarith) τ hτ1.le (L / 2) (half_pos hL)
  have hb0 : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hiso := actualScatter_norm_eventually
    (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ R (max R 1)
    hρ hχ.le hb0 (le_max_left R 1) hi q hq
  have hI := PhysicalDeviceFlux.scaled_integrable_eventually
    (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh q hq k hk hR N A h3
  have hL := partner_limitEffective_isUnit
    (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a))
    ρ χ R (max R 1) hρ hχ.le hb0 (le_max_left R 1) hi q hq
  obtain ⟨n, hn⟩ := ((((h7.and hiso).and h8).and hI).and hL).exists
  obtain ⟨⟨⟨⟨hc, hs⟩, hp⟩, hnI⟩, hnL⟩ := hn
  have hCU := SourcePairedReduction.eventually_combined_isUnit q hq.le n
    (deviceCoeff (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ hχ.le q n)
    (deviceData (fun a l => abovePoint (hpoint (-(k * (L / 2))) (ysq N (k * (L / 2))) l) (h * a)) ρ χ R hρ hχ.le hi q hq n)
    (max R 1) hb0 (device_carrier_le _ ρ χ R (max R 1) hρ hχ.le (le_max_left R 1) hi q hq n) hnL
  obtain ⟨r, hr⟩ := (((((hc.and hs).and (Filter.eventually_all.mpr (fun j => hp (A j)))).and
    (h6 n)).and hnI).and hCU).exists
  obtain ⟨⟨⟨⟨⟨hcount, hunit⟩, hid⟩, hdiel⟩, hint⟩, hcombined⟩ := hr
  obtain ⟨hb, hd⟩ := hdiel
  have hphysical := PhysicalPlaneFlux.counted_of_double volume (Dsq (L / 2))
    (Submodule.span ℂ (Set.range A)) _
    (flux k (-(k * (L / 2))) (ysq N (k * (L / 2))) ρ χ h R hρ hχ hi hρh q hq n r)
    τ η δ hint hcount
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, n, r, h1, h2, h3, h4, h5,
    ⟨hb, hd⟩, hunit, hcombined, hphysical, ?_, hid⟩
  intro a ha
  exact ⟨hint a ha, PhysicalPlaneFlux.real_flux_integrable volume _ (hint a ha),
    PhysicalPlaneFlux.absolute_flux_integrable volume _ (hint a ha)⟩

end OQ14.FullChannelDeviceUnit
#print axioms OQ14.FullChannelDeviceUnit.counted_subspaces_physical_unit
