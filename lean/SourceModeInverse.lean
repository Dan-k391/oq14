import SourceModeDatum

/-! Both polarizations and all angular degrees use one actual material inverse. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceModeInverse
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction
open OQ14.SourceDielectricModes OQ14.SourceModeDatum OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization

theorem tm_inverse (c : Coefficient) (d : Data)
    (hm : ∀ x : Space,(c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.X))
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) :
    MaterialField.solution c 1 d.X (tmIncident c d hc a)=
      SourceWeightedDatum.datum c d.X hc (tmData d (a.1+1)) (representative (a.1+1) a.2) :=
  (SourceMaterialResponse.inverse_solution c (tmData d (a.1+1)) hm hdisp
    (representative (a.1+1) a.2) (representative_homogeneous _ _) (representative_harmonic _ _) hu).symm

theorem te_inverse (c : Coefficient) (d : Data)
    (hm : ∀ x : Space,(c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.X))
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) :
    MaterialField.solution c 1 d.X (teIncident c d hc a)=
      SourceTEWeightedDatum.datum c d.X hc (teData d (a.1+1)) (representative (a.1+1) a.2) := by
  have hmu (x : Space) : (c.value (VectorFourier.coordinateMap x) : ℂ)=
      SourceGeneralMaxwell.mu (teData d (a.1+1)) ‖x‖-1 := by rw [te_mu d hdisp,hm]
  exact (SourceTEMaterialResponse.inverse_solution c (teData d (a.1+1)) hmu (te_sigma d _)
    (representative (a.1+1) a.2) (representative_homogeneous _ _) (representative_harmonic _ _) hu).symm

theorem tm_source (c : Coefficient) (d : Data)
    (hm : ∀ x : Space,(c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.X))
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) (i : Fin 3) :
    DynamicVolume.source c (MaterialField.solution c 1 d.X (tmIncident c d hc a)) i=ᵐ[volume]
      SourceRegularCorrection.polarization (tmData d (a.1+1)) (representative (a.1+1) a.2) i := by
  rw [tm_inverse c d hm hdisp hu hc a]
  exact SourceWeightedDatum.source_actual c (tmData d (a.1+1)) hm (representative (a.1+1) a.2) i

theorem te_source (c : Coefficient) (d : Data)
    (hm : ∀ x : Space,(c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.X))
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) (i : Fin 3) :
    DynamicVolume.source c (MaterialField.solution c 1 d.X (teIncident c d hc a)) i=ᵐ[volume]
      SourceTECorrection.polarization (teData d (a.1+1)) (representative (a.1+1) a.2) i := by
  rw [te_inverse c d hm hdisp hu hc a]
  apply SourceTEWeightedDatum.source_actual c (teData d (a.1+1)) _ (representative (a.1+1) a.2) i
  intro x
  rw [te_mu d hdisp,hm]

theorem tm_core (c : Coefficient) (d : Data)
    (hm : ∀ x : Space,(c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.X))
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) (x : Space) (hx : ‖x‖<d.R) (i : Fin 3) :
    (∑ j : Fin 3, ∫ y : Space, DynamicVolume.source c
      (MaterialField.solution c 1 d.X (tmIncident c d hc a)) j y*DyadicKernel.dyadic 1 (x-y) i j)=
      multiplier (tmData d (a.1+1))*SolidMaxwellProfiles.electric (a.1+1) (representative (a.1+1) a.2) x i := by
  refine Eq.trans ?_ (SourceCoreVolumeIntegral.integral_core (tmData d (a.1+1)) hdisp
    (representative (a.1+1) a.2) (representative_homogeneous _ _) (representative_harmonic _ _) x hx i)
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [tm_source c d hm hdisp hu hc a j] with y hy
  rw [hy]

theorem te_core (c : Coefficient) (d : Data)
    (hm : ∀ x : Space,(c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.X))
    (hc : ∀ x : Space,x∉closedBall 0 d.X → c.value (VectorFourier.coordinateMap x)=0)
    (a : PositiveIndex) (x : Space) (hx : ‖x‖<d.R) (i : Fin 3) :
    (∑ j : Fin 3, ∫ y : Space, DynamicVolume.source c
      (MaterialField.solution c 1 d.X (teIncident c d hc a)) j y*DyadicKernel.dyadic 1 (x-y) i j)=
      multiplier (teData d (a.1+1))*SolidMaxwellProfiles.magnetic (a.1+1) (representative (a.1+1) a.2) x i := by
  refine Eq.trans ?_ (SourceTECoreVolumeIntegral.integral_core (teData d (a.1+1)) (te_sigma d _)
    (representative (a.1+1) a.2) (representative_homogeneous _ _) (representative_harmonic _ _) x hx i)
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [te_source c d hm hdisp hu hc a j] with y hy
  rw [hy]

end OQ14.SourceModeInverse
#print axioms OQ14.SourceModeInverse.tm_inverse
#print axioms OQ14.SourceModeInverse.te_inverse
#print axioms OQ14.SourceModeInverse.tm_source
#print axioms OQ14.SourceModeInverse.te_source
#print axioms OQ14.SourceModeInverse.tm_core
#print axioms OQ14.SourceModeInverse.te_core
