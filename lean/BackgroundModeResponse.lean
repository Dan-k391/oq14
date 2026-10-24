import BackgroundModeMaxwell
import SourceTMPhysicalResponse
import SourceRadiatingTrace

/-! The shells' response to the regular incident mode is the background mode (TM modes).  The scattered
part of the background mode is purely outgoing in the exterior, forced by the shell polarization, locally
square integrable, smooth outside the stack and radiating; hence it is the free volume response of its
polarization, the background mode solves the square-root weighted volume equation of the shell
coefficient with the regular mode as incident datum, and (the volume block being invertible) equals the
actual shell solution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.BackgroundModeResponse
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.MaterialMaxwell OQ14.MagneticResponse
  OQ14.DynamicSource OQ14.ForcedMaxwellResponse OQ14.BackgroundModeMaxwell
  OQ14.SourceRadialSystem OQ14.SourceCoreReaction OQ14.BackgroundCoreTransmission
open scoped ComplexConjugate Topology

/-- Scattered electric field: background minus the regular incident mode of unit amplitude. -/
def scatteredElectric (d : Data) (P : HarmonicPolynomial.Poly) : Field :=
  backgroundElectric d P-SolidMaxwellProfiles.electric d.l P

/-- Scattered magnetic field. -/
def scatteredMagnetic (d : Data) (P : HarmonicPolynomial.Poly) : Field :=
  backgroundMagnetic d P-SolidMaxwellProfiles.magnetic d.l P

theorem scattered_forced (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (P : HarmonicPolynomial.Poly)
    (hp : P.IsHomogeneous d.l) (hh : HarmonicPolynomial.formalLaplacian P=0) :
    TestForced 1 (backgroundPolarization d P) (scatteredElectric d P) (scatteredMagnetic d P) := by
  have hbg := background_forced d hdisp P hp hh
  have hvac := TestFieldLocalization.vacuum_smul 1 1 (SolidMaxwellProfiles.electric d.l P)
    (SolidMaxwellProfiles.magnetic d.l P)
    (MaterialMaxwell.classical_vacuum_testMaxwell 1 _ _
      (fun i => (SolidMaxwellProfiles.electric_smooth d.l P i).of_le (by simp))
      (fun i => (SolidMaxwellProfiles.magnetic_smooth d.l P i).of_le (by simp))
      (SolidMaxwellProfiles.actual_maxwell d.l P hp hh))
  have hρ : ∀ i, LocallyIntegrable (backgroundPolarization d P i) := by
    intro i
    have hc : LocallyIntegrable (fun x => kappa d*(SourceRegularCorrection.polarization d P i x-
        conj (SourceRegularCorrection.polarization d P i x))) := by
      have h0 := (SourceCorrectionLocalBounds.polarization_integrable d P i).locallyIntegrable
      have h1 : LocallyIntegrable (fun x => conj (SourceRegularCorrection.polarization d P i x)) := by
        refine h0.mono (Complex.continuous_conj.comp_aestronglyMeasurable h0.aestronglyMeasurable) ?_
        exact Filter.Eventually.of_forall (fun x => by simp)
      simpa only [smul_eq_mul] using (h0.sub h1).smul (kappa d)
    exact hc
  have hsub := testForced_sub 1 _ _ _ _ _ _ hρ (fun i => locallyIntegrable_zero)
    (backgroundElectric_locallyIntegrable d P) (backgroundMagnetic_locallyIntegrable d P)
    (locallyIntegrable_smul 1 _ (solidE_locallyIntegrable d.l P))
    (locallyIntegrable_smul 1 _ (solidH_locallyIntegrable d.l P)) hbg hvac
  simpa only [scatteredElectric,scatteredMagnetic,one_smul,sub_zero] using hsub

theorem scatteredElectric_locallyIntegrable (d : Data) (P : HarmonicPolynomial.Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => scatteredElectric d P x i) :=
  locallyIntegrable_sub' _ _ (backgroundElectric_locallyIntegrable d P)
    (solidE_locallyIntegrable d.l P) i

theorem scatteredMagnetic_locallyIntegrable (d : Data) (P : HarmonicPolynomial.Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => scatteredMagnetic d P x i) :=
  locallyIntegrable_sub' _ _ (backgroundMagnetic_locallyIntegrable d P)
    (solidH_locallyIntegrable d.l P) i

/-- The scattered part is purely outgoing beyond the stack. -/
theorem scatteredElectric_exterior (d : Data) (P : HarmonicPolynomial.Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : d.X<‖x‖) :
    scatteredElectric d P x=
      ((reflection d.l d.gs d.R d.X d.hR-1)/2*Complex.I) • SourceUnclippedMaxwell.electric (vacuum d) P x := by
  ext i
  have h := congrFun (backgroundElectric_exterior d P hp hh x hx) i
  simp only [scatteredElectric,Pi.sub_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul] at h ⊢
  rw [h]
  ring

theorem scatteredMagnetic_exterior (d : Data) (P : HarmonicPolynomial.Poly) (x : Space) (hx : d.X<‖x‖) :
    scatteredMagnetic d P x=
      ((reflection d.l d.gs d.R d.X d.hR-1)/2*Complex.I) • SourceUnclippedMaxwell.magnetic (vacuum d) P x := by
  ext i
  have h := congrFun (backgroundMagnetic_exterior d P x hx) i
  simp only [scatteredMagnetic,Pi.sub_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul] at h ⊢
  rw [h]
  ring


/-! ### Local square integrability, exterior smoothness and the radiation trace -/

theorem conj_memLp_ball (f : Space → ℂ) (T : ℝ)
    (h : MemLp f 2 (volume.restrict (closedBall 0 T))) :
    MemLp (fun x => conj (f x)) 2 (volume.restrict (closedBall 0 T)) :=
  h.of_le (Complex.continuous_conj.comp_aestronglyMeasurable h.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => by simp))

theorem backgroundElectric_memLp_ball (d : Data) (P : HarmonicPolynomial.Poly) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => backgroundElectric d P x i) 2 (volume.restrict (closedBall 0 T)) := by
  have h1 := SourceCorrectionLocalBounds.electric_memLp_ball d P T i
  have h2 := conj_memLp_ball _ T h1
  have h3 := SourceLocalBounds.continuous_memLp_ball
    (fun x => SolidMaxwellProfiles.electric d.l P x i)
    (SolidMaxwellProfiles.electric_smooth d.l P i).continuous T
  have h := ((h1.sub h2).const_smul (kappa d)).add (h3.const_smul (-2*Complex.I*kappa d))
  exact h

theorem backgroundMagnetic_memLp_ball (d : Data) (P : HarmonicPolynomial.Poly) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => backgroundMagnetic d P x i) 2 (volume.restrict (closedBall 0 T)) := by
  have h1 := SourceCorrectionLocalBounds.magnetic_memLp_ball d P T i
  have h2 := conj_memLp_ball _ T h1
  have h3 := SourceLocalBounds.continuous_memLp_ball
    (fun x => SolidMaxwellProfiles.magnetic d.l P x i)
    (SolidMaxwellProfiles.magnetic_smooth d.l P i).continuous T
  have h := ((h1.add h2).const_smul (kappa d)).add (h3.const_smul (-2*Complex.I*kappa d))
  exact h

theorem scatteredElectric_memLp_ball (d : Data) (P : HarmonicPolynomial.Poly) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => scatteredElectric d P x i) 2 (volume.restrict (closedBall 0 T)) := by
  have h3 := SourceLocalBounds.continuous_memLp_ball
    (fun x => SolidMaxwellProfiles.electric d.l P x i)
    (SolidMaxwellProfiles.electric_smooth d.l P i).continuous T
  exact (backgroundElectric_memLp_ball d P T i).sub h3

theorem scatteredMagnetic_memLp_ball (d : Data) (P : HarmonicPolynomial.Poly) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => scatteredMagnetic d P x i) 2 (volume.restrict (closedBall 0 T)) := by
  have h3 := SourceLocalBounds.continuous_memLp_ball
    (fun x => SolidMaxwellProfiles.magnetic d.l P x i)
    (SolidMaxwellProfiles.magnetic_smooth d.l P i).continuous T
  exact (backgroundMagnetic_memLp_ball d P T i).sub h3

theorem scatteredElectric_smooth (d : Data) (P : HarmonicPolynomial.Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : d.X<‖x‖) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => scatteredElectric d P z i) x := by
  have h1 := SourceExteriorSmooth.correction_electric_smooth d P hp hh x hx i
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => conj (SourceRegularCorrection.electric d P z i)) x :=
    Complex.conjCLE.contDiff.contDiffAt.comp x h1
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => SolidMaxwellProfiles.electric d.l P z i) x :=
    (SolidMaxwellProfiles.electric_smooth d.l P i).contDiffAt
  have hk : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : Space => kappa d) x := contDiffAt_const
  have hl : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : Space => (-2*Complex.I*kappa d)) x := contDiffAt_const
  have h := ((hk.mul (h1.sub h2)).add (hl.mul h3)).sub h3
  exact h

/-- Trace of the scattered part: it is a multiple of the outgoing vacuum mode outside the stack. -/
def scatteredTrace (d : Data) (P : HarmonicPolynomial.Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) :
    RadiatingTrace.Trace 1 (scatteredElectric d P) (scatteredMagnetic d P) :=
  RadiatingTraceTransport.exteriorCongr
    (RadiatingTraceTransport.smul (SourceRadiatingTrace.tm_trace (vacuum d) P hp)
      ((reflection d.l d.gs d.R d.X d.hR-1)/2*Complex.I)) d.X
    (fun x hx => scatteredElectric_exterior d P hp hh x hx)
    (fun x hx => scatteredMagnetic_exterior d P x hx)



/-! ### Volume representation of the scattered part -/

theorem conj_memLp (f : Space → ℂ) (h : MemLp f 2 volume) : MemLp (fun x => conj (f x)) 2 volume :=
  h.of_le (Complex.continuous_conj.comp_aestronglyMeasurable h.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => by simp))

theorem conj_integrable (f : Space → ℂ) (h : Integrable f) : Integrable (fun x => conj (f x)) :=
  h.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable h.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => by simp))

theorem backgroundPolarization_memLp (d : Data) (P : HarmonicPolynomial.Poly) (i : Fin 3) :
    MemLp (backgroundPolarization d P i) 2 volume := by
  have h := SourceCorrectionLocalBounds.polarization_memLp d P i
  have h2 := ((h.sub (conj_memLp _ h)).const_smul (kappa d))
  simpa only [smul_eq_mul] using h2

theorem backgroundPolarization_integrable (d : Data) (P : HarmonicPolynomial.Poly) (i : Fin 3) :
    Integrable (backgroundPolarization d P i) := by
  have h := SourceCorrectionLocalBounds.polarization_integrable d P i
  have h2 := ((h.sub (conj_integrable _ h)).smul (kappa d))
  simpa only [smul_eq_mul] using h2

theorem backgroundPolarization_outer (d : Data) (P : HarmonicPolynomial.Poly) (y : Space)
    (hy : d.X<‖y‖) (i : Fin 3) : backgroundPolarization d P i y=0 := by
  unfold backgroundPolarization
  rw [SourceRegularCorrection.polarization_outer d P y hy i]
  simp

/-- The background polarization as an element of `VectorL2`. -/
def backgroundSource (d : Data) (P : HarmonicPolynomial.Poly) : VectorFourier.VectorL2 :=
  ∑ i : Fin 3,DynamicConvolution.insert i
    ((backgroundPolarization_memLp d P i).toLp (backgroundPolarization d P i))

theorem backgroundSource_coordinate (d : Data) (P : HarmonicPolynomial.Poly) (i : Fin 3) :
    NewtonL2.physicalCoordinate (backgroundSource d P) i=
      (backgroundPolarization_memLp d P i).toLp (backgroundPolarization d P i) := by
  change DynamicConvolution.component i (∑ j : Fin 3,DynamicConvolution.insert j _)=_
  simp only [map_sum,DynamicConvolution.component_insert]
  simp

theorem backgroundSource_actual (d : Data) (P : HarmonicPolynomial.Poly) (i : Fin 3) :
    (NewtonL2.physicalCoordinate (backgroundSource d P) i : Space → ℂ) =ᵐ[volume]
      backgroundPolarization d P i := by
  rw [backgroundSource_coordinate]
  exact (backgroundPolarization_memLp d P i).coeFn_toLp

/-- **Volume representation.**  The scattered part of the background mode is the free volume response of
its polarization. -/
theorem scattered_representation (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (P : HarmonicPolynomial.Poly)
    (hp : P.IsHomogeneous d.l) (hh : HarmonicPolynomial.formalLaplacian P=0) :
    (scatteredElectric d P =ᵐ[volume]
        FieldResponse.electric 1 (backgroundSource d P) (backgroundPolarization d P)) ∧
      (scatteredMagnetic d P =ᵐ[volume] MagneticResponse.magnetic 1 (backgroundPolarization d P)) :=
  RadiatingSourceRepresentation.actual_response 1 (by norm_num) d.X
    (d.hR.le.trans (RadialStack.chain_ordered d.chain)) (backgroundSource d P)
    (backgroundPolarization d P) (backgroundPolarization_integrable d P)
    (fun i y hy => backgroundPolarization_outer d P y
      (by simpa only [mem_closedBall,dist_zero_right,not_le] using hy) i)
    (backgroundSource_actual d P) (scatteredElectric d P) (scatteredMagnetic d P)
    (scatteredElectric_memLp_ball d P) (scatteredMagnetic_memLp_ball d P)
    (scattered_forced d hdisp P hp hh)
    (fun i x hx => scatteredElectric_smooth d P hp hh x hx i) (scatteredTrace d P hp hh)


/-! ### Identification with the abstract shell solution -/

section Material
open OQ14.SourceMaterialCoefficient

/-- Square-root weighted datum of the background electric field. -/
def backgroundDatum (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (P : HarmonicPolynomial.Poly) : VectorFourier.VectorL2 :=
  IncidentLocalization.datum (coefficient d M hM hs) d.X (backgroundElectric d P)
    (SourceWeightedDatum.material_outer _ d (value_complex d M hM hs))
    (fun i => backgroundElectric_memLp_ball d P d.X i)

/-- Square-root weighted datum of the regular incident mode of unit amplitude. -/
def incidentDatum (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (P : HarmonicPolynomial.Poly) : VectorFourier.VectorL2 :=
  IncidentLocalization.datum (coefficient d M hM hs) d.X (SolidMaxwellProfiles.electric d.l P)
    (SourceWeightedDatum.material_outer _ d (value_complex d M hM hs))
    (fun i => SourceLocalBounds.continuous_memLp_ball _
      (SolidMaxwellProfiles.electric_smooth d.l P i).continuous d.X)

theorem backgroundDatum_actual (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (P : HarmonicPolynomial.Poly) (i : Fin 3) :
    (fun x => backgroundDatum d M hM hs P (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt ((coefficient d M hM hs).value (VectorFourier.coordinateMap x)) : ℂ)*
        backgroundElectric d P x i := by
  unfold backgroundDatum
  exact IncidentLocalization.datum_actual _ _ _ _ _ i

theorem incidentDatum_actual (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (P : HarmonicPolynomial.Poly) (i : Fin 3) :
    (fun x => incidentDatum d M hM hs P (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt ((coefficient d M hM hs).value (VectorFourier.coordinateMap x)) : ℂ)*
        SolidMaxwellProfiles.electric d.l P x i := by
  unfold incidentDatum
  exact IncidentLocalization.datum_actual _ _ _ _ _ i

theorem backgroundDatum_source (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (P : HarmonicPolynomial.Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (i : Fin 3) :
    DynamicVolume.source (coefficient d M hM hs) (backgroundDatum d M hM hs P) i=ᵐ[volume]
      backgroundPolarization d P i := by
  have h := MaterialVolumeConverse.source_from_weighted (coefficient d M hM hs)
    (backgroundDatum d M hM hs P) (backgroundElectric d P)
    (fun j => backgroundDatum_actual d M hM hs P j) i
  filter_upwards [h,show ∀ᵐ x : Space, x≠0 from ae_iff.mpr (by simp)] with x hx hx0
  rw [hx,value_complex,backgroundPolarization_eq d P hp hh x hx0 i]

theorem backgroundDatum_sqrtMultiplier (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (P : HarmonicPolynomial.Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) :
    StaticCoefficient.sqrtMultiplier (coefficient d M hM hs) (backgroundDatum d M hM hs P)=
      backgroundSource d P := by
  apply MaterialVolumeConverse.vector_ext
  intro i
  exact (StaticNewton.material_source_ae _ _ i).trans
    ((backgroundDatum_source d M hM hs P hp hh i).trans (backgroundSource_actual d P i).symm)

/-- **The scattered field of the background datum is the scattered part of the background mode.** -/
theorem backgroundDatum_scattered (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (P : HarmonicPolynomial.Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) :
    MaterialField.scattered (coefficient d M hM hs) 1 (backgroundDatum d M hM hs P)=ᵐ[volume]
      scatteredElectric d P := by
  unfold MaterialField.scattered
  rw [backgroundDatum_sqrtMultiplier d M hM hs P hp hh,
    MaterialVolumeConverse.response_source_congr 1 (backgroundSource d P) _ _
      (backgroundDatum_source d M hM hs P hp hh)]
  exact (scattered_representation d hdisp P hp hh).1.symm

/-- The background datum solves the square-root weighted volume equation with the regular incident
datum on the right-hand side. -/
theorem backgroundDatum_volume_equation (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (P : HarmonicPolynomial.Poly)
    (hp : P.IsHomogeneous d.l) (hh : HarmonicPolynomial.formalLaplacian P=0) :
    DynamicVolume.volumeBlock (coefficient d M hM hs) 1 d.X (backgroundDatum d M hM hs P)=
      incidentDatum d M hM hs P := by
  apply MaterialVolumeConverse.volume_equation (coefficient d M hM hs) 1 d.X _ _
    (backgroundElectric d P) (SolidMaxwellProfiles.electric d.l P)
    (SourceWeightedDatum.material_outer _ d (value_complex d M hM hs))
    (fun j => backgroundDatum_actual d M hM hs P j)
    (fun j => incidentDatum_actual d M hM hs P j)
  intro i
  filter_upwards [backgroundDatum_scattered d M hM hs hdisp P hp hh] with x hx
  have := congrFun hx i
  simpa only [scatteredElectric,Pi.sub_apply] using this

/-- **The actual shell solution for the regular incident mode is the background datum.** -/
theorem backgroundDatum_eq_solution (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (P : HarmonicPolynomial.Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) :
    backgroundDatum d M hM hs P=
      MaterialField.solution (coefficient d M hM hs) 1 d.X (incidentDatum d M hM hs P) :=
  MaterialVolumeConverse.inverse_solution _ 1 d.X _ _
    (SourceMaterialPartition.volumeBlock_isUnit d M hM hs 1 (by norm_num))
    (backgroundDatum_volume_equation d M hM hs hdisp P hp hh)

/-- **The shells' actual response to the regular incident mode of degree `l` is the background mode:**
the total field (incident mode plus the field scattered by the actual shell solution) equals the
background electric field almost everywhere.  Inside the core it is `transmission/2` times the incident
mode (`backgroundElectric_core`). -/
theorem total_eq_background (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (P : HarmonicPolynomial.Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) :
    MaterialField.total (coefficient d M hM hs) 1
      (MaterialField.solution (coefficient d M hM hs) 1 d.X (incidentDatum d M hM hs P))
      (SolidMaxwellProfiles.electric d.l P)=ᵐ[volume] backgroundElectric d P := by
  rw [← backgroundDatum_eq_solution d M hM hs hdisp P hp hh]
  filter_upwards [backgroundDatum_scattered d M hM hs hdisp P hp hh] with x hx
  funext i
  have := congrFun hx i
  simp only [MaterialField.total,scatteredElectric,Pi.sub_apply] at this ⊢
  rw [this]
  ring

end Material

end OQ14.BackgroundModeResponse
#print axioms OQ14.BackgroundModeResponse.scattered_forced
#print axioms OQ14.BackgroundModeResponse.scatteredElectric_locallyIntegrable
#print axioms OQ14.BackgroundModeResponse.scatteredMagnetic_locallyIntegrable
#print axioms OQ14.BackgroundModeResponse.scatteredElectric_exterior
#print axioms OQ14.BackgroundModeResponse.scatteredMagnetic_exterior
#print axioms OQ14.BackgroundModeResponse.conj_memLp_ball
#print axioms OQ14.BackgroundModeResponse.backgroundElectric_memLp_ball
#print axioms OQ14.BackgroundModeResponse.backgroundMagnetic_memLp_ball
#print axioms OQ14.BackgroundModeResponse.scatteredElectric_memLp_ball
#print axioms OQ14.BackgroundModeResponse.scatteredMagnetic_memLp_ball
#print axioms OQ14.BackgroundModeResponse.scatteredElectric_smooth
#print axioms OQ14.BackgroundModeResponse.conj_memLp
#print axioms OQ14.BackgroundModeResponse.conj_integrable
#print axioms OQ14.BackgroundModeResponse.backgroundPolarization_memLp
#print axioms OQ14.BackgroundModeResponse.backgroundPolarization_integrable
#print axioms OQ14.BackgroundModeResponse.backgroundPolarization_outer
#print axioms OQ14.BackgroundModeResponse.backgroundSource_coordinate
#print axioms OQ14.BackgroundModeResponse.backgroundSource_actual
#print axioms OQ14.BackgroundModeResponse.scattered_representation
#print axioms OQ14.BackgroundModeResponse.backgroundDatum_actual
#print axioms OQ14.BackgroundModeResponse.incidentDatum_actual
#print axioms OQ14.BackgroundModeResponse.backgroundDatum_source
#print axioms OQ14.BackgroundModeResponse.backgroundDatum_sqrtMultiplier
#print axioms OQ14.BackgroundModeResponse.backgroundDatum_scattered
#print axioms OQ14.BackgroundModeResponse.backgroundDatum_volume_equation
#print axioms OQ14.BackgroundModeResponse.backgroundDatum_eq_solution
#print axioms OQ14.BackgroundModeResponse.total_eq_background
