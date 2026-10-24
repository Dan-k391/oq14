import BackgroundModeResponse
import SourceTEMaterialResponse
import RestrictedTEDatumLinear
import RestrictedTEIncoming
import SourceDielectricModes

/-! The shells' response to a regular TE incident mode, and to a finite TE coefficient vector, is the
background mode of the TE stack.  A TE mode of a stack with unit `sigma` is the dual of the transverse
magnetic structure of the same radial state: electric field `backgroundMagnetic`, magnetic field
`-backgroundElectric`.  Bundled radiating pairs are closed under finite linear combinations, which gives
the response to a finite sum of TE modes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.BackgroundModeTE
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.MaterialMaxwell OQ14.MagneticResponse
  OQ14.DynamicSource OQ14.ForcedMaxwellResponse OQ14.BackgroundModeMaxwell OQ14.BackgroundModeResponse
  OQ14.SourceRadialSystem OQ14.SourceCoreReaction OQ14.BackgroundCoreTransmission
open scoped ComplexConjugate Topology

/-! ### Bundled radiating pairs -/

/-- Zero trace. -/
def zeroTrace : RadiatingTrace.Trace 1 (0 : Field) (0 : Field) where
  far := fun _ => 0
  transverse := fun n => by simp [dot]
  sphericalContinuous := Filter.Eventually.of_forall (fun r => ⟨continuous_const,continuous_const⟩)
  bounded := ⟨0,le_rfl,Filter.Eventually.of_forall (fun r n i => by simp)⟩
  electricLimit := fun n => by simp
  magneticLimit := fun n => by
    have h : crossProduct (MaxwellRadiation.direction n) (0 : Vector)=0 := by
      ext i
      fin_cases i <;> simp [cross_apply]
    simp only [h]
    simp

/-- The hypotheses of the radiating volume representation for a field pair with force `ρ`. -/
structure RadiatingPair (R : ℝ) (E H : Field) (ρ : Fin 3 → Space → ℂ) where
  forced : TestForced 1 ρ E H
  locE : ∀ i, LocallyIntegrable (fun x => E x i)
  locH : ∀ i, LocallyIntegrable (fun x => H x i)
  locρ : ∀ i, LocallyIntegrable (ρ i)
  memE : ∀ (T : ℝ) (i : Fin 3), MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T))
  memH : ∀ (T : ℝ) (i : Fin 3), MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T))
  smooth : ∀ (i : Fin 3) (x : Space), R<‖x‖ → ContDiffAt ℝ (⊤ : ℕ∞) (fun z => E z i) x
  trace : RadiatingTrace.Trace 1 E H
  ρint : ∀ j, Integrable (ρ j)
  ρmem : ∀ j, MemLp (ρ j) 2 volume
  ρout : ∀ (j : Fin 3) (y : Space), R<‖y‖ → ρ j y=0

namespace RadiatingPair

def zero (R : ℝ) : RadiatingPair R 0 0 (fun _ _ => 0) where
  forced := fun i f => by simp [curlPair,fieldPair]
  locE := fun i => locallyIntegrable_zero
  locH := fun i => locallyIntegrable_zero
  locρ := fun i => locallyIntegrable_zero
  memE := fun T i => by simp
  memH := fun T i => by simp
  smooth := fun i x _ => contDiffAt_const
  trace := zeroTrace
  ρint := fun j => integrable_zero _ _ _
  ρmem := fun j => MeasureTheory.MemLp.zero
  ρout := fun j y _ => rfl

end RadiatingPair


namespace RadiatingPair

variable {R : ℝ} {E H E' H' : Field} {ρ ρ' : Fin 3 → Space → ℂ}

def smul (c : ℂ) (p : RadiatingPair R E H ρ) : RadiatingPair R (c • E) (c • H) (fun i x => c*ρ i x) where
  forced := testForced_smul 1 c ρ E H p.forced
  locE := fun i => locallyIntegrable_smul c E p.locE i
  locH := fun i => locallyIntegrable_smul c H p.locH i
  locρ := fun i => by simpa only [smul_eq_mul] using (p.locρ i).smul c
  memE := fun T i => by simpa only [Pi.smul_apply,smul_eq_mul] using (p.memE T i).const_smul c
  memH := fun T i => by simpa only [Pi.smul_apply,smul_eq_mul] using (p.memH T i).const_smul c
  smooth := fun i x hx => by
    have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => c*E z i) x :=
      (contDiffAt_const (c := c)).mul (p.smooth i x hx)
    exact h
  trace := RadiatingTraceTransport.smul p.trace c
  ρint := fun j => by simpa only [smul_eq_mul] using (p.ρint j).smul c
  ρmem := fun j => by simpa only [smul_eq_mul] using (p.ρmem j).const_smul c
  ρout := fun j y hy => by simp [p.ρout j y hy]

def add (p : RadiatingPair R E H ρ) (q : RadiatingPair R E' H' ρ') :
    RadiatingPair R (E+E') (H+H') (fun i x => ρ i x+ρ' i x) where
  forced := testForced_add 1 ρ ρ' E H E' H' p.locρ q.locρ p.locE p.locH q.locE q.locH p.forced q.forced
  locE := fun i => locallyIntegrable_add E E' p.locE q.locE i
  locH := fun i => locallyIntegrable_add H H' p.locH q.locH i
  locρ := fun i => (p.locρ i).add (q.locρ i)
  memE := fun T i => (p.memE T i).add (q.memE T i)
  memH := fun T i => (p.memH T i).add (q.memH T i)
  smooth := fun i x hx => (p.smooth i x hx).add (q.smooth i x hx)
  trace := RadiatingTraceTransport.add p.trace q.trace
  ρint := fun j => (p.ρint j).add (q.ρint j)
  ρmem := fun j => (p.ρmem j).add (q.ρmem j)
  ρout := fun j y hy => by simp [p.ρout j y hy,q.ρout j y hy]

/-- The force of a radiating pair as an element of `VectorL2`. -/
def source (p : RadiatingPair R E H ρ) : VectorFourier.VectorL2 :=
  ∑ i : Fin 3,DynamicConvolution.insert i ((p.ρmem i).toLp (ρ i))

theorem source_coordinate (p : RadiatingPair R E H ρ) (i : Fin 3) :
    NewtonL2.physicalCoordinate p.source i=(p.ρmem i).toLp (ρ i) := by
  change DynamicConvolution.component i (∑ j : Fin 3,DynamicConvolution.insert j _)=_
  simp only [map_sum,DynamicConvolution.component_insert]
  simp

theorem source_actual (p : RadiatingPair R E H ρ) (i : Fin 3) :
    (NewtonL2.physicalCoordinate p.source i : Space → ℂ) =ᵐ[volume] ρ i := by
  rw [source_coordinate]
  exact (p.ρmem i).coeFn_toLp

/-- **Volume representation of a radiating pair.** -/
theorem representation (hR : 0≤R) (p : RadiatingPair R E H ρ) :
    (E =ᵐ[volume] FieldResponse.electric 1 p.source ρ) ∧
      (H =ᵐ[volume] MagneticResponse.magnetic 1 ρ) :=
  RadiatingSourceRepresentation.actual_response 1 (by norm_num) R hR p.source ρ p.ρint
    (fun i y hy => p.ρout i y (by simpa only [mem_closedBall,dist_zero_right,not_le] using hy))
    p.source_actual E H p.memE p.memH p.forced p.smooth p.trace

end RadiatingPair

theorem sum_nonempty {ι : Type*} [DecidableEq ι] (R : ℝ) (s : Finset ι) (c : ι → ℂ) (E H : ι → Field)
    (ρ : ι → Fin 3 → Space → ℂ) (p : ∀ q, Nonempty (RadiatingPair R (E q) (H q) (ρ q))) :
    Nonempty (RadiatingPair R (∑ q ∈ s,c q • E q) (∑ q ∈ s,c q • H q)
      (fun i x => ∑ q ∈ s,c q*ρ q i x)) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨RadiatingPair.zero R⟩
  | insert a s ha ih =>
    obtain ⟨ih'⟩ := ih
    obtain ⟨pa⟩ := p a
    have e1 : (∑ q ∈ insert a s,c q • E q)=c a • E a+∑ q ∈ s,c q • E q := Finset.sum_insert ha
    have e2 : (∑ q ∈ insert a s,c q • H q)=c a • H a+∑ q ∈ s,c q • H q := Finset.sum_insert ha
    have e3 : (fun i x => ∑ q ∈ insert a s,c q*ρ q i x)=
        fun i x => c a*ρ a i x+∑ q ∈ s,c q*ρ q i x := by
      funext i x
      exact Finset.sum_insert ha
    rw [e1,e2,e3]
    exact ⟨(pa.smul (c a)).add ih'⟩


theorem testForced_fields_congr {k : ℝ} {ρ : Fin 3 → Space → ℂ} {E H E' H' : Field}
    (h : TestForced k ρ E H) (hE : ∀ x i, E x i=E' x i) (hH : ∀ x i, H x i=H' x i) :
    TestForced k ρ E' H' := by
  have e : E=E' := funext (fun x => funext (hE x))
  have f : H=H' := funext (fun x => funext (hH x))
  rw [← e,← f]
  exact h

/-! ### One TE mode of a stack with unit `sigma` -/

section TEMode
open OQ14.HarmonicPolynomial

theorem locallyIntegrable_conj_fun (f : Space → ℂ) (h : LocallyIntegrable f) :
    LocallyIntegrable (fun x => conj (f x)) := by
  refine h.mono (Complex.continuous_conj.comp_aestronglyMeasurable h.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun x => by simp)

/-- Force of the TE background pair. -/
def teBackgroundPolarization (d : Data) (P : Poly) (i : Fin 3) (x : Space) : ℂ :=
  kappa d*(SourceTECorrection.polarization d P i x+conj (SourceTECorrection.polarization d P i x))

theorem teVacuumPair (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (c : ℂ) :
    TestForced 1 (fun _ _ => 0) (c • SolidMaxwellProfiles.magnetic d.l P)
      (c • (-(SolidMaxwellProfiles.electric d.l P))) :=
  TestFieldLocalization.vacuum_smul c 1 _ _
    (SourceTECorrection.vacuum_dual 1 _ _
      (MaterialMaxwell.classical_vacuum_testMaxwell 1 _ _
        (fun i => (SolidMaxwellProfiles.electric_smooth d.l P i).of_le (by simp))
        (fun i => (SolidMaxwellProfiles.magnetic_smooth d.l P i).of_le (by simp))
        (SolidMaxwellProfiles.actual_maxwell d.l P hp hh)))

theorem teBackgroundPolarization_loc (d : Data) (P : Poly) (i : Fin 3) :
    LocallyIntegrable (teBackgroundPolarization d P i) := by
  have h0 := (SourceMuBounds.polarization_integrable d P i).locallyIntegrable
  have h := (h0.add (locallyIntegrable_conj_fun _ h0)).smul (kappa d)
  simpa only [smul_eq_mul] using h

theorem te_background_forced (d : Data) (hσ : ∀ g∈d.gs,g.σ=1) (P : Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) :
    TestForced 1 (teBackgroundPolarization d P) (backgroundMagnetic d P)
      (-(backgroundElectric d P)) := by
  have hc := SourceTEGlobal.forced_maxwell d hσ P hp hh
  have hcc := testForced_conj 1 _ _ _ hc
  have hρ : ∀ i, LocallyIntegrable (SourceTECorrection.polarization d P i) :=
    fun i => (SourceMuBounds.polarization_integrable d P i).locallyIntegrable
  have hρc : ∀ i, LocallyIntegrable (fun x => conj (SourceTECorrection.polarization d P i x)) :=
    fun i => locallyIntegrable_conj_fun _ (hρ i)
  have hE := SourceMuBounds.electric_locallyIntegrable d P
  have hH := SourceMuBounds.magnetic_locallyIntegrable d P
  have hsum := testForced_add 1 _ _ _ _ _ _ hρ hρc hE hH (locallyIntegrable_conj _ hE)
    (locallyIntegrable_negConj _ hH) hc hcc
  have hsm := testForced_smul 1 (kappa d) _ _ _ hsum
  have hvac := teVacuumPair d P hp hh (-2*Complex.I*kappa d)
  have hE1 : ∀ i, LocallyIntegrable (fun x => (SourceTECorrection.electric d P+
      BackgroundModeMaxwell.conjField (SourceTECorrection.electric d P)) x i) :=
    fun i => locallyIntegrable_add _ _ hE (locallyIntegrable_conj _ hE) i
  have hH1 : ∀ i, LocallyIntegrable (fun x => (SourceTECorrection.magnetic d P+
      negConjField (SourceTECorrection.magnetic d P)) x i) :=
    fun i => locallyIntegrable_add _ _ hH (locallyIntegrable_negConj _ hH) i
  have hρk : ∀ i, LocallyIntegrable (fun x => kappa d*(SourceTECorrection.polarization d P i x+
      conj (SourceTECorrection.polarization d P i x))) := teBackgroundPolarization_loc d P
  have hadd := testForced_add 1 _ _ _ _ _ _ hρk (fun i => locallyIntegrable_zero)
    (locallyIntegrable_smul _ _ hE1) (locallyIntegrable_smul _ _ hH1)
    (locallyIntegrable_smul _ _ (solidH_locallyIntegrable d.l P))
    (locallyIntegrable_smul _ _ (fun i => (solidE_locallyIntegrable d.l P i).neg)) hsm hvac
  refine testForced_fields_congr
    (testForced_congr_rho 1 _ (teBackgroundPolarization d P) _ _
      (fun i => Filter.Eventually.of_forall (fun x => by simp [teBackgroundPolarization])) hadd) ?_ ?_
  · intro x i
    simp [backgroundMagnetic,SourceTECorrection.electric]
  · intro x i
    simp [SourceTECorrection.magnetic,backgroundElectric,negConjField,BackgroundModeMaxwell.conjField]
    ring

end TEMode


section TEPair
open OQ14.HarmonicPolynomial

theorem scatteredMagnetic_smooth (d : Data) (P : Poly) (x : Space) (hx : d.X<‖x‖) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => scatteredMagnetic d P z i) x := by
  have h1 := SourceExteriorSmooth.correction_magnetic_smooth d P x hx i
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => conj (SourceRegularCorrection.magnetic d P z i)) x :=
    Complex.conjCLE.contDiff.contDiffAt.comp x h1
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => SolidMaxwellProfiles.magnetic d.l P z i) x :=
    (SolidMaxwellProfiles.magnetic_smooth d.l P i).contDiffAt
  have hk : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : Space => kappa d) x := contDiffAt_const
  have hl : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : Space => (-2*Complex.I*kappa d)) x := contDiffAt_const
  have h := ((hk.mul (h1.add h2)).add (hl.mul h3)).sub h3
  exact h

theorem conj_select_mu (gs : List RadialStack.Layer) (r : ℝ) :
    conj (ClippedLayerProfiles.select gs (fun g _ => ((g.q^2/g.σ : ℝ) : ℂ)) (fun _ => 0) r)=
      ClippedLayerProfiles.select gs (fun g _ => ((g.q^2/g.σ : ℝ) : ℂ)) (fun _ => 0) r := by
  induction gs with
  | nil => simp [ClippedLayerProfiles.select]
  | cons g gs ih =>
    simp only [ClippedLayerProfiles.select] at ih ⊢
    split_ifs
    · simp
    · exact ih

theorem conj_mu (d : Data) (r : ℝ) : conj (SourceGeneralMaxwell.mu d r)=SourceGeneralMaxwell.mu d r := by
  unfold SourceGeneralMaxwell.mu SourceRadialSystem.extend
  split_ifs
  · simp
  · exact conj_select_mu d.gs r
  · simp

theorem teBackgroundPolarization_eq (d : Data) (P : Poly) (x : Space) (hx : x≠0) (i : Fin 3) :
    teBackgroundPolarization d P i x=(SourceGeneralMaxwell.mu d ‖x‖-1)*backgroundMagnetic d P x i := by
  rw [backgroundMagnetic_eq d P x hx i]
  unfold teBackgroundPolarization SourceTECorrection.polarization
  rw [map_mul,map_sub,conj_mu,map_one]
  ring

end TEPair


section TEFamily
open OQ14.HarmonicPolynomial

/-- The TE scattered part of one mode as a radiating pair. -/
def tePair (d : Data) (hσ : ∀ g∈d.gs,g.σ=1) (P : Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) :
    RadiatingPair d.X (scatteredMagnetic d P) (-(scatteredElectric d P)) (teBackgroundPolarization d P) where
  forced := by
    have hbg := te_background_forced d hσ P hp hh
    have hvac := teVacuumPair d P hp hh 1
    have hsub := testForced_sub 1 (teBackgroundPolarization d P) (fun _ _ => 0) _ _ _ _
      (teBackgroundPolarization_loc d P) (fun i => locallyIntegrable_zero)
      (backgroundMagnetic_locallyIntegrable d P)
      (fun i => (backgroundElectric_locallyIntegrable d P i).neg)
      (locallyIntegrable_smul 1 _ (solidH_locallyIntegrable d.l P))
      (locallyIntegrable_smul 1 _ (fun i => (solidE_locallyIntegrable d.l P i).neg)) hbg hvac
    refine testForced_fields_congr (testForced_congr_rho 1 _ (teBackgroundPolarization d P) _ _
      (fun i => Filter.Eventually.of_forall (fun x => by simp)) hsub) ?_ ?_
    · intro x i
      simp [scatteredMagnetic]
    · intro x i
      simp [scatteredElectric]
      ring
  locE := scatteredMagnetic_locallyIntegrable d P
  locH := fun i => (scatteredElectric_locallyIntegrable d P i).neg
  locρ := teBackgroundPolarization_loc d P
  memE := scatteredMagnetic_memLp_ball d P
  memH := fun T i => (scatteredElectric_memLp_ball d P T i).neg
  smooth := fun i x hx => scatteredMagnetic_smooth d P x hx i
  trace := SourceRadiatingTrace.dual_trace (scatteredTrace d P hp hh)
  ρint := fun j => by
    have h := SourceMuBounds.polarization_integrable d P j
    have h2 := (h.add (conj_integrable _ h)).smul (kappa d)
    simpa only [smul_eq_mul] using h2
  ρmem := fun j => by
    have h := SourceMuBounds.polarization_memLp d P j
    have h2 := (h.add (conj_memLp _ h)).const_smul (kappa d)
    simpa only [smul_eq_mul] using h2
  ρout := fun j y hy => by
    simp [teBackgroundPolarization,SourceTECorrection.polarization_outer d P y hy j]

end TEFamily


section TEMaterial
open OQ14.HarmonicPolynomial

variable {ι : Type*}

/-- TE background electric field of a finite family of modes over a common stack. -/
def famBackground (d0 : Data) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) : Field :=
  ∑ q ∈ s,c q • backgroundMagnetic { d0 with l := lq q } (P q)

/-- The corresponding incident TE electric field. -/
def famIncident (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) : Field :=
  ∑ q ∈ s,c q • SolidMaxwellProfiles.magnetic (lq q) (P q)

/-- The force of the family. -/
def famForce (d0 : Data) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly)
    (i : Fin 3) (x : Space) : ℂ :=
  ∑ q ∈ s,c q*teBackgroundPolarization { d0 with l := lq q } (P q) i x

theorem famBackground_apply (d0 : Data) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly)
    (x : Space) (i : Fin 3) :
    famBackground d0 s c lq P x i=∑ q ∈ s,c q*backgroundMagnetic { d0 with l := lq q } (P q) x i := by
  simp [famBackground,Finset.sum_apply]

theorem famIncident_apply (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) (x : Space) (i : Fin 3) :
    famIncident s c lq P x i=∑ q ∈ s,c q*SolidMaxwellProfiles.magnetic (lq q) (P q) x i := by
  simp [famIncident,Finset.sum_apply]

theorem famBackground_memLp (d0 : Data) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly)
    (T : ℝ) (i : Fin 3) :
    MemLp (fun x => famBackground d0 s c lq P x i) 2 (volume.restrict (closedBall 0 T)) := by
  have h := MeasureTheory.memLp_finset_sum (p := 2) s (f := fun q x =>
    c q*backgroundMagnetic { d0 with l := lq q } (P q) x i) (fun q _ => by
      simpa only [smul_eq_mul] using
        (backgroundMagnetic_memLp_ball { d0 with l := lq q } (P q) T i).const_smul (c q))
  have e : (fun x => famBackground d0 s c lq P x i)=
      fun x => ∑ q ∈ s,c q*backgroundMagnetic { d0 with l := lq q } (P q) x i := by
    funext x
    exact famBackground_apply d0 s c lq P x i
  rw [e]
  exact h

theorem famIncident_continuous (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) (i : Fin 3) :
    Continuous (fun x => famIncident s c lq P x i) := by
  have e : (fun x => famIncident s c lq P x i)=
      fun x => ∑ q ∈ s,c q*SolidMaxwellProfiles.magnetic (lq q) (P q) x i := by
    funext x
    exact famIncident_apply s c lq P x i
  rw [e]
  exact continuous_finset_sum _ (fun q _ =>
    continuous_const.mul (SolidMaxwellProfiles.magnetic_smooth (lq q) (P q) i).continuous)

theorem famForce_eq (d0 : Data) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly)
    (x : Space) (hx : x≠0) (i : Fin 3) :
    famForce d0 s c lq P i x=(SourceGeneralMaxwell.mu d0 ‖x‖-1)*famBackground d0 s c lq P x i := by
  rw [famBackground_apply,Finset.mul_sum]
  unfold famForce
  apply Finset.sum_congr rfl
  intro q _
  rw [teBackgroundPolarization_eq { d0 with l := lq q } (P q) x hx i]
  change c q*((SourceGeneralMaxwell.mu d0 ‖x‖-1)*_)=_
  ring

theorem famPair_nonempty [DecidableEq ι] (d0 : Data) (hσ : ∀ g∈d0.gs,g.σ=1) (s : Finset ι)
    (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) (hp : ∀ q, (P q).IsHomogeneous (lq q))
    (hh : ∀ q, HarmonicPolynomial.formalLaplacian (P q)=0) :
    Nonempty (RadiatingPair d0.X
      (∑ q ∈ s,c q • scatteredMagnetic { d0 with l := lq q } (P q))
      (∑ q ∈ s,c q • (-(scatteredElectric { d0 with l := lq q } (P q))))
      (fun i x => ∑ q ∈ s,c q*teBackgroundPolarization { d0 with l := lq q } (P q) i x)) :=
  sum_nonempty d0.X s c _ _ _ (fun q => ⟨tePair { d0 with l := lq q } hσ (P q) (hp q) (hh q)⟩)

/-- Weighted datum of the family background field. -/
def famBackgroundDatum (d0 : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d0.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M)
    (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) : VectorFourier.VectorL2 :=
  IncidentLocalization.datum (SourceMuMaterial.coefficient d0 M hM hs) d0.X (famBackground d0 s c lq P)
    (SourceTEWeightedDatum.material_outer _ d0 (SourceMuMaterial.value_complex d0 M hM hs))
    (fun i => famBackground_memLp d0 s c lq P d0.X i)

/-- Weighted datum of the family incident field. -/
def famIncidentDatum (d0 : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d0.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M)
    (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ) (P : ι → Poly) : VectorFourier.VectorL2 :=
  IncidentLocalization.datum (SourceMuMaterial.coefficient d0 M hM hs) d0.X (famIncident s c lq P)
    (SourceTEWeightedDatum.material_outer _ d0 (SourceMuMaterial.value_complex d0 M hM hs))
    (fun i => SourceLocalBounds.continuous_memLp_ball _ (famIncident_continuous s c lq P i) d0.X)

theorem famBackgroundDatum_actual (d0 : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d0.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ)
    (P : ι → Poly) (i : Fin 3) :
    (fun x => famBackgroundDatum d0 M hM hs s c lq P (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt ((SourceMuMaterial.coefficient d0 M hM hs).value
        (VectorFourier.coordinateMap x)) : ℂ)*famBackground d0 s c lq P x i := by
  unfold famBackgroundDatum
  exact IncidentLocalization.datum_actual _ _ _ _ _ i

theorem famIncidentDatum_actual (d0 : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d0.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ)
    (P : ι → Poly) (i : Fin 3) :
    (fun x => famIncidentDatum d0 M hM hs s c lq P (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt ((SourceMuMaterial.coefficient d0 M hM hs).value
        (VectorFourier.coordinateMap x)) : ℂ)*famIncident s c lq P x i := by
  unfold famIncidentDatum
  exact IncidentLocalization.datum_actual _ _ _ _ _ i

theorem famBackgroundDatum_source (d0 : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d0.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (s : Finset ι) (c : ι → ℂ) (lq : ι → ℕ)
    (P : ι → Poly) (i : Fin 3) :
    DynamicVolume.source (SourceMuMaterial.coefficient d0 M hM hs)
      (famBackgroundDatum d0 M hM hs s c lq P) i=ᵐ[volume] famForce d0 s c lq P i := by
  have h := MaterialVolumeConverse.source_from_weighted (SourceMuMaterial.coefficient d0 M hM hs)
    (famBackgroundDatum d0 M hM hs s c lq P) (famBackground d0 s c lq P)
    (fun j => famBackgroundDatum_actual d0 M hM hs s c lq P j) i
  filter_upwards [h,show ∀ᵐ x : Space, x≠0 from ae_iff.mpr (by simp)] with x hx hx0
  rw [hx,SourceMuMaterial.value_complex,famForce_eq d0 s c lq P x hx0 i]

/-- **Volume equation for a finite family of TE modes.** -/
theorem te_family_volume_equation [DecidableEq ι] (d0 : Data) (hσ : ∀ g∈d0.gs,g.σ=1) (M : ℝ)
    (hM : 1≤M) (hs : ∀ g∈d0.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (s : Finset ι) (c : ι → ℂ)
    (lq : ι → ℕ) (P : ι → Poly) (hp : ∀ q, (P q).IsHomogeneous (lq q))
    (hh : ∀ q, HarmonicPolynomial.formalLaplacian (P q)=0) :
    DynamicVolume.volumeBlock (SourceMuMaterial.coefficient d0 M hM hs) 1 d0.X
      (famBackgroundDatum d0 M hM hs s c lq P)=famIncidentDatum d0 M hM hs s c lq P := by
  obtain ⟨pA⟩ := famPair_nonempty d0 hσ s c lq P hp hh
  have hrep := pA.representation (d0.hR.le.trans (RadialStack.chain_ordered d0.chain))
  have hsq : StaticCoefficient.sqrtMultiplier (SourceMuMaterial.coefficient d0 M hM hs)
      (famBackgroundDatum d0 M hM hs s c lq P)=pA.source := by
    apply MaterialVolumeConverse.vector_ext
    intro i
    exact (StaticNewton.material_source_ae _ _ i).trans
      ((famBackgroundDatum_source d0 M hM hs s c lq P i).trans (pA.source_actual i).symm)
  have hsc : MaterialField.scattered (SourceMuMaterial.coefficient d0 M hM hs) 1
      (famBackgroundDatum d0 M hM hs s c lq P)=ᵐ[volume]
      ∑ q ∈ s,c q • scatteredMagnetic { d0 with l := lq q } (P q) := by
    unfold MaterialField.scattered
    rw [hsq,MaterialVolumeConverse.response_source_congr 1 pA.source _ _
      (famBackgroundDatum_source d0 M hM hs s c lq P)]
    exact hrep.1.symm
  apply MaterialVolumeConverse.volume_equation (SourceMuMaterial.coefficient d0 M hM hs) 1 d0.X _ _
    (famBackground d0 s c lq P) (famIncident s c lq P)
    (SourceTEWeightedDatum.material_outer _ d0 (SourceMuMaterial.value_complex d0 M hM hs))
    (fun j => famBackgroundDatum_actual d0 M hM hs s c lq P j)
    (fun j => famIncidentDatum_actual d0 M hM hs s c lq P j)
  intro i
  filter_upwards [hsc] with x hx
  have h := congrFun hx i
  rw [h]
  simp only [famBackground_apply,famIncident_apply,scatteredMagnetic,Finset.sum_apply,Pi.smul_apply,
    Pi.sub_apply,smul_eq_mul,← Finset.sum_sub_distrib,mul_sub]

/-- **The actual shell solution for a finite family of regular TE modes is the family background datum.** -/
theorem te_family_solution [DecidableEq ι] (d0 : Data) (hσ : ∀ g∈d0.gs,g.σ=1) (M : ℝ)
    (hM : 1≤M) (hs : ∀ g∈d0.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (s : Finset ι) (c : ι → ℂ)
    (lq : ι → ℕ) (P : ι → Poly) (hp : ∀ q, (P q).IsHomogeneous (lq q))
    (hh : ∀ q, HarmonicPolynomial.formalLaplacian (P q)=0) :
    famBackgroundDatum d0 M hM hs s c lq P=
      MaterialField.solution (SourceMuMaterial.coefficient d0 M hM hs) 1 d0.X
        (famIncidentDatum d0 M hM hs s c lq P) :=
  MaterialVolumeConverse.inverse_solution _ 1 d0.X _ _
    (SourceMuMaterial.volumeBlock_isUnit d0 M hM hs 1 (by norm_num))
    (te_family_volume_equation d0 hσ M hM hs s c lq P hp hh)

/-- **Total field.**  The incident family field plus the field scattered by the actual shell solution is
the background family field. -/
theorem te_family_total [DecidableEq ι] (d0 : Data) (hσ : ∀ g∈d0.gs,g.σ=1) (M : ℝ)
    (hM : 1≤M) (hs : ∀ g∈d0.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (s : Finset ι) (c : ι → ℂ)
    (lq : ι → ℕ) (P : ι → Poly) (hp : ∀ q, (P q).IsHomogeneous (lq q))
    (hh : ∀ q, HarmonicPolynomial.formalLaplacian (P q)=0) :
    MaterialField.total (SourceMuMaterial.coefficient d0 M hM hs) 1
      (MaterialField.solution (SourceMuMaterial.coefficient d0 M hM hs) 1 d0.X
        (famIncidentDatum d0 M hM hs s c lq P)) (famIncident s c lq P)=ᵐ[volume]
      famBackground d0 s c lq P := by
  rw [← te_family_solution d0 hσ M hM hs s c lq P hp hh]
  obtain ⟨pA⟩ := famPair_nonempty d0 hσ s c lq P hp hh
  have hrep := pA.representation (d0.hR.le.trans (RadialStack.chain_ordered d0.chain))
  have hsq : StaticCoefficient.sqrtMultiplier (SourceMuMaterial.coefficient d0 M hM hs)
      (famBackgroundDatum d0 M hM hs s c lq P)=pA.source := by
    apply MaterialVolumeConverse.vector_ext
    intro i
    exact (StaticNewton.material_source_ae _ _ i).trans
      ((famBackgroundDatum_source d0 M hM hs s c lq P i).trans (pA.source_actual i).symm)
  have hsc : MaterialField.scattered (SourceMuMaterial.coefficient d0 M hM hs) 1
      (famBackgroundDatum d0 M hM hs s c lq P)=ᵐ[volume]
      ∑ q ∈ s,c q • scatteredMagnetic { d0 with l := lq q } (P q) := by
    unfold MaterialField.scattered
    rw [hsq,MaterialVolumeConverse.response_source_congr 1 pA.source _ _
      (famBackgroundDatum_source d0 M hM hs s c lq P)]
    exact hrep.1.symm
  filter_upwards [hsc] with x hx
  funext i
  have h := congrFun hx i
  simp only [MaterialField.total]
  rw [h]
  simp only [famBackground_apply,famIncident_apply,scatteredMagnetic,Finset.sum_apply,Pi.smul_apply,
    Pi.sub_apply,smul_eq_mul,mul_sub,Finset.sum_sub_distrib]
  ring

end TEMaterial


/-! ### Finite TE coefficient vectors -/

section TEFinite
open OQ14.HarmonicPolynomial

/-- TE regular mode amplitude: `electric (single q 1) = teCoeff (single q 1) q * (magnetic mode)`. -/
def teCoeff (A : SymmetricHarmonicJets.Index →₀ ℂ) (q : SymmetricHarmonicJets.Index) : ℂ :=
  RestrictedTEIncoming.coefficient A q*Complex.I

theorem polynomial_homogeneous (q : SymmetricHarmonicJets.Index) :
    (RestrictedTEIncoming.polynomial q).IsHomogeneous q.val.1 :=
  EvenHarmonicProjection.homogeneous q.val.2 q.val.1 q.property.1

theorem polynomial_harmonic (q : SymmetricHarmonicJets.Index) :
    HarmonicPolynomial.formalLaplacian (RestrictedTEIncoming.polynomial q)=0 :=
  EvenHarmonicProjection.harmonic q.val.2 q.val.1 q.property.2

theorem teElectric_wave (l : ℕ) (P : Poly) (x : Space) (i : Fin 3) :
    DebyeMaxwell.teElectric (SolidScalarHelmholtz.wave l 1 P) x i=
      Complex.I*SolidMaxwellProfiles.magnetic l P x i := by
  change OQ14.DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l 1 P) x i=
    Complex.I*(-Complex.I*1*1*OQ14.DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l 1 P) x i)
  linear_combination (OQ14.DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l 1 P) x i)*Complex.I_mul_I

/-- The regular TE incident field of a finite coefficient vector as a family of regular modes. -/
theorem electric_eq_famIncident (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    RestrictedTEPlaneLocal.electric A=
      famIncident A.support (teCoeff A) (fun q => q.val.1) RestrictedTEIncoming.polynomial := by
  funext x i
  rw [famIncident_apply]
  change DebyeMaxwell.teElectric (RestrictedTEFields.potential 1 A) x i=_
  rw [RestrictedTEIncoming.electric_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [teElectric_wave]
  unfold teCoeff
  ring

theorem electric_scaledCoeff_eq (A : SymmetricHarmonicJets.Index →₀ ℂ) (τ : ℕ → ℂ) :
    RestrictedTEPlaneLocal.electric (scaledCoeff A τ)=
      famIncident A.support (teCoeff (scaledCoeff A τ)) (fun q => q.val.1)
        RestrictedTEIncoming.polynomial := by
  rw [electric_eq_famIncident]
  funext x i
  rw [famIncident_apply,famIncident_apply]
  apply Finset.sum_subset (scaledCoeff_support A τ)
  intro q _ hq
  have h : (scaledCoeff A τ) q=0 := Finsupp.not_mem_support_iff.mp hq
  simp [teCoeff,RestrictedTEIncoming.coefficient,h]

theorem teCoeff_scaledCoeff (A : SymmetricHarmonicJets.Index →₀ ℂ) (τ : ℕ → ℂ)
    (q : SymmetricHarmonicJets.Index) : teCoeff (scaledCoeff A τ) q=teCoeff A q*τ q.val.1 := by
  unfold teCoeff RestrictedTEIncoming.coefficient
  rw [scaledCoeff_apply]
  ring

/-- Support datum of the shell coefficient on the closed ball of radius `X`. -/
def teSupportData (cs : StaticCoefficient.Coefficient) (X : ℝ)
    (hc : ∀ x : Space,x∉closedBall 0 X → cs.value (VectorFourier.coordinateMap x)=0) :
    BoundedMaterialKernel.SupportData cs where
  radius := X
  carrier := closedBall 0 X
  measurable := measurableSet_closedBall
  finite := (isCompact_closedBall (0 : Space) X).measure_lt_top.ne
  ballZero := hc
  carrierZero := hc

end TEFinite


section TEResponse
open OQ14.HarmonicPolynomial

/-- The incident datum of the family equals the restricted-TE datum of the coefficient vector. -/
theorem te_finite_datum (d0 : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d0.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    famIncidentDatum d0 M hM hs A.support (teCoeff A) (fun q => q.val.1) RestrictedTEIncoming.polynomial=
      RestrictedTEMaterial.datum (SourceMuMaterial.coefficient d0 M hM hs)
        (teSupportData _ d0.X (SourceTEWeightedDatum.material_outer _ d0
          (SourceMuMaterial.value_complex d0 M hM hs))) A := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  filter_upwards [famIncidentDatum_actual d0 M hM hs A.support (teCoeff A) (fun q => q.val.1)
    RestrictedTEIncoming.polynomial i,
    RestrictedTEMaterial.datum_actual (SourceMuMaterial.coefficient d0 M hM hs)
      (teSupportData _ d0.X (SourceTEWeightedDatum.material_outer _ d0
        (SourceMuMaterial.value_complex d0 M hM hs))) A i] with x h1 h2
  rw [h1,h2,← congrFun (congrFun (electric_eq_famIncident A) x) i]

/-- **Response of the shells to a finite TE coefficient vector.**  The incident field is
`RestrictedTEPlaneLocal.electric A`, the actual shell solution is the inverse of the volume block applied to
the restricted-TE datum, and the resulting total field is the TE background field of the family of regular
modes `teCoeff A q * magnetic mode (q.val.1, polynomial q)`. -/
theorem te_finite_response (d0 : Data) (hσ : ∀ g∈d0.gs,g.σ=1) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d0.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    MaterialField.total (SourceMuMaterial.coefficient d0 M hM hs) 1
      (MaterialField.solution (SourceMuMaterial.coefficient d0 M hM hs) 1 d0.X
        (RestrictedTEMaterial.datum (SourceMuMaterial.coefficient d0 M hM hs)
          (teSupportData _ d0.X (SourceTEWeightedDatum.material_outer _ d0
            (SourceMuMaterial.value_complex d0 M hM hs))) A))
      (RestrictedTEPlaneLocal.electric A)=ᵐ[volume]
      famBackground d0 A.support (teCoeff A) (fun q => q.val.1) RestrictedTEIncoming.polynomial := by
  classical
  rw [← te_finite_datum,electric_eq_famIncident]
  exact te_family_total d0 hσ M hM hs A.support (teCoeff A) (fun q => q.val.1)
    RestrictedTEIncoming.polynomial (fun q => polynomial_homogeneous q) (fun q => polynomial_harmonic q)

/-- **Core field.**  In the core the TE background field of the family is the regular TE field of the
coefficient vector rescaled degreewise by `transmission/2`. -/
theorem te_finite_core (d0 : Data) (A : SymmetricHarmonicJets.Index →₀ ℂ) (x : Space) (hx : x≠0)
    (hR : ‖x‖≤d0.R) :
    famBackground d0 A.support (teCoeff A) (fun q => q.val.1) RestrictedTEIncoming.polynomial x=
      RestrictedTEPlaneLocal.electric
        (scaledCoeff A (fun l => transmission l d0.gs d0.R d0.X d0.hR/2)) x := by
  funext i
  rw [electric_scaledCoeff_eq,famBackground_apply,famIncident_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [teCoeff_scaledCoeff]
  have h := congrFun (backgroundMagnetic_core { d0 with l := q.val.1 } (RestrictedTEIncoming.polynomial q) x hx hR) i
  simp only [Pi.smul_apply,smul_eq_mul] at h
  rw [h]
  ring

end TEResponse


section Physical
open OQ14.HarmonicPolynomial

theorem transmission_congr {l : ℕ} {gs gs' : List RadialStack.Layer} {R X X' : ℝ} {hR : 0<R}
    (h1 : gs=gs') (h2 : X=X') : transmission l gs R X hR=transmission l gs' R X' hR := by
  subst h1 h2
  rfl

theorem one_le_sq' (q : ℝ) (hq1 : 1≤q) : 1≤q^2 := by nlinarith

/-- The TE data of the physical paired stack at shell index `s` (the degree field is irrelevant). -/
def physicalTE (q : ℝ) (hq : 0<q) (n s : ℕ) : Data :=
  SourceDielectricModes.teData (SourcePairedGeometry.physicalData q hq n s) 0

theorem physicalTE_sigma (q : ℝ) (hq : 0<q) (n s : ℕ) : ∀ g∈(physicalTE q hq n s).gs,g.σ=1 :=
  SourceDielectricModes.te_sigma _ 0

theorem physicalTE_parameters (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n s : ℕ) :
    ∀ g∈(physicalTE q hq n s).gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤q^2 := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  have h := SourcePairedGeometry.physical_parameters q hq hq1 n s a ha
  have hd := SourcePairedGeometry.physical_dispersion q hq n s a ha
  change 1≤a.q^2/1 ∧ a.q^2/1≤q^2
  rw [div_one,hd]
  exact ⟨h.1,h.2.1⟩

theorem physicalTE_transmission (q : ℝ) (hq : 0<q) (n l s : ℕ) :
    transmission l (physicalTE q hq n s).gs (physicalTE q hq n s).R (physicalTE q hq n s).X
        (physicalTE q hq n s).hR=
      stackTransmission l (RadialPairedFamily.te q hq n) (RadialPhaseLimit.radius s)
        (RadialPhaseLimit.radius_pos s) := by
  unfold stackTransmission
  exact transmission_congr (SourcePairedGeometry.physical_te_layers q hq n s)
    (SourcePairedGeometry.physical_te_outer q hq n s)

theorem physicalTE_transmission_limit (q : ℝ) (hq : 0<q) (n l : ℕ) :
    Tendsto (fun s : ℕ => transmission l (physicalTE q hq n s).gs (physicalTE q hq n s).R
        (physicalTE q hq n s).X (physicalTE q hq n s).hR) atTop
      (𝓝 (limitingTransmission l (RadialPairedFamily.te q hq n))) := by
  have h := transmission_limit l (RadialPairedFamily.te q hq n)
  refine h.congr (fun s => ?_)
  exact (physicalTE_transmission q hq n l s).symm

/-- **Physical TE response.**  For the physical paired stack at shell index `s` and a finite TE coefficient
vector `A`, the field of the actual shell solution (incident field plus scattered field) is the TE background
field of the family. -/
theorem physicalTE_response (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n s : ℕ)
    (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    MaterialField.total (SourceMuMaterial.coefficient (physicalTE q hq n s) (q^2) (one_le_sq' q hq1)
        (physicalTE_parameters q hq hq1 n s)) 1
      (MaterialField.solution (SourceMuMaterial.coefficient (physicalTE q hq n s) (q^2) (one_le_sq' q hq1)
          (physicalTE_parameters q hq hq1 n s)) 1 (physicalTE q hq n s).X
        (RestrictedTEMaterial.datum (SourceMuMaterial.coefficient (physicalTE q hq n s) (q^2)
          (one_le_sq' q hq1) (physicalTE_parameters q hq hq1 n s))
          (teSupportData _ (physicalTE q hq n s).X (SourceTEWeightedDatum.material_outer _ _
            (SourceMuMaterial.value_complex (physicalTE q hq n s) (q^2) (one_le_sq' q hq1)
              (physicalTE_parameters q hq hq1 n s)))) A))
      (RestrictedTEPlaneLocal.electric A)=ᵐ[volume]
      famBackground (physicalTE q hq n s) A.support (teCoeff A) (fun q => q.val.1)
        RestrictedTEIncoming.polynomial :=
  te_finite_response _ (physicalTE_sigma q hq n s) (q^2) (one_le_sq' q hq1) _ A

/-- **Limit of the core part of the physical TE response.**  At every point away from the origin the core
field of the shells' response to the finite TE coefficient vector `A` converges, as the shell index
tends to infinity, to the regular TE field of `A` rescaled degreewise by `limitingTransmission/2`. -/
theorem physicalTE_core_tendsto (q : ℝ) (hq : 0<q) (n : ℕ) (A : SymmetricHarmonicJets.Index →₀ ℂ)
    (x : Space) (hx : x≠0) :
    Tendsto (fun s : ℕ => famBackground (physicalTE q hq n s) A.support (teCoeff A)
        (fun q => q.val.1) RestrictedTEIncoming.polynomial x) atTop
      (𝓝 (RestrictedTEPlaneLocal.electric
        (scaledCoeff A (fun l => limitingTransmission l (RadialPairedFamily.te q hq n)/2)) x)) := by
  have h := electric_scaledCoeff_tendsto (F := atTop) A
    (fun (s : ℕ) (l : ℕ) => transmission l (physicalTE q hq n s).gs (physicalTE q hq n s).R
      (physicalTE q hq n s).X (physicalTE q hq n s).hR/2)
    (fun l => limitingTransmission l (RadialPairedFamily.te q hq n)/2)
    (fun l => (physicalTE_transmission_limit q hq n l).div_const 2)
  have hx' := (tendsto_pi_nhds.mp h) x
  refine hx'.congr' ?_
  have hev : ∀ᶠ s : ℕ in atTop, ‖x‖≤(physicalTE q hq n s).R := by
    have hr := (RadialPhaseLimit.radius_tendsto.eventually (eventually_ge_atTop ‖x‖))
    exact hr
  filter_upwards [hev] with s hs
  exact (te_finite_core (physicalTE q hq n s) A x hx hs).symm

end Physical


section Complements
open OQ14.HarmonicPolynomial

/-- A basis TE mode: `electric (single q 1)` is `4 pi I^l * I` times the regular magnetic mode. -/
theorem electric_single (q : SymmetricHarmonicJets.Index) :
    RestrictedTEPlaneLocal.electric (Finsupp.single q (1 : ℂ))=
      (((4*Real.pi : ℂ)*Complex.I^q.val.1)*Complex.I) •
        SolidMaxwellProfiles.magnetic q.val.1 (RestrictedTEIncoming.polynomial q) := by
  classical
  funext x i
  rw [electric_eq_famIncident,famIncident_apply,Finsupp.support_single_ne_zero q one_ne_zero,
    Finset.sum_singleton]
  simp [teCoeff,RestrictedTEIncoming.coefficient]

/-- **Weak Maxwell for the TM background pair in the dielectric form.**  The pair solves
`curl E = I H`, `curl H = -I sigma E` against every compactly supported Schwartz test function, where
`sigma` is the real layer permittivity of the stack. -/
theorem background_testMaxwell (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (P : Poly)
    (hp : P.IsHomogeneous d.l) (hh : HarmonicPolynomial.formalLaplacian P=0) :
    TestMaxwell 1 (fun x => SourceMaterialCoefficient.realSigma d ‖x‖) (backgroundElectric d P)
      (backgroundMagnetic d P) := by
  intro i f
  obtain ⟨h1,h2⟩ := background_forced_sigma d hdisp P hp hh i f
  refine ⟨h1,?_⟩
  have hE := backgroundElectric_locallyIntegrable d P i
  have hi : (∫ x,((SourceMaterialCoefficient.realSigma d ‖x‖ : ℝ) : ℂ)*backgroundElectric d P x i*f.val x)=
      fieldPair (backgroundElectric d P) i f+
        ∫ x,((sigma d ‖x‖-1)*backgroundElectric d P x i)*f.val x := by
    have hs : ∀ x : Space,((SourceMaterialCoefficient.realSigma d ‖x‖ : ℝ) : ℂ)*backgroundElectric d P x i*
        f.val x=backgroundElectric d P x i*f.val x+((sigma d ‖x‖-1)*backgroundElectric d P x i)*f.val x := by
      intro x
      rw [← SourceMaterialCoefficient.sigma_eq]
      ring
    simp_rw [hs]
    have hI1 : Integrable (fun x => backgroundElectric d P x i*f.val x) :=
      PointSingularity.test_product_integrable _ _ hE f.val.continuous f.property
    have hI2 : Integrable (fun x => ((sigma d ‖x‖-1)*backgroundElectric d P x i)*f.val x) := by
      have hρ := (backgroundPolarization_integrable d P i).locallyIntegrable
      refine (PointSingularity.test_product_integrable _ _ hρ f.val.continuous f.property).congr ?_
      filter_upwards [show ∀ᵐ x : Space, x≠0 from ae_iff.mpr (by simp)] with x hx
      rw [backgroundPolarization_eq d P hp hh x hx i]
    exact integral_add hI1 hI2
  rw [hi]
  exact h2

end Complements


section PhysicalTM
open OQ14.HarmonicPolynomial

/-- The TM data of degree `l` of the physical paired stack at shell index `s`. -/
def physicalTM (q : ℝ) (hq : 0<q) (n s l : ℕ) : Data :=
  { SourcePairedGeometry.physicalData q hq n s with l := l }

/-- **Physical TM response.**  For the physical paired stack, the total field of the regular incident TM
mode of degree `l` (incident mode plus the field scattered by the actual shell solution) is the background
electric field almost everywhere. -/
theorem physicalTM_response (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n s l : ℕ) (P : Poly)
    (hp : P.IsHomogeneous l) (hh : HarmonicPolynomial.formalLaplacian P=0) :
    MaterialField.total (SourceMaterialCoefficient.coefficient (physicalTM q hq n s l) (q^2)
        (one_le_sq' q hq1) (SourcePairedGeometry.physical_material_bounds q hq hq1 n s)) 1
      (MaterialField.solution (SourceMaterialCoefficient.coefficient (physicalTM q hq n s l) (q^2)
          (one_le_sq' q hq1) (SourcePairedGeometry.physical_material_bounds q hq hq1 n s)) 1
        (physicalTM q hq n s l).X
        (incidentDatum (physicalTM q hq n s l) (q^2) (one_le_sq' q hq1)
          (SourcePairedGeometry.physical_material_bounds q hq hq1 n s) P))
      (SolidMaxwellProfiles.electric l P)=ᵐ[volume] backgroundElectric (physicalTM q hq n s l) P :=
  total_eq_background (physicalTM q hq n s l) (q^2) (one_le_sq' q hq1)
    (SourcePairedGeometry.physical_material_bounds q hq hq1 n s)
    (SourcePairedGeometry.physical_dispersion q hq n s) P hp hh

/-- Core field of the physical TM response: `physicalTransmission/2` times the regular incident mode. -/
theorem physicalTM_core (q : ℝ) (hq : 0<q) (n s l : ℕ) (P : Poly) (hp : P.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : x≠0)
    (hR : ‖x‖≤RadialPhaseLimit.radius s) :
    backgroundElectric (physicalTM q hq n s l) P x=
      (physicalTransmission q hq n l s/2) • SolidMaxwellProfiles.electric l P x :=
  backgroundElectric_core (physicalTM q hq n s l) P hp hh x hx hR

/-- **Limit of the core field of the physical TM response**: it converges to `physicalLimit/2` times the
regular incident mode. -/
theorem physicalTM_core_tendsto (q : ℝ) (hq : 0<q) (n l : ℕ) (P : Poly) (hp : P.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : x≠0) :
    Tendsto (fun s : ℕ => backgroundElectric (physicalTM q hq n s l) P x) atTop
      (𝓝 ((physicalLimit q hq n l/2) • SolidMaxwellProfiles.electric l P x)) := by
  have h := ((physical_transmission_limit q hq n l).div_const 2).smul_const
    (SolidMaxwellProfiles.electric l P x)
  refine h.congr' ?_
  have hev : ∀ᶠ s : ℕ in atTop, ‖x‖≤RadialPhaseLimit.radius s :=
    RadialPhaseLimit.radius_tendsto.eventually (eventually_ge_atTop ‖x‖)
  filter_upwards [hev] with s hs
  exact (physicalTM_core q hq n s l P hp hh x hx hs).symm

end PhysicalTM


section Parity
open OQ14.HarmonicPolynomial

theorem parity_block_one {c : StaticCoefficient.Coefficient} (d : BoundedMaterialKernel.SupportData c)
    (k : ℝ) : ParityMaterialField.block d k 1=DynamicVolume.volumeBlock c k d.radius := by
  rw [ParityMaterialField.block_eq]
  simp

theorem parity_solution_one {c : StaticCoefficient.Coefficient} (d : BoundedMaterialKernel.SupportData c)
    (k : ℝ) (f : VectorFourier.VectorL2) :
    ParityMaterialField.solution d k 1 f=MaterialField.solution c k d.radius f := by
  unfold ParityMaterialField.solution MaterialField.solution
  rw [parity_block_one]

theorem parity_total_one {c : StaticCoefficient.Coefficient} (k : ℝ) (u : VectorFourier.VectorL2)
    (incident : Field) :
    ParityMaterialField.total c k 1 u incident=MaterialField.total c k u incident := by
  funext x i
  simp [ParityMaterialField.total,ParityMaterialField.scattered,MaterialField.total]

/-- The finite TE response stated with the restricted-TE parity solution at `B = 1`. -/
theorem te_finite_response_parity (d0 : Data) (hσ : ∀ g∈d0.gs,g.σ=1) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d0.gs,1≤g.q^2/g.σ ∧ g.q^2/g.σ≤M) (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    ParityMaterialField.total (SourceMuMaterial.coefficient d0 M hM hs) 1 1
      (ParityMaterialField.solution (teSupportData _ d0.X (SourceTEWeightedDatum.material_outer _ d0
        (SourceMuMaterial.value_complex d0 M hM hs))) 1 1
        (RestrictedTEMaterial.datum (SourceMuMaterial.coefficient d0 M hM hs)
          (teSupportData _ d0.X (SourceTEWeightedDatum.material_outer _ d0
            (SourceMuMaterial.value_complex d0 M hM hs))) A))
      (RestrictedTEPlaneLocal.electric A)=ᵐ[volume]
      famBackground d0 A.support (teCoeff A) (fun q => q.val.1) RestrictedTEIncoming.polynomial := by
  rw [parity_total_one,parity_solution_one]
  exact te_finite_response d0 hσ M hM hs A

end Parity


section ConjugationLemmas
open OQ14.HarmonicPolynomial

theorem conj_clippedInverse (gs : List RadialStack.Layer) (r : ℝ) :
    conj (ClippedLayerProfiles.inverseSigma gs r)=ClippedLayerProfiles.inverseSigma gs r := by
  induction gs with
  | nil => simp [ClippedLayerProfiles.inverseSigma,ClippedLayerProfiles.select]
  | cons g gs ih =>
    simp only [ClippedLayerProfiles.inverseSigma,ClippedLayerProfiles.select] at ih ⊢
    split_ifs
    · simp
    · exact ih

theorem conj_inverseSigma (d : Data) (r : ℝ) : conj (inverseSigma d r)=inverseSigma d r := by
  unfold inverseSigma SourceRadialSystem.extend
  split_ifs
  · simp
  · exact conj_clippedInverse d.gs r
  · simp

/-- For a real polynomial the conjugate of the source electric field is the electric formula applied to the
conjugated radial state. -/
theorem conj_electric_eq_form (d : Data) (P : Poly) (x : Space) (i : Fin 3) :
    conj (SourceUnclippedMaxwell.electric d P x i)=
      Eform d.l P (inverseSigma d ‖x‖) (conjState (raw d ‖x‖)).1 (conjState (raw d ‖x‖)).2 x i := by
  rw [electric_eq_Eform,conj_Eform,conj_inverseSigma]
  rfl

/-- The conjugate of the source magnetic field is minus the magnetic formula applied to the conjugated
radial state (the factor `-I`). -/
theorem conj_magnetic_eq_form (d : Data) (P : Poly) (x : Space) (i : Fin 3) :
    conj (SourceUnclippedMaxwell.magnetic d P x i)=-Hform d.l P (conjState (raw d ‖x‖)).1 x i := by
  rw [magnetic_eq_Hform,conj_Hform]
  rfl

/-- **Conjugation of weak Maxwell pairs with real permittivity.**  If `(E,H)` is a weak Maxwell pair for the
real wavenumber `k` and real permittivity `ε` (and unit permeability), then so is `(conj E, -conj H)`. -/
theorem testMaxwell_conj (k : ℝ) (ε : Space → ℝ) (E H : Field) (h : TestMaxwell k ε E H) :
    TestMaxwell k ε (BackgroundModeMaxwell.conjField E) (negConjField H) := by
  intro i f
  obtain ⟨h1,h2⟩ := h i (conjTest f)
  have hk : conj (k : ℂ)=(k : ℂ) := Complex.conj_ofReal k
  have hint : (∫ x,(ε x : ℂ)*BackgroundModeMaxwell.conjField E x i*f.val x)=
      conj (∫ x,(ε x : ℂ)*E x i*(conjTest f).val x) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with x
    simp [BackgroundModeMaxwell.conjField,conjTest_apply]
  constructor
  · rw [curlPair_conj,h1,fieldPair_negConj,map_mul,map_mul,hk,Complex.conj_I]
    ring
  · rw [curlPair_negConj,h2,hint,map_mul,map_neg,map_mul,hk,Complex.conj_I]
    ring

end ConjugationLemmas

end OQ14.BackgroundModeTE
#print axioms OQ14.BackgroundModeTE.RadiatingPair.source_coordinate
#print axioms OQ14.BackgroundModeTE.RadiatingPair.source_actual
#print axioms OQ14.BackgroundModeTE.RadiatingPair.representation
#print axioms OQ14.BackgroundModeTE.sum_nonempty
#print axioms OQ14.BackgroundModeTE.testForced_fields_congr
#print axioms OQ14.BackgroundModeTE.locallyIntegrable_conj_fun
#print axioms OQ14.BackgroundModeTE.teVacuumPair
#print axioms OQ14.BackgroundModeTE.teBackgroundPolarization_loc
#print axioms OQ14.BackgroundModeTE.te_background_forced
#print axioms OQ14.BackgroundModeTE.scatteredMagnetic_smooth
#print axioms OQ14.BackgroundModeTE.conj_select_mu
#print axioms OQ14.BackgroundModeTE.conj_mu
#print axioms OQ14.BackgroundModeTE.teBackgroundPolarization_eq
#print axioms OQ14.BackgroundModeTE.famBackground_apply
#print axioms OQ14.BackgroundModeTE.famIncident_apply
#print axioms OQ14.BackgroundModeTE.famBackground_memLp
#print axioms OQ14.BackgroundModeTE.famIncident_continuous
#print axioms OQ14.BackgroundModeTE.famForce_eq
#print axioms OQ14.BackgroundModeTE.famPair_nonempty
#print axioms OQ14.BackgroundModeTE.famBackgroundDatum_actual
#print axioms OQ14.BackgroundModeTE.famIncidentDatum_actual
#print axioms OQ14.BackgroundModeTE.famBackgroundDatum_source
#print axioms OQ14.BackgroundModeTE.te_family_volume_equation
#print axioms OQ14.BackgroundModeTE.te_family_solution
#print axioms OQ14.BackgroundModeTE.te_family_total
#print axioms OQ14.BackgroundModeTE.polynomial_homogeneous
#print axioms OQ14.BackgroundModeTE.polynomial_harmonic
#print axioms OQ14.BackgroundModeTE.teElectric_wave
#print axioms OQ14.BackgroundModeTE.electric_eq_famIncident
#print axioms OQ14.BackgroundModeTE.electric_scaledCoeff_eq
#print axioms OQ14.BackgroundModeTE.teCoeff_scaledCoeff
#print axioms OQ14.BackgroundModeTE.te_finite_datum
#print axioms OQ14.BackgroundModeTE.te_finite_response
#print axioms OQ14.BackgroundModeTE.te_finite_core
#print axioms OQ14.BackgroundModeTE.transmission_congr
#print axioms OQ14.BackgroundModeTE.one_le_sq'
#print axioms OQ14.BackgroundModeTE.physicalTE_sigma
#print axioms OQ14.BackgroundModeTE.physicalTE_parameters
#print axioms OQ14.BackgroundModeTE.physicalTE_transmission
#print axioms OQ14.BackgroundModeTE.physicalTE_transmission_limit
#print axioms OQ14.BackgroundModeTE.physicalTE_response
#print axioms OQ14.BackgroundModeTE.physicalTE_core_tendsto
#print axioms OQ14.BackgroundModeTE.electric_single
#print axioms OQ14.BackgroundModeTE.background_testMaxwell
#print axioms OQ14.BackgroundModeTE.physicalTM_response
#print axioms OQ14.BackgroundModeTE.physicalTM_core
#print axioms OQ14.BackgroundModeTE.physicalTM_core_tendsto
#print axioms OQ14.BackgroundModeTE.parity_block_one
#print axioms OQ14.BackgroundModeTE.parity_solution_one
#print axioms OQ14.BackgroundModeTE.parity_total_one
#print axioms OQ14.BackgroundModeTE.te_finite_response_parity
#print axioms OQ14.BackgroundModeTE.conj_clippedInverse
#print axioms OQ14.BackgroundModeTE.conj_inverseSigma
#print axioms OQ14.BackgroundModeTE.conj_electric_eq_form
#print axioms OQ14.BackgroundModeTE.conj_magnetic_eq_form
#print axioms OQ14.BackgroundModeTE.testMaxwell_conj
