import FiniteVectorAngular
import RegularTMIncoming
import TEFiniteCalculus
import PlaneDebyeCoefficients

/-! Genuine finite mixed-polarization regular Maxwell fields with the negative-phase Herglotz factors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.FiniteMixedFields
open Complex Set OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open OQ14.ComplexTransverseExpansion

def index : ModeIndex → PositiveIndex := Sum.elim id id
def degree (m : ModeIndex) : ℕ := (index m).1+1
def polynomial (m : ModeIndex) : HarmonicPolynomial.Poly := representative (degree m) (index m).2

def phaseFactor : ModeIndex → ℂ
  | Sum.inl a => I*(4*Real.pi : ℂ)*(-I)^(a.1+1)
  | Sum.inr a => (4*Real.pi : ℂ)*(-I)^(a.1+1)

def modeElectric : ModeIndex → Field
  | Sum.inl a => SolidMaxwellProfiles.electric (a.1+1) (representative (a.1+1) a.2)
  | Sum.inr a => DebyeMaxwell.teElectric (SolidScalarHelmholtz.wave (a.1+1) 1 (representative (a.1+1) a.2))
def modeMagnetic : ModeIndex → Field
  | Sum.inl a => SolidMaxwellProfiles.magnetic (a.1+1) (representative (a.1+1) a.2)
  | Sum.inr a => DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave (a.1+1) 1 (representative (a.1+1) a.2))

def halfElectric : ModeIndex → Bool → Field
  | Sum.inl a,b => RegularTMIncoming.electric (a.1+1) b (representative (a.1+1) a.2)
  | Sum.inr a,b => RegularTEIncoming.electric (a.1+1) b (representative (a.1+1) a.2)
def halfMagnetic : ModeIndex → Bool → Field
  | Sum.inl a,b => RegularTMIncoming.magnetic (a.1+1) b (representative (a.1+1) a.2)
  | Sum.inr a,b => RegularTEIncoming.magnetic (a.1+1) b (representative (a.1+1) a.2)

def scalar (c : ModeIndex →₀ ℂ) (m : ModeIndex) : ℂ :=
  c m*phaseFactor m*(normalizer (index m).1 : ℂ)

def electric (c : ModeIndex →₀ ℂ) : Field := fun x i => ∑ m∈c.support,scalar c m*modeElectric m x i
def magnetic (c : ModeIndex →₀ ℂ) : Field := fun x i => ∑ m∈c.support,scalar c m*modeMagnetic m x i
def electricPart (c : ModeIndex →₀ ℂ) (b : Bool) : Field := fun x i => ∑ m∈c.support,scalar c m*halfElectric m b x i
def magneticPart (c : ModeIndex →₀ ℂ) (b : Bool) : Field := fun x i => ∑ m∈c.support,scalar c m*halfMagnetic m b x i

theorem modeElectric_smooth (m : ModeIndex) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => modeElectric m x i) := by
  cases m with
  | inl a => exact SolidMaxwellProfiles.electric_smooth _ _ i
  | inr a =>
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact DebyeCalculus.toroidal_smooth _ x (SolidScalarHelmholtz.wave_contDiff _ _ _).contDiffAt i

theorem modeMagnetic_smooth (m : ModeIndex) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => modeMagnetic m x i) := by
  cases m with
  | inl a => exact SolidMaxwellProfiles.magnetic_smooth _ _ i
  | inr a => exact contDiff_const.mul (SolidMaxwellProfiles.electric_smooth _ _ i)

theorem mode_maxwell (m : ModeIndex) (x : Space) : MaxwellAt 1 1 1 (modeElectric m) (modeMagnetic m) x := by
  cases m with
  | inl a => exact SolidMaxwellProfiles.actual_maxwell _ _ (representative_homogeneous _ _) (representative_harmonic _ _) x
  | inr a =>
    exact DebyeMaxwell.te_real_maxwell isOpen_univ _
      (fun _ _ => (SolidScalarHelmholtz.wave_contDiff _ _ _).contDiffAt)
      1 1 1 (by norm_num) (by ring)
      (fun y _ => SolidScalarHelmholtz.wave_helmholtz _ _ _
        (representative_homogeneous _ _) (representative_harmonic _ _) y) x (mem_univ x)

theorem electric_smooth (c : ModeIndex →₀ ℂ) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => electric c x i) :=
  ContDiff.sum (fun m _ => contDiff_const.mul (modeElectric_smooth m i))

theorem magnetic_smooth (c : ModeIndex →₀ ℂ) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => magnetic c x i) :=
  ContDiff.sum (fun m _ => contDiff_const.mul (modeMagnetic_smooth m i))

theorem actual_maxwell (c : ModeIndex →₀ ℂ) (x : Space) : MaxwellAt 1 1 1 (electric c) (magnetic c) x := by
  constructor
  · ext i
    change curl (fun y j => ∑ m∈c.support,scalar c m*modeElectric m y j) x i=_
    rw [TEFiniteCalculus.curl_sum c.support modeElectric (scalar c) x
      (fun m _ j => (modeElectric_smooth m j).contDiffAt.differentiableAt (by simp)) i]
    simp only [Complex.ofReal_one,mul_one,magnetic,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [congrFun (mode_maxwell m x).1 i]
    simp only [Complex.ofReal_one,mul_one]
    ring
  · ext i
    change curl (fun y j => ∑ m∈c.support,scalar c m*modeMagnetic m y j) x i=_
    rw [TEFiniteCalculus.curl_sum c.support modeMagnetic (scalar c) x
      (fun m _ j => (modeMagnetic_smooth m j).contDiffAt.differentiableAt (by simp)) i]
    simp only [Complex.ofReal_one,mul_one,electric,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [congrFun (mode_maxwell m x).2 i]
    simp only [Complex.ofReal_one,mul_one]
    ring

theorem mode_electric_split (m : ModeIndex) (x : Space) (hx : x≠0) :
    modeElectric m x=halfElectric m false x+halfElectric m true x := by
  cases m with
  | inl a => exact RegularTMIncoming.electric_split _ _ (representative_homogeneous _ _) x hx
  | inr a => exact RegularTEDecomposition.electric_split _ _ (representative_homogeneous _ _) x hx

theorem mode_magnetic_split (m : ModeIndex) (x : Space) (hx : x≠0) :
    modeMagnetic m x=halfMagnetic m false x+halfMagnetic m true x := by
  cases m with
  | inl a => exact RegularTMIncoming.magnetic_split _ _ (representative_homogeneous _ _) x hx
  | inr a => exact RegularTEDecomposition.magnetic_split _ _ (representative_homogeneous _ _) x hx

theorem electric_split (c : ModeIndex →₀ ℂ) (x : Space) (hx : x≠0) :
    electric c x=electricPart c false x+electricPart c true x := by
  ext i
  simp only [electric,electricPart,Pi.add_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [mode_electric_split m x hx]
  simp only [Pi.add_apply,mul_add]

theorem magnetic_split (c : ModeIndex →₀ ℂ) (x : Space) (hx : x≠0) :
    magnetic c x=magneticPart c false x+magneticPart c true x := by
  ext i
  simp only [magnetic,magneticPart,Pi.add_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [mode_magnetic_split m x hx]
  simp only [Pi.add_apply,mul_add]

theorem power_phase (l : ℕ) : (-I)^l*I^(l+1)=I := by
  calc
    _ = ((-I)*I)^l*I := by rw [mul_pow,pow_succ]; ring
    _ = _ := by simp [I_sq]

theorem incoming_toroidal_phase (a : PositiveIndex) :
    phaseFactor (Sum.inr a)*RegularTEIncoming.coefficient (a.1+1) true/2=(2*Real.pi : ℂ)*I := by
  change (4*Real.pi : ℂ)*(-I)^(a.1+1)*I^((a.1+1)+1)/2=_
  calc
    _ = ((4*Real.pi : ℂ)/2)*((-I)^(a.1+1)*I^((a.1+1)+1)) := by ring
    _ = _ := by rw [power_phase]; ring

theorem incoming_poloidal_phase (a : PositiveIndex) :
    phaseFactor (Sum.inl a)*(RegularTEIncoming.coefficient (a.1+1) true*(-I)/2)=(2*Real.pi : ℂ)*I := by
  calc
    _ = (I*(-I))*(phaseFactor (Sum.inr a)*RegularTEIncoming.coefficient (a.1+1) true/2) := by
      simp only [phaseFactor]
      ring
    _ = _ := by
      rw [show I*(-I)=(1 : ℂ) by norm_num,one_mul,incoming_toroidal_phase]

end OQ14.FiniteMixedFields
#print axioms OQ14.FiniteMixedFields.modeElectric_smooth
#print axioms OQ14.FiniteMixedFields.modeMagnetic_smooth
#print axioms OQ14.FiniteMixedFields.mode_maxwell
#print axioms OQ14.FiniteMixedFields.electric_smooth
#print axioms OQ14.FiniteMixedFields.magnetic_smooth
#print axioms OQ14.FiniteMixedFields.actual_maxwell
#print axioms OQ14.FiniteMixedFields.mode_electric_split
#print axioms OQ14.FiniteMixedFields.mode_magnetic_split
#print axioms OQ14.FiniteMixedFields.electric_split
#print axioms OQ14.FiniteMixedFields.magnetic_split
#print axioms OQ14.FiniteMixedFields.power_phase
#print axioms OQ14.FiniteMixedFields.incoming_toroidal_phase
#print axioms OQ14.FiniteMixedFields.incoming_poloidal_phase
