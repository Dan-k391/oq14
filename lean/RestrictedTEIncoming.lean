import RestrictedTEInterpolation
import RestrictedTEParity
import RegularTEDecomposition
import TEFiniteCalculus
import FiniteTEIncomingPower

/-! Actual incoming parts and physical power of the interpolated restricted TE fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEIncoming
open Complex Filter Maxwell HarmonicPolynomial SymmetricHarmonicJets RestrictedTEFields
open scoped Topology
abbrev Space := FourierL2.Space

def polynomial (q : Index) : Poly := EvenHarmonicProjection.project q.val.1 q.val.2
def coefficient (A : Index →₀ ℂ) (q : Index) : ℂ := A q*((4*Real.pi : ℂ)*I^q.val.1)

theorem potential_eq (A : Index →₀ ℂ) : potential 1 A=
    (fun x => ∑ q ∈ A.support, coefficient A q*SolidScalarHelmholtz.wave q.val.1 1 (polynomial q) x) := by
  funext x
  simp only [potential,RestrictedHarmonicInterpolation.scalar,Complex.ofReal_one,one_pow,mul_one,coefficient,polynomial,mul_assoc]

theorem electric_sum (A : Index →₀ ℂ) (x : Space) (i : Fin 3) :
    DebyeMaxwell.teElectric (potential 1 A) x i=
      ∑ q ∈ A.support, coefficient A q*DebyeMaxwell.teElectric (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) x i := by
  rw [potential_eq]
  exact TEFiniteCalculus.electric_sum _ _ _ (fun q _ => SolidScalarHelmholtz.wave_contDiff _ _ _) x i

theorem magnetic_sum (A : Index →₀ ℂ) (x : Space) (i : Fin 3) :
    DebyeMaxwell.teMagnetic 1 (potential 1 A) x i=
      ∑ q ∈ A.support, coefficient A q*DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) x i := by
  rw [potential_eq]
  exact TEFiniteCalculus.magnetic_sum _ _ _ (fun q _ => SolidScalarHelmholtz.wave_contDiff _ _ _) 1 x i

def incomingElectric (A : Index →₀ ℂ) : Field :=
  FiniteTEIncomingPower.electric A.support (fun q => q.val.1) polynomial (coefficient A)
def incomingMagnetic (A : Index →₀ ℂ) : Field :=
  FiniteTEIncomingPower.magnetic A.support (fun q => q.val.1) polynomial (coefficient A)
def outgoingElectric (A : Index →₀ ℂ) : Field :=
  fun x i => ∑ q ∈ A.support, coefficient A q*RegularTEIncoming.electric q.val.1 false (polynomial q) x i
def outgoingMagnetic (A : Index →₀ ℂ) : Field :=
  fun x i => ∑ q ∈ A.support, coefficient A q*RegularTEIncoming.magnetic q.val.1 false (polynomial q) x i

theorem electric_split (A : Index →₀ ℂ) (x : Space) (hx : x≠0) :
    DebyeMaxwell.teElectric (potential 1 A) x=outgoingElectric A x+incomingElectric A x := by
  ext i
  rw [electric_sum]
  simp only [incomingElectric,FiniteTEIncomingPower.electric,outgoingElectric,Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [RegularTEDecomposition.electric_split q.val.1 (polynomial q)
    (EvenHarmonicProjection.homogeneous _ _ q.property.1) x hx]
  simp only [Pi.add_apply]
  ring

theorem magnetic_split (A : Index →₀ ℂ) (x : Space) (hx : x≠0) :
    DebyeMaxwell.teMagnetic 1 (potential 1 A) x=outgoingMagnetic A x+incomingMagnetic A x := by
  ext i
  rw [magnetic_sum]
  simp only [incomingMagnetic,FiniteTEIncomingPower.magnetic,outgoingMagnetic,Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [RegularTEDecomposition.magnetic_split q.val.1 (polynomial q)
    (EvenHarmonicProjection.homogeneous _ _ q.property.1) x hx]
  simp only [Pi.add_apply]
  ring

def physicalPower (A : Index →₀ ℂ) : ℝ :=
  FiniteTEIncomingPower.incomingPower A.support (fun q => q.val.1) polynomial (coefficient A)

theorem actual_power_limit (A : Index →₀ ℂ) :
    Tendsto (fun r : ℝ => ∫ n : SphereReactionKernel.Sphere, -r^2*FarFieldPower.radialPower n
      (incomingElectric A (r • (n : Space))) (incomingMagnetic A (r • (n : Space))) ∂SphereReactionKernel.surface)
      atTop (𝓝 (physicalPower A)) := by
  exact FiniteTEIncomingPower.actual_power_limit A.support (fun q => q.val.1) polynomial
    (fun q => EvenHarmonicProjection.homogeneous _ _ q.property.1)
    (fun q => EvenHarmonicProjection.harmonic _ _ q.property.2) (coefficient A)

theorem physical_power_nonnegative (A : Index →₀ ℂ) : 0 ≤ physicalPower A :=
  FiniteTEIncomingPower.incoming_power_nonnegative _ _ _ _

end OQ14.RestrictedTEIncoming
#print axioms OQ14.RestrictedTEIncoming.potential_eq
#print axioms OQ14.RestrictedTEIncoming.electric_sum
#print axioms OQ14.RestrictedTEIncoming.magnetic_sum
#print axioms OQ14.RestrictedTEIncoming.electric_split
#print axioms OQ14.RestrictedTEIncoming.magnetic_split
#print axioms OQ14.RestrictedTEIncoming.actual_power_limit
#print axioms OQ14.RestrictedTEIncoming.physical_power_nonnegative
