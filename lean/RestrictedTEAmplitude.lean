import RestrictedTEIncoming

/-! Actual transverse incoming amplitude and Herglotz identification of restricted TE fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEAmplitude
open Complex MeasureTheory Maxwell HarmonicPolynomial DebyeRadialTrace
open RestrictedTEIncoming SymmetricHarmonicJets
abbrev Space := FourierL2.Space
abbrev Sphere := SphereReactionKernel.Sphere

def density (A : Index →₀ ℂ) (n : Sphere) : Vector :=
  fun j => ∑ q ∈ A.support, A q*angularToroidal (polynomial q) n j
def amplitude (A : Index →₀ ℂ) : Sphere → Vector :=
  FiniteTEIncomingPower.amplitude A.support (fun q => q.val.1) polynomial (coefficient A)

theorem angular_zero (x : Space) : angularToroidal 0 x=0 := by
  ext j
  fin_cases j <;> simp [angularToroidal,complexEvaluate_partial,complexEvaluate,evaluate]

theorem phase_even (l : ℕ) (hl : Even l) : I^l*I^(l+1)=I := by
  calc
    _ = (I^2)^l*I := by rw [pow_succ,pow_two,mul_pow]; ring
    _ = I := by rw [I_sq,hl.neg_one_pow,one_mul]

theorem amplitude_eq (A : Index →₀ ℂ) (n : Sphere) : amplitude A n=(2*Real.pi*I : ℂ) • density A n := by
  ext j
  simp only [amplitude,FiniteTEIncomingPower.amplitude,FiniteTEIncomingPower.amplitudeCoefficient,
    FiniteTEIncomingPower.angular,RegularTEIncoming.coefficient,if_true,density,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  change coefficient A q*I^(q.val.1+1)/2*angularToroidal (polynomial q) n j=
    (2*Real.pi*I : ℂ)*(A q*angularToroidal (polynomial q) n j)
  by_cases he : Even q.val.1
  · unfold coefficient
    have hh := phase_even q.val.1 he
    calc
      _ = (A q*(4*Real.pi : ℂ)/2)*(I^q.val.1*I^(q.val.1+1))*angularToroidal (polynomial q) n j := by ring
      _ = _ := by rw [hh]; ring
  · have hp : polynomial q=0 := by simp [polynomial,EvenHarmonicProjection.project,he]
    simp [hp,angular_zero]

theorem density_continuous (A : Index →₀ ℂ) : Continuous (density A) := by
  apply continuous_pi
  intro j
  apply continuous_finset_sum
  intro q _
  exact continuous_const.mul ((continuous_apply j).comp
    ((HarmonicRadiationGeometry.angularToroidal_continuous (polynomial q)).comp continuous_subtype_val))

theorem amplitude_continuous (A : Index →₀ ℂ) : Continuous (amplitude A) := by
  rw [show amplitude A=(fun n : Sphere => (2*Real.pi*I : ℂ) • density A n) from funext (amplitude_eq A)]
  exact continuous_const.smul (density_continuous A)

theorem density_transverse (A : Index →₀ ℂ) (n : Sphere) : dot (position n) (density A n)=0 := by
  unfold dot density
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro q _
  simp [angularToroidal,position]
  ring

theorem amplitude_transverse (A : Index →₀ ℂ) (n : Sphere) : dot (position n) (amplitude A n)=0 := by
  rw [amplitude_eq]
  have he : dot (position n) ((2*Real.pi*I : ℂ) • density A n)=
      (2*Real.pi*I : ℂ)*dot (position n) (density A n) := by simp [dot,Pi.smul_apply];ring
  rw [he,density_transverse,mul_zero]

theorem electric_herglotz (A : Index →₀ ℂ) (x : Space) (j : Fin 3) :
    DebyeMaxwell.teElectric (RestrictedTEFields.potential 1 A) x j=
      ∫ n : Sphere, density A n j*SphereReactionKernel.wave 1 x n ∂SphereReactionKernel.surface := by
  rw [RestrictedTEIncoming.electric_sum]
  symm
  unfold density
  simp only [Finset.sum_mul]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro q _
    rw [show (fun n : Sphere => A q*angularToroidal (polynomial q) n j*SphereReactionKernel.wave 1 x n)=
      (fun n : Sphere => A q*(angularToroidal (polynomial q) n j*SphereReactionKernel.wave 1 x n)) from funext (fun n => by ring),integral_const_mul,
      ToroidalPlaneWaveMoment.actual_toroidal_integral q.val.1 (polynomial q)
        (EvenHarmonicProjection.homogeneous _ _ q.property.1)
        (EvenHarmonicProjection.harmonic _ _ q.property.2) 1 x j]
    simp [coefficient,DebyeMaxwell.teElectric]
    ring
  · intro q _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    have ht : Continuous (fun n : Sphere => angularToroidal (polynomial q) n j) :=
      (continuous_apply j).comp ((HarmonicRadiationGeometry.angularToroidal_continuous (polynomial q)).comp continuous_subtype_val)
    have hw : Continuous (SphereReactionKernel.wave 1 x) := by unfold SphereReactionKernel.wave; fun_prop
    exact (continuous_const.mul ht).mul hw

end OQ14.RestrictedTEAmplitude
#print axioms OQ14.RestrictedTEAmplitude.angular_zero
#print axioms OQ14.RestrictedTEAmplitude.phase_even
#print axioms OQ14.RestrictedTEAmplitude.amplitude_eq
#print axioms OQ14.RestrictedTEAmplitude.density_continuous
#print axioms OQ14.RestrictedTEAmplitude.amplitude_continuous
#print axioms OQ14.RestrictedTEAmplitude.density_transverse
#print axioms OQ14.RestrictedTEAmplitude.amplitude_transverse
#print axioms OQ14.RestrictedTEAmplitude.electric_herglotz
