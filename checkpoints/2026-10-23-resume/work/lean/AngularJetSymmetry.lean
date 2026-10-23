import AngularScalarJets
import HarmonicHalfTurn

/-! Actual symmetric angular jet kernels on the measurement plane. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.AngularJetSymmetry
open MeasureTheory Maxwell ModalDipole SphereReactionKernel SphereWaveCalculus
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem scalarJet_neg (r : ℝ) (y : ι → ℝ) (s t : ℂ) :
    EdgeScalarInterpolation.scalarJet r y (-s) (-t)=EdgeScalarInterpolation.scalarJet r y s t := by
  funext q
  rcases q with ⟨j,n⟩
  have he : (r : ℂ)*(-s)+(y j : ℂ)*(-t)= -((r : ℂ)*s+(y j : ℂ)*t) := by ring
  fin_cases n <;> dsimp only [EdgeScalarInterpolation.scalarJet] <;>
    rw [he] <;> simp only [Complex.cos_neg,Complex.sin_neg] <;> ring

def cosineJet (k r : ℝ) (y : ι → ℝ) (θ : Sphere) : EdgeScalarInterpolation.Jet ι :=
  EdgeScalarInterpolation.scalarJet r y (k*θ.val 0) (k*θ.val 1)

omit [Fintype ι] in
theorem cosineJet_continuous (k r : ℝ) (y : ι → ℝ) : Continuous (cosineJet k r y) := by
  apply continuous_pi
  rintro ⟨j,n⟩
  have h0 : Continuous (fun θ : Sphere => (k : ℂ)*(θ.val 0 : ℂ)) := continuous_const.mul (coordinate_continuous 0)
  have h1 : Continuous (fun θ : Sphere => (k : ℂ)*(θ.val 1 : ℂ)) := continuous_const.mul (coordinate_continuous 1)
  have hp : Continuous (fun θ : Sphere => (r : ℂ)*((k : ℂ)*(θ.val 0 : ℂ))+(y j : ℂ)*((k : ℂ)*(θ.val 1 : ℂ))) := (continuous_const.mul h0).add (continuous_const.mul h1)
  have hc := Complex.continuous_cos.comp hp
  have hs := Complex.continuous_sin.comp hp
  fin_cases n <;> dsimp only [cosineJet,EdgeScalarInterpolation.scalarJet]
  · exact hc
  · exact h0.neg.mul hs
  · exact h1.neg.mul hs
  · exact (h0.pow 2).neg.mul hc
  · exact (h0.neg.mul h1).mul hc
  · exact (h1.pow 2).neg.mul hc

omit [Fintype ι] in
theorem cosineJet_half_turn (k r : ℝ) (y : ι → ℝ) (θ : Sphere) :
    cosineJet k r y (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ)=cosineJet k r y θ := by
  have h0 : (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ).val 0= -θ.val 0 := by
    change HarmonicHalfTurn.rotation θ.val 0= -θ.val 0
    simp [HarmonicHalfTurn.rotation_apply,reflect,sign]
  have h1 : (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ).val 1= -θ.val 1 := by
    change HarmonicHalfTurn.rotation θ.val 1= -θ.val 1
    simp [HarmonicHalfTurn.rotation_apply,reflect,sign]
  simp only [cosineJet,h0,h1,mul_neg,Complex.ofReal_neg]
  exact scalarJet_neg r y _ _

omit [Fintype ι] in
theorem cosineJet_central (k r : ℝ) (y : ι → ℝ) (θ : Sphere) :
    cosineJet k r y (SphereAngularSymmetry.sphereMap (LinearIsometryEquiv.neg ℝ) θ)=cosineJet k r y θ := by
  have h0 : (SphereAngularSymmetry.sphereMap (LinearIsometryEquiv.neg ℝ) θ).val 0= -θ.val 0 := rfl
  have h1 : (SphereAngularSymmetry.sphereMap (LinearIsometryEquiv.neg ℝ) θ).val 1= -θ.val 1 := rfl
  simp only [cosineJet,h0,h1]
  simp only [mul_neg,Complex.ofReal_neg]
  exact scalarJet_neg r y _ _

omit [Fintype ι] in
theorem wave_on_plane (k r : ℝ) (y : ι → ℝ) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0) (θ : Sphere) (j : ι) :
    SphereReactionKernel.wave k (p j) θ=
      Complex.exp (((r : ℂ)*(k*θ.val 0 : ℝ)+(y j : ℂ)*(k*θ.val 1 : ℝ))*Complex.I) := by
  unfold SphereReactionKernel.wave
  congr 1
  simp only [PiLp.inner_apply,Fin.sum_univ_three,RCLike.inner_apply,conj_trivial,h0,h1,h2,mul_zero,add_zero]
  push_cast
  ring

omit [Fintype ι] in
theorem cosineJet_average (k r : ℝ) (y : ι → ℝ) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0) (θ : Sphere) :
    cosineJet k r y θ=(1/2 : ℂ) • (AngularScalarJets.planeJet k p θ+
      AngularScalarJets.planeJet k p (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ)) := by
  have ht0 : (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ).val 0= -θ.val 0 := by
    change HarmonicHalfTurn.rotation θ.val 0= -θ.val 0
    simp [HarmonicHalfTurn.rotation_apply,reflect,sign]
  have ht1 : (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ).val 1= -θ.val 1 := by
    change HarmonicHalfTurn.rotation θ.val 1= -θ.val 1
    simp [HarmonicHalfTurn.rotation_apply,reflect,sign]
  funext q
  rcases q with ⟨j,n⟩
  have hw := wave_on_plane k r y p h0 h1 h2 θ j
  have hw' := wave_on_plane k r y p h0 h1 h2 (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ) j
  simp only [ht0,ht1,mul_neg,Complex.ofReal_neg] at hw'
  have he : -((r : ℂ)*(k*θ.val 0 : ℝ)) + -((y j : ℂ)*(k*θ.val 1 : ℝ))=
      -((r : ℂ)*(k*θ.val 0 : ℝ)+(y j : ℂ)*(k*θ.val 1 : ℝ)) := by ring
  rw [he] at hw'
  fin_cases n <;> dsimp only [cosineJet,EdgeScalarInterpolation.scalarJet,AngularScalarJets.planeJet,Pi.smul_apply,Pi.add_apply]
  all_goals simp only [SphereWaveCalculus.coordinate,ht0,ht1,Complex.ofReal_neg,hw,hw',smul_eq_mul]
  all_goals simp only [Complex.cos,Complex.sin]
  all_goals push_cast
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals ring

end OQ14.AngularJetSymmetry
#print axioms OQ14.AngularJetSymmetry.scalarJet_neg
#print axioms OQ14.AngularJetSymmetry.cosineJet_continuous
#print axioms OQ14.AngularJetSymmetry.cosineJet_half_turn
#print axioms OQ14.AngularJetSymmetry.cosineJet_central
#print axioms OQ14.AngularJetSymmetry.wave_on_plane
#print axioms OQ14.AngularJetSymmetry.cosineJet_average
