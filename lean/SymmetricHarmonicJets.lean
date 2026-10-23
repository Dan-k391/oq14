import AngularJetSymmetry
import HarmonicProjectedMoments

/-! Actual projected harmonic Herglotz jets and their angular test functionals. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SymmetricHarmonicJets
open MeasureTheory Maxwell HarmonicPolynomial SphereReactionKernel SphereWaveCalculus
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

def Index := {q : ℕ × Poly // q.2.IsHomogeneous q.1 ∧ formalLaplacian q.2=0}

def amplitude (q : Index) : Sphere → ℂ :=
  SphericalMomentEquation.angularPolynomial (EvenHarmonicProjection.project q.val.1 q.val.2)

def generator (k : ℝ) (p : ι → Space) (q : Index) : EdgeScalarInterpolation.Jet ι :=
  SymmetricScalarJets.jet (moment (amplitude q) k) p

omit [Fintype ι] in
theorem amplitude_symmetry (q : Index) (θ : Sphere) :
    amplitude q (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ)=amplitude q θ := by
  change (complexEvaluate _ (HarmonicHalfTurn.rotation θ.val))=complexEvaluate _ θ.val
  simp only [complexEvaluate,EvenHarmonicProjection.invariant]

theorem functional_generator (k r : ℝ) (y : ι → ℝ) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0)
    (L : EdgeScalarInterpolation.Jet ι →ₗ[ℂ] ℂ) (q : Index) :
    L (generator k p q)=∫ θ, amplitude q θ*L (AngularJetSymmetry.cosineJet k r y θ) ∂surface := by
  let a := amplitude q
  have ha : Continuous a := SphericalMomentEquation.angularPolynomial_continuous _
  have hA (θ : Sphere) : ‖a θ‖≤‖SpherePolynomial.polynomialMap (EvenHarmonicProjection.project q.val.1 q.val.2)‖ := by
    simpa only [a,amplitude,SphericalMomentEquation.angularPolynomial,complexEvaluate,evaluate,
      Complex.norm_real,SpherePolynomial.polynomialMap_apply] using
      (SpherePolynomial.polynomialMap (EvenHarmonicProjection.project q.val.1 q.val.2)).norm_coe_le_norm θ
  have hc := L.toContinuousLinearMap.continuous.comp (AngularScalarJets.planeJet_continuous k p)
  have hi : Integrable (fun θ => a θ*L (AngularScalarJets.planeJet k p θ)) surface :=
    (ha.mul hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hit : Integrable (fun θ => a θ*L (AngularScalarJets.planeJet k p
      (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ))) surface :=
    (ha.mul (hc.comp (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs := HarmonicProjectedMoments.integral_twist HarmonicHalfTurn.rotation a
    (fun θ => L (AngularScalarJets.planeJet k p θ)) (amplitude_symmetry q)
  rw [generator,AngularScalarJets.functional_moment _ ha _ hA]
  symm
  calc
    _ = (1/2 : ℂ)*(∫ θ, a θ*L (AngularScalarJets.planeJet k p θ)+
        a θ*L (AngularScalarJets.planeJet k p (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ)) ∂surface) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with θ
      rw [AngularJetSymmetry.cosineJet_average k r y p h0 h1 h2,map_smul,map_add]
      change a θ*((1/2 : ℂ)*_)=_
      ring
    _ = _ := by rw [integral_add hi hit,hs]; ring

theorem annihilator_cosine (k r : ℝ) (y : ι → ℝ) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0)
    (L : EdgeScalarInterpolation.Jet ι →ₗ[ℂ] ℂ)
    (hz : ∀ q : Index, L (generator k p q)=0) :
    ∀ θ, L (AngularJetSymmetry.cosineJet k r y θ)=0 := by
  apply HarmonicProjectedMoments.zero_of_projected_moments
    (fun θ => L (AngularJetSymmetry.cosineJet k r y θ))
    (L.toContinuousLinearMap.continuous.comp (AngularJetSymmetry.cosineJet_continuous k r y))
    (fun θ => congrArg L (AngularJetSymmetry.cosineJet_half_turn k r y θ))
    (fun θ => congrArg L (AngularJetSymmetry.cosineJet_central k r y θ))
  intro l q hq hh
  have h := (functional_generator k r y p h0 h1 h2 L ⟨(l,q),hq,hh⟩).symm.trans (hz ⟨(l,q),hq,hh⟩)
  simpa only [amplitude,SphericalMomentEquation.angularPolynomial,complexEvaluate,
    SpherePolynomial.polynomialMap_apply,evaluate,mul_comm] using h

end OQ14.SymmetricHarmonicJets
#print axioms OQ14.SymmetricHarmonicJets.amplitude_symmetry
#print axioms OQ14.SymmetricHarmonicJets.functional_generator
#print axioms OQ14.SymmetricHarmonicJets.annihilator_cosine
