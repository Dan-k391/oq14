import SymmetricHarmonicJets
import SphereFrequencyLift

/-! Finite interpolation by actual even-degree half-turn-projected harmonic waves. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedHarmonicInterpolation
open Maxwell HarmonicPolynomial SphereReactionKernel SphereWaveCalculus SymmetricHarmonicJets
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

theorem dual_zero (k : ℝ) (hk : 0<k) (r : ℝ) (hr : r≠0)
    (y : ι → ℝ) (hy : Function.Injective y) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0)
    (L : EdgeScalarInterpolation.Jet ι →ₗ[ℂ] ℂ)
    (hz : ∀ q : Index, L (generator k p q)=0) : L=0 := by
  apply EdgeScalarInterpolation.dual_zero r hr y hy (k/3) (by positivity) L
  intro s t hs hs' ht ht'
  obtain ⟨θ,hθ0,hθ1⟩ := SphereFrequencyLift.rectangle_direction k hk s t (by linarith) hs' (by linarith) ht'
  have h := annihilator_cosine k r y p h0 h1 h2 L hz θ
  simpa only [AngularJetSymmetry.cosineJet,← Complex.ofReal_mul,hθ0,hθ1] using h

theorem span_top (k : ℝ) (hk : 0<k) (r : ℝ) (hr : r≠0)
    (y : ι → ℝ) (hy : Function.Injective y) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0) :
    Submodule.span ℂ (Set.range (generator k p))=⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro L hL
  apply dual_zero k hk r hr y hy p h0 h1 h2 L
  intro q
  exact (Submodule.mem_dualAnnihilator _).mp hL _
    (Submodule.subset_span (Set.mem_range.mpr ⟨q,rfl⟩))

theorem finite_interpolant (k : ℝ) (hk : 0<k) (r : ℝ) (hr : r≠0)
    (y : ι → ℝ) (hy : Function.Injective y) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0)
    (v : EdgeScalarInterpolation.Jet ι) :
    ∃ A : Index →₀ ℂ, Finsupp.linearCombination ℂ (generator k p) A=v := by
  apply Finsupp.mem_span_range_iff_exists_finsupp.mp
  rw [span_top k hk r hr y hy p h0 h1 h2]
  trivial

def scalar (k : ℝ) (q : Index) (x : Space) : ℂ :=
  (4*Real.pi : ℂ)*Complex.I^q.val.1*(k : ℂ)^q.val.1*
    SolidScalarHelmholtz.wave q.val.1 k (EvenHarmonicProjection.project q.val.1 q.val.2) x

theorem moment_eq_scalar (k : ℝ) (q : Index) : moment (amplitude q) k=scalar k q := by
  funext x
  exact ScalarPlaneWaveMoment.positive_moment q.val.1 _
    (EvenHarmonicProjection.homogeneous _ _ q.property.1)
    (EvenHarmonicProjection.harmonic _ _ q.property.2) k x

theorem scalar_contDiff (k : ℝ) (q : Index) : ContDiff ℝ (⊤ : ℕ∞) (scalar k q) :=
  contDiff_const.mul (SolidScalarHelmholtz.wave_contDiff _ _ _)

theorem finite_scalar_interpolant (k : ℝ) (hk : 0<k) (r : ℝ) (hr : r≠0)
    (y : ι → ℝ) (hy : Function.Injective y) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0)
    (v : EdgeScalarInterpolation.Jet ι) :
    ∃ A : Index →₀ ℂ, SymmetricScalarJets.jet (fun x => ∑ q ∈ A.support, A q*scalar k q x) p=v := by
  obtain ⟨A,hA⟩ := finite_interpolant k hk r hr y hy p h0 h1 h2 v
  refine ⟨A,?_⟩
  rw [ScalarFiniteCalculus.jet_sum _ _ _ _ (fun q _ => scalar_contDiff k q)]
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,generator,moment_eq_scalar] at hA
  exact hA

end OQ14.RestrictedHarmonicInterpolation
#print axioms OQ14.RestrictedHarmonicInterpolation.dual_zero
#print axioms OQ14.RestrictedHarmonicInterpolation.span_top
#print axioms OQ14.RestrictedHarmonicInterpolation.finite_interpolant
#print axioms OQ14.RestrictedHarmonicInterpolation.moment_eq_scalar
#print axioms OQ14.RestrictedHarmonicInterpolation.scalar_contDiff
#print axioms OQ14.RestrictedHarmonicInterpolation.finite_scalar_interpolant
