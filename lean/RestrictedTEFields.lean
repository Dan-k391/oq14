import RestrictedHarmonicInterpolation
import HalfTurnMaxwellParity

/-! Actual Maxwell fields of finite even-degree half-turn harmonic sums. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEFields
open Maxwell ModalDipole ExteriorClassical ExteriorHelmholtz HarmonicPolynomial
open RestrictedHarmonicInterpolation SymmetricHarmonicJets
abbrev Space := FourierL2.Space

theorem laplacian_const_mul (c : ℂ) (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space) :
    laplacian (fun y => c*f y) x=c*laplacian f x := by
  have hp (i : Fin 3) : (fun y => dcoord (fun z => c*f z) y i)=
      (fun y => c*dcoord f y i) :=
    funext (fun y => partial_const_mul (hf.contDiffAt.differentiableAt (by simp)) c i)
  unfold laplacian
  simp_rw [hp]
  simp_rw [partial_const_mul ((partial_smooth hf.contDiffAt _).differentiableAt (by simp))]
  exact (Finset.mul_sum _ _ _).symm

theorem scalar_helmholtz (k : ℝ) (q : Index) (x : Space) :
    laplacian (scalar k q) x+(k : ℂ)^2*scalar k q x=0 := by
  unfold scalar
  rw [laplacian_const_mul _ _ (SolidScalarHelmholtz.wave_contDiff _ _ _)]
  have h := SolidScalarHelmholtz.wave_helmholtz q.val.1 (k : ℂ)
    (EvenHarmonicProjection.project q.val.1 q.val.2)
    (EvenHarmonicProjection.homogeneous _ _ q.property.1)
    (EvenHarmonicProjection.harmonic _ _ q.property.2) x
  linear_combination ((4*Real.pi : ℂ)*Complex.I^q.val.1*(k : ℂ)^q.val.1)*h

def potential (k : ℝ) (A : Index →₀ ℂ) (x : Space) : ℂ := ∑ q ∈ A.support, A q*scalar k q x

theorem potential_smooth (k : ℝ) (A : Index →₀ ℂ) : ContDiff ℝ (⊤ : ℕ∞) (potential k A) := by
  apply ContDiff.sum
  intro q _
  exact contDiff_const.mul (scalar_contDiff k q)

theorem potential_helmholtz (k : ℝ) (A : Index →₀ ℂ) (x : Space) :
    laplacian (potential k A) x+(k : ℂ)^2*potential k A x=0 := by
  unfold potential
  rw [ScalarFiniteCalculus.laplacian_sum _ _ _ _ (fun q _ => scalar_contDiff k q)]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro q _
  linear_combination A q*(scalar_helmholtz k q x)

theorem potential_half_turn (k : ℝ) (A : Index →₀ ℂ) (x : Space) :
    potential k A (HalfTurnMaxwellParity.halfTurn x)=potential k A x := by
  unfold potential scalar
  have he : HalfTurnMaxwellParity.halfTurn x=HarmonicHalfTurn.rotation x := by
    rw [HalfTurnMaxwellParity.halfTurn_apply,HarmonicHalfTurn.rotation_apply]
  simp only [he,EvenHarmonicProjection.wave_invariant]

theorem potential_central_even (k : ℝ) (A : Index →₀ ℂ) (x : Space) :
    potential k A (-x)=potential k A x := by
  unfold potential scalar
  apply Finset.sum_congr rfl
  intro q _
  rw [EvenHarmonicProjection.wave_central_even _ _ q.property.1]

theorem maxwell (k : ℝ) (hk : k≠0) (A : Index →₀ ℂ) (x : Space) :
    MaxwellAt k 1 1 (DebyeMaxwell.teElectric (potential k A))
      (DebyeMaxwell.teMagnetic k (potential k A)) x := by
  apply DebyeMaxwell.te_real_maxwell isOpen_univ _ (fun y _ => (potential_smooth k A).contDiffAt)
    k k 1 hk (by ring) (fun y _ => potential_helmholtz k A y) x (Set.mem_univ x)

theorem electric_half_turn (k : ℝ) (A : Index →₀ ℂ) :
    HalfTurnMaxwellParity.Invariant (DebyeMaxwell.teElectric (potential k A)) :=
  HalfTurnMaxwellParity.toroidal_invariant _ (potential_smooth k A) (potential_half_turn k A)

end OQ14.RestrictedTEFields
#print axioms OQ14.RestrictedTEFields.laplacian_const_mul
#print axioms OQ14.RestrictedTEFields.scalar_helmholtz
#print axioms OQ14.RestrictedTEFields.potential_smooth
#print axioms OQ14.RestrictedTEFields.potential_helmholtz
#print axioms OQ14.RestrictedTEFields.potential_half_turn
#print axioms OQ14.RestrictedTEFields.potential_central_even
#print axioms OQ14.RestrictedTEFields.maxwell
#print axioms OQ14.RestrictedTEFields.electric_half_turn
