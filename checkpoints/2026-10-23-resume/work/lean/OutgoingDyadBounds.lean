import VacuumOutgoingBounds
import DebyeJetBounds
import VectorReactionTerms

/-! Genuine signed free-source dyad estimates, uniform on an exterior and source compact. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.OutgoingDyadBounds
open OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open OQ14.DebyeUnitReaction OQ14.FreeSourceCoefficients OQ14.AngularExteriorBounds

theorem weight_norm_le (a : PositiveIndex) : ‖weight a‖≤1 := by
  have he : weight a=(VectorReactionTerms.angularWeight (a.1+1) : ℂ) := by
    simp only [weight,VectorReactionTerms.angularWeight,Complex.ofReal_inv,Complex.ofReal_mul,
      Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,Nat.cast_add,Nat.cast_one]
    congr 1
    ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (VectorReactionTerms.angularWeight_bounds (a.1+1)).1]
  exact (VectorReactionTerms.angularWeight_bounds (a.1+1)).2

theorem regular_coefficient_bound (a : PositiveIndex) (b B : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (y : Space) (hy : ‖y‖≤b) (j : Fin 3) :
    ‖tmCoefficient a y j‖≤DebyeJetBounds.scale 0 b*RiccatiSeriesCoefficients.amplitude (a.1+1) 0*
      (a.1+2 : ℝ)^3*B^(a.1+1) ∧
    ‖teCoefficient a y j‖≤DebyeJetBounds.scale 0 b*RiccatiSeriesCoefficients.amplitude (a.1+1) 0*
      (a.1+2 : ℝ)^3*B^(a.1+1) := by
  have h := DebyeJetBounds.normalized_vector_jet_bound (a.1+1) a.2 0 0 le_rfl b B hb hB hscale y hy j
  simp only [norm_iteratedFDeriv_zero] at h
  constructor
  · rw [tmCoefficient,norm_mul,norm_neg]
    apply (mul_le_mul_of_nonneg_right (weight_norm_le a) (norm_nonneg _)).trans
    simpa only [one_mul,electric,Nat.cast_add,Nat.cast_one,add_assoc,show (1 : ℝ)+1=2 by norm_num] using h.2
  · rw [teCoefficient,norm_mul,norm_mul,norm_neg,Complex.norm_I,one_mul]
    apply (mul_le_mul_of_nonneg_right (weight_norm_le a) (norm_nonneg _)).trans
    simpa only [one_mul,toroidal,Nat.cast_add,Nat.cast_one,add_assoc,show (1 : ℝ)+1=2 by norm_num] using h.1

def tmWeighted (a : PositiveIndex) (r : ℝ) (n : Sphere) (y : Space) (i j : Fin 3) : ℂ :=
  tmCoefficient a y j*SourceFarAmplitude.electricWeighted (VacuumOutgoingBounds.data (a.1+1))
    (representative (a.1+1) a.2) (r • (n : Space)) i
def teWeighted (a : PositiveIndex) (r : ℝ) (n : Sphere) (y : Space) (i j : Fin 3) : ℂ :=
  teCoefficient a y j*SourceFarAmplitude.magneticWeighted (VacuumOutgoingBounds.data (a.1+1))
    (representative (a.1+1) a.2) (r • (n : Space)) i

theorem tm_radial_bound (a : PositiveIndex) (b B r : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hr : 1<r)
    (n : Sphere) (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    ‖tmWeighted a r n y i j‖≤DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*
      (a.1+2 : ℝ)^8*(RiccatiSeriesCoefficients.amplitude (a.1+1) 0*(B*base)^(a.1+1)*
        (‖ModalAlgebra.xiD (a.1+1) r‖+‖ModalAlgebra.xi (a.1+1) r‖)) := by
  have hreg := (regular_coefficient_bound a b B hb hB hscale y hy j).1
  have hout := VacuumOutgoingBounds.electric_weighted_bound (a.1+1) a.2 n r hr i
  rw [tmWeighted,norm_mul]
  apply (mul_le_mul hreg hout (norm_nonneg _) (by
    have h := DebyeJetBounds.scale_nonnegative 0 b hb
    have h' := (RiccatiSeriesCoefficients.amplitude_pos (a.1+1) 0).le
    positivity)).trans_eq
  simp only [envelope,Nat.cast_add,Nat.cast_one,mul_pow]
  ring

theorem te_radial_bound (a : PositiveIndex) (b B r : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hr : 1<r)
    (n : Sphere) (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    ‖teWeighted a r n y i j‖≤2*DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*
      (a.1+2 : ℝ)^6*(RiccatiSeriesCoefficients.amplitude (a.1+1) 0*(B*base)^(a.1+1)*
        ‖ModalAlgebra.xi (a.1+1) r‖) := by
  have hreg := (regular_coefficient_bound a b B hb hB hscale y hy j).2
  have hout := VacuumOutgoingBounds.magnetic_weighted_bound (a.1+1) a.2 n r hr i
  rw [teWeighted,norm_mul]
  apply (mul_le_mul hreg hout (norm_nonneg _) (by
    have h := DebyeJetBounds.scale_nonnegative 0 b hb
    have h' := (RiccatiSeriesCoefficients.amplitude_pos (a.1+1) 0).le
    positivity)).trans_eq
  simp only [envelope,Nat.cast_add,Nat.cast_one,mul_pow]
  ring

end OQ14.OutgoingDyadBounds

#print axioms OQ14.OutgoingDyadBounds.weight_norm_le
#print axioms OQ14.OutgoingDyadBounds.regular_coefficient_bound
#print axioms OQ14.OutgoingDyadBounds.tm_radial_bound
#print axioms OQ14.OutgoingDyadBounds.te_radial_bound
