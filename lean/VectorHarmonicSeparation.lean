import VectorHarmonicBasisSpan
import Mathlib.Analysis.InnerProductSpace.Projection

/-! Actual vector harmonic moments separate the genuine sphere L2 space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.VectorHarmonicSeparation
open MeasureTheory OQ14.SphereHarmonicBasis OQ14.VectorHarmonicBasisSpan
open scoped RealInnerProductSpace
abbrev Ambient := VectorHarmonicNormalization.VectorAmbient
abbrev lift : C(Sphere,OQ14.Maxwell.Space) →L[ℝ] Ambient := ContinuousMap.toLp 2 angularMeasure ℝ

theorem moments_separate (F : Ambient)
    (hR : ∀ a,⟪F,lift (radialField a)⟫=0)
    (hP : ∀ a,⟪F,lift (poloidalField a)⟫=0)
    (hT : ∀ a,⟪F,lift (toroidalField a)⟫=0) : F=0 := by
  apply Dense.eq_zero_of_inner_left basisL2Span_dense
  rintro ⟨v,hv⟩
  obtain ⟨f,hf,rfl⟩ := hv
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with (⟨a,rfl⟩ | ⟨a,rfl⟩) | ⟨a,rfl⟩
    · exact hR a
    · exact hP a
    · exact hT a
  | zero => simp
  | add f g hf hg ihf ihg => simp only [map_add,inner_add_right,ihf,ihg,add_zero]
  | smul a f hf ih => simp only [map_smul,inner_smul_right,ih,mul_zero]

theorem poloidal_zero (i : Index 0) : poloidalField ⟨0,i⟩=0 := by
  ext n j
  simp [poloidalField,VectorHarmonicSpan.vectorMap_apply,AngularHarmonicEnergy.tangential,
    HarmonicVectorConstants.partial_zero _ (representative_homogeneous 0 i)]

theorem toroidal_zero (i : Index 0) : toroidalField ⟨0,i⟩=0 := by
  have hz : PolynomialVectorCalculus.grad (representative 0 i)=0 := by
    funext j
    exact HarmonicVectorConstants.partial_zero _ (representative_homogeneous 0 i) j
  ext n j
  fin_cases j <;> simp [toroidalField,hz,VectorHarmonicSpan.vectorMap_apply,PolynomialVectorCalculus.tor]

theorem normalized_transverse_separate (F : Ambient)
    (hR : ∀ a,⟪F,lift (radialField a)⟫=0)
    (hP : ∀ a,⟪F,VectorHarmonicNormalization.normalizedP a⟫=0)
    (hT : ∀ a,⟪F,VectorHarmonicNormalization.normalizedT a⟫=0) : F=0 := by
  apply moments_separate F hR
  · rintro ⟨l,i⟩
    cases l with
    | zero => simp [poloidal_zero]
    | succ n =>
      have h := hP ⟨n,i⟩
      have hn : VectorHarmonicNormalization.normalizer n≠0 := by
        unfold VectorHarmonicNormalization.normalizer
        exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
      change ⟪F,VectorHarmonicNormalization.normalizer n • lift (poloidalField ⟨n+1,i⟩)⟫=0 at h
      rw [inner_smul_right] at h
      exact (mul_eq_zero.mp h).resolve_left hn
  · rintro ⟨l,i⟩
    cases l with
    | zero => simp [toroidal_zero]
    | succ n =>
      have h := hT ⟨n,i⟩
      have hn : VectorHarmonicNormalization.normalizer n≠0 := by
        unfold VectorHarmonicNormalization.normalizer
        exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
      change ⟪F,VectorHarmonicNormalization.normalizer n • lift (toroidalField ⟨n+1,i⟩)⟫=0 at h
      rw [inner_smul_right] at h
      exact (mul_eq_zero.mp h).resolve_left hn

theorem radialField_apply (a : Σ l,Index l) (n : Sphere) :
    radialField a n=angular a.1 a.2 n • (n : OQ14.Maxwell.Space) := by
  ext i
  simp [radialField,VectorHarmonicSpan.vectorMap_apply,PolynomialVectorCalculus.radial,
    angular,PiLp.smul_apply,mul_comm,SpherePolynomial.polynomialMap_apply]

def IsTangential (F : Ambient) : Prop :=
  ∀ᵐ (n : Sphere) ∂angularMeasure,⟪(n : OQ14.Maxwell.Space),F n⟫=0

theorem radial_moments_zero (F : Ambient) (hF : IsTangential F) (a : Σ l,Index l) :
    ⟪F,lift (radialField a)⟫=0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hF,(radialField a).coeFn_toLp (p := 2) (𝕜 := ℝ) angularMeasure] with n hn he
  change lift (radialField a) n=radialField a n at he
  rw [he,radialField_apply,inner_smul_right,real_inner_comm,hn,mul_zero]
  rfl

theorem tangential_moments_separate (F : Ambient) (hF : IsTangential F)
    (hP : ∀ a,⟪F,VectorHarmonicNormalization.normalizedP a⟫=0)
    (hT : ∀ a,⟪F,VectorHarmonicNormalization.normalizedT a⟫=0) : F=0 :=
  normalized_transverse_separate F (radial_moments_zero F hF) hP hT

end OQ14.VectorHarmonicSeparation

#print axioms OQ14.VectorHarmonicSeparation.moments_separate
#print axioms OQ14.VectorHarmonicSeparation.poloidal_zero
#print axioms OQ14.VectorHarmonicSeparation.toroidal_zero
#print axioms OQ14.VectorHarmonicSeparation.normalized_transverse_separate
#print axioms OQ14.VectorHarmonicSeparation.radialField_apply
#print axioms OQ14.VectorHarmonicSeparation.radial_moments_zero
#print axioms OQ14.VectorHarmonicSeparation.tangential_moments_separate
