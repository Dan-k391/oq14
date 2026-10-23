import VectorHarmonicSeparation
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Genuine normalized transverse Hilbert basis of the actual sphere vector space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.TransverseHarmonicBasis
open MeasureTheory OQ14.SphereHarmonicBasis OQ14.VectorHarmonicBasisSpan
open OQ14.VectorHarmonicSeparation OQ14.VectorHarmonicNormalization
open scoped RealInnerProductSpace

def radialSpace : Submodule ℝ VectorHarmonicSeparation.Ambient :=
  Submodule.span ℝ (Set.range (fun a => lift (radialField a)))
def transverseSpace := radialSpaceᗮ

instance : CompleteSpace transverseSpace := by
  change CompleteSpace ↥(radialSpaceᗮ)
  infer_instance

theorem mem_transverse_iff (F : VectorHarmonicSeparation.Ambient) :
    F∈transverseSpace ↔ ∀ a,⟪F,lift (radialField a)⟫=0 := by
  rw [transverseSpace,Submodule.mem_orthogonal']
  constructor
  · intro h a
    exact h _ (Submodule.subset_span ⟨a,rfl⟩)
  · intro h v hv
    induction hv using Submodule.span_induction with
    | mem v hv => obtain ⟨a,rfl⟩ := hv; exact h a
    | zero => simp
    | add v w hv hw ihv ihw => simp only [inner_add_right,ihv,ihw,add_zero]
    | smul a v hv ih => simp only [inner_smul_right,ih,mul_zero]

theorem tangential_mem (F : VectorHarmonicSeparation.Ambient) (hF : IsTangential F) :
    F∈transverseSpace := (mem_transverse_iff F).mpr (radial_moments_zero F hF)

theorem poloidal_tangent (a : Σ l,Index l) : IsTangential (lift (poloidalField a)) := by
  filter_upwards [(poloidalField a).coeFn_toLp (p := 2) (𝕜 := ℝ) angularMeasure] with n hn
  change lift (poloidalField a) n=poloidalField a n at hn
  rw [hn]
  have h := restriction_poloidal_tangent (representative a.1 a.2) a.1
    (representative_homogeneous a.1 a.2) n
  simpa only [poloidalField,VectorHarmonicSpan.vectorMap,PiLp.inner_apply,RCLike.inner_apply,
    conj_trivial,mul_comm] using h

theorem toroidal_tangent (a : Σ l,Index l) : IsTangential (lift (VectorHarmonicBasisSpan.toroidalField a)) := by
  filter_upwards [(VectorHarmonicBasisSpan.toroidalField a).coeFn_toLp (p := 2) (𝕜 := ℝ) angularMeasure] with n hn
  change lift (VectorHarmonicBasisSpan.toroidalField a) n=VectorHarmonicBasisSpan.toroidalField a n at hn
  rw [hn]
  have h := restriction_toroidal_tangent (representative a.1 a.2) n
  simpa only [VectorHarmonicBasisSpan.toroidalField,VectorHarmonicSpan.vectorMap,PolynomialVectorCalculus.tor_grad,
    PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm] using h

theorem polarized_mem (a : PositiveIndex ⊕ PositiveIndex) : polarized a∈transverseSpace := by
  cases a with
  | inl a => exact transverseSpace.smul_mem _ (tangential_mem _ (poloidal_tangent ⟨a.1+1,a.2⟩))
  | inr a => exact transverseSpace.smul_mem _ (tangential_mem _ (toroidal_tangent ⟨a.1+1,a.2⟩))

def vectors (a : PositiveIndex ⊕ PositiveIndex) : transverseSpace := ⟨polarized a,polarized_mem a⟩

theorem vectors_orthonormal : Orthonormal ℝ vectors := by
  rw [orthonormal_iff_ite]
  intro a b
  exact orthonormal_iff_ite.mp polarized_orthonormal a b

theorem vectors_orthogonal_eq_bot : (Submodule.span ℝ (Set.range vectors))ᗮ=⊥ := by
  apply eq_bot_iff.mpr
  intro F hF
  have hz : (F : VectorHarmonicSeparation.Ambient)=0 := by
    apply normalized_transverse_separate _ ((mem_transverse_iff _).mp F.property)
    · intro a
      have h := (Submodule.mem_orthogonal' _ _).mp hF (vectors (Sum.inl a))
        (Submodule.subset_span ⟨Sum.inl a,rfl⟩)
      exact h
    · intro a
      have h := (Submodule.mem_orthogonal' _ _).mp hF (vectors (Sum.inr a))
        (Submodule.subset_span ⟨Sum.inr a,rfl⟩)
      exact h
  exact Subtype.ext hz

def hilbertBasis : HilbertBasis (PositiveIndex ⊕ PositiveIndex) ℝ transverseSpace :=
  HilbertBasis.mkOfOrthogonalEqBot vectors_orthonormal vectors_orthogonal_eq_bot

theorem hilbertBasis_apply (a : PositiveIndex ⊕ PositiveIndex) : hilbertBasis a=vectors a := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot vectors_orthonormal vectors_orthogonal_eq_bot) a

theorem expansion (F : transverseSpace) :
    HasSum (fun a => ⟪vectors a,F⟫ • vectors a) F := by
  simpa only [HilbertBasis.repr_apply_apply,hilbertBasis_apply] using hilbertBasis.hasSum_repr F

theorem parseval (F : transverseSpace) :
    HasSum (fun a => ⟪vectors a,F⟫^2) (‖F‖^2) := by
  have h := hilbertBasis.hasSum_inner_mul_inner F F
  simpa only [hilbertBasis_apply,real_inner_comm,← sq,real_inner_self_eq_norm_sq] using h

end OQ14.TransverseHarmonicBasis

#print axioms OQ14.TransverseHarmonicBasis.mem_transverse_iff
#print axioms OQ14.TransverseHarmonicBasis.tangential_mem
#print axioms OQ14.TransverseHarmonicBasis.poloidal_tangent
#print axioms OQ14.TransverseHarmonicBasis.toroidal_tangent
#print axioms OQ14.TransverseHarmonicBasis.polarized_mem
#print axioms OQ14.TransverseHarmonicBasis.vectors_orthonormal
#print axioms OQ14.TransverseHarmonicBasis.vectors_orthogonal_eq_bot
#print axioms OQ14.TransverseHarmonicBasis.hilbertBasis_apply
#print axioms OQ14.TransverseHarmonicBasis.expansion
#print axioms OQ14.TransverseHarmonicBasis.parseval
