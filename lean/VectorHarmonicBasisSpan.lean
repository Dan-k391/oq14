import VectorHarmonicDensity

/-! Actual constructed scalar harmonic representatives generate the vector sectors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.VectorHarmonicBasisSpan
open MvPolynomial OQ14.HarmonicPolynomial OQ14.PolynomialVectorCalculus
open OQ14.SphereHarmonicBasis OQ14.VectorHarmonicSpan

def gradLinear : Poly →ₗ[ℝ] Vec where
  toFun := grad
  map_add' p q := by funext i; simp [grad]
  map_smul' a p := by funext i; simp [grad]

def radialLinear : Poly →ₗ[ℝ] Vec where
  toFun := radial
  map_add' p q := by funext i; simp [radial,mul_add]
  map_smul' a p := by funext i; simp [radial,Algebra.mul_smul_comm]

def torLinear : Vec →ₗ[ℝ] Vec where
  toFun := tor
  map_add' Q V := by funext i; fin_cases i <;> simp [tor] <;> ring
  map_smul' a Q := by
    funext i
    change tor (fun j => a • Q j) i=a • tor Q i
    simpa only [smul_eq_C_mul] using tor_Cmul a Q i

def radialField (a : Σ l,Index l) := vectorMap (radial (representative a.1 a.2))
def poloidalField (a : Σ l,Index l) :=
  vectorMap (AngularHarmonicEnergy.tangential (representative a.1 a.2) a.1)
def toroidalField (a : Σ l,Index l) := vectorMap (tor (grad (representative a.1 a.2)))

def basisSpan : Submodule ℝ C(Sphere,OQ14.Maxwell.Space) :=
  Submodule.span ℝ (Set.range radialField ∪ Set.range poloidalField ∪ Set.range toroidalField)

theorem radialField_mem (a : Σ l,Index l) : radialField a∈basisSpan :=
  Submodule.subset_span (Or.inl (Or.inl ⟨a,rfl⟩))

theorem poloidalField_mem (a : Σ l,Index l) : poloidalField a∈basisSpan :=
  Submodule.subset_span (Or.inl (Or.inr ⟨a,rfl⟩))

theorem toroidalField_mem (a : Σ l,Index l) : toroidalField a∈basisSpan :=
  Submodule.subset_span (Or.inr ⟨a,rfl⟩)

theorem gradField_mem (a : Σ l,Index l) : vectorMap (grad (representative a.1 a.2))∈basisSpan := by
  have he : vectorMap (grad (representative a.1 a.2))=
      poloidalField a+(a.1 : ℝ) • radialField a := by
    simp only [poloidalField,radialField,← map_add,← map_smul]
    congr 1
    funext i
    simp [grad,radial,AngularHarmonicEnergy.tangential]
  rw [he]
  exact basisSpan.add_mem (poloidalField_mem a) (basisSpan.smul_mem _ (radialField_mem a))

theorem linear_image_mem (L : Poly →ₗ[ℝ] C(Sphere,OQ14.Maxwell.Space))
    (hL : ∀ a : Σ l,Index l,L (representative a.1 a.2)∈basisSpan)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) : L p∈basisSpan := by
  have he := HarmonicPolynomialRestriction.representative_expansion l ⟨p,hp,hh⟩
  dsimp only at he
  rw [he,map_sum]
  apply basisSpan.sum_mem
  intro i _
  rw [map_smul]
  exact basisSpan.smul_mem _ (hL ⟨l,i⟩)

theorem sectorSpan_le : sectorSpan≤basisSpan := by
  apply Submodule.span_le.mpr
  rintro f ⟨l,p,hp,hh,hf⟩
  rcases hf with rfl | rfl | rfl
  · exact linear_image_mem (vectorMap.comp gradLinear) gradField_mem p l hp hh
  · exact linear_image_mem (vectorMap.comp radialLinear) radialField_mem p l hp hh
  · exact linear_image_mem (vectorMap.comp (torLinear.comp gradLinear)) toroidalField_mem p l hp hh

theorem basisSpan_dense : Dense (basisSpan : Set C(Sphere,OQ14.Maxwell.Space)) :=
  VectorHarmonicDensity.sectorSpan_dense.mono sectorSpan_le

def basisL2Span : Submodule ℝ VectorHarmonicNormalization.VectorAmbient :=
  basisSpan.map (ContinuousMap.toLp 2 angularMeasure ℝ).toLinearMap

theorem basisL2Span_dense : Dense (basisL2Span : Set VectorHarmonicNormalization.VectorAmbient) := by
  change Dense ((ContinuousMap.toLp 2 angularMeasure ℝ) '' (basisSpan : Set C(Sphere,OQ14.Maxwell.Space)))
  exact (ContinuousMap.toLp_denseRange OQ14.Maxwell.Space angularMeasure ℝ (p := 2) (by norm_num)).dense_image
    (ContinuousMap.toLp 2 angularMeasure ℝ).continuous basisSpan_dense

end OQ14.VectorHarmonicBasisSpan

#print axioms OQ14.VectorHarmonicBasisSpan.radialField_mem
#print axioms OQ14.VectorHarmonicBasisSpan.poloidalField_mem
#print axioms OQ14.VectorHarmonicBasisSpan.toroidalField_mem
#print axioms OQ14.VectorHarmonicBasisSpan.gradField_mem
#print axioms OQ14.VectorHarmonicBasisSpan.linear_image_mem
#print axioms OQ14.VectorHarmonicBasisSpan.sectorSpan_le
#print axioms OQ14.VectorHarmonicBasisSpan.basisSpan_dense
#print axioms OQ14.VectorHarmonicBasisSpan.basisL2Span_dense
