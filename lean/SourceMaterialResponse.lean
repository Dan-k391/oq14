import SourceWeightedDatum

/-! The literal layered source fields solve their actual square-root weighted material equation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceMaterialResponse
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction
open OQ14.SourceWeightedDatum

theorem scattered_actual (c : Coefficient) (d : Data)
    (hm : ∀ x : Space, (c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) :
    MaterialField.scattered c 1 (datum c d.X (material_outer c d hm) d p)=ᵐ[volume]
      SourceRegularCorrection.electric d p := by
  unfold MaterialField.scattered
  rw [sourceL2_eq c d hm p,
    MaterialVolumeConverse.response_source_congr 1 (SourceVolumeRepresentation.sourceL2 d p) _ _
      (source_actual c d hm p)]
  exact (SourceVolumeRepresentation.actual_response d hdisp p hp hh).1.symm

theorem volume_equation (c : Coefficient) (d : Data)
    (hm : ∀ x : Space, (c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) :
    DynamicVolume.volumeBlock c 1 d.X (datum c d.X (material_outer c d hm) d p)=
      datum c d.X (material_outer c d hm) (vacuum d) p := by
  apply MaterialVolumeConverse.volume_equation c 1 d.X _ _
    (SourceUnclippedMaxwell.electric d p) (SourceUnclippedMaxwell.electric (vacuum d) p)
    (material_outer c d hm) (actual c d.X _ d p (material_inner c d hm))
    (actual c d.X _ (vacuum d) p (material_inner c d hm))
  intro i
  filter_upwards [scattered_actual c d hm hdisp p hp hh,
    show ∀ᵐ x : Space, x≠0 from ae_iff.mpr (by simp)] with x hx hx0
  rw [hx,SourceRegularCorrection.electric_away d p hp hh x hx0]
  rfl

theorem inverse_solution (c : Coefficient) (d : Data)
    (hm : ∀ x : Space, (c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0)
    (hunit : IsUnit (DynamicVolume.volumeBlock c 1 d.X)) :
    datum c d.X (material_outer c d hm) d p=
      MaterialField.solution c 1 d.X (datum c d.X (material_outer c d hm) (vacuum d) p) :=
  MaterialVolumeConverse.inverse_solution c 1 d.X _ _ hunit (volume_equation c d hm hdisp p hp hh)

end OQ14.SourceMaterialResponse
#print axioms OQ14.SourceMaterialResponse.scattered_actual
#print axioms OQ14.SourceMaterialResponse.volume_equation
#print axioms OQ14.SourceMaterialResponse.inverse_solution
