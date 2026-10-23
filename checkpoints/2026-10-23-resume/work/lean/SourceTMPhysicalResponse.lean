import SourceMaterialResponse
import SourceMaterialPartition
import SourceCoreVolumeIntegral

/-! Fully instantiated finite-stack TM source response, with actual material inverse and core integral. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceTMPhysicalResponse
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction
open OQ14.SourceMaterialCoefficient OQ14.SourceWeightedDatum

def weighted (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (p : HarmonicPolynomial.Poly) : VectorFourier.VectorL2 :=
  datum (coefficient d M hM hs) d.X (material_outer _ d (value_complex d M hM hs)) d p

def incident (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (p : HarmonicPolynomial.Poly) : VectorFourier.VectorL2 :=
  datum (coefficient d M hM hs) d.X (material_outer _ d (value_complex d M hM hs)) (vacuum d) p

theorem inverse_actual (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) :
    MaterialField.solution (coefficient d M hM hs) 1 d.X (incident d M hM hs p)=weighted d M hM hs p :=
  (SourceMaterialResponse.inverse_solution _ d (value_complex d M hM hs) hdisp p hp hh
    (SourceMaterialPartition.volumeBlock_isUnit d M hM hs 1 (by norm_num))).symm

theorem polarization_actual (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) (i : Fin 3) :
    DynamicVolume.source (coefficient d M hM hs)
      (MaterialField.solution (coefficient d M hM hs) 1 d.X (incident d M hM hs p)) i
      =ᵐ[volume] SourceRegularCorrection.polarization d p i := by
  rw [inverse_actual d M hM hs hdisp p hp hh]
  exact source_actual _ d (value_complex d M hM hs) p i

theorem core_integral (d : Data) (M : ℝ) (hM : 1≤M) (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) (x : Space) (hx : ‖x‖<d.R) (i : Fin 3) :
    (∑ j : Fin 3, ∫ y : Space, DynamicVolume.source (coefficient d M hM hs)
      (MaterialField.solution (coefficient d M hM hs) 1 d.X (incident d M hM hs p)) j y*
        DyadicKernel.dyadic 1 (x-y) i j)=multiplier d*SolidMaxwellProfiles.electric d.l p x i := by
  rw [←SourceCoreVolumeIntegral.integral_core d hdisp p hp hh x hx i]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [polarization_actual d M hM hs hdisp p hp hh j] with y hy
  rw [hy]

end OQ14.SourceTMPhysicalResponse
#print axioms OQ14.SourceTMPhysicalResponse.inverse_actual
#print axioms OQ14.SourceTMPhysicalResponse.polarization_actual
#print axioms OQ14.SourceTMPhysicalResponse.core_integral
