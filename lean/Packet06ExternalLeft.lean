import Packet06ExternalResidue
import Packet06Cokernel
import Packet06PhysicalNormalization
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ExternalLeft
open Filter Metric Packet06SectorOperator Packet06MaterialSector
open KernelReciprocity ComplexVolumeReciprocity
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

def physicalLeft (c : StaticCoefficient.Coefficient) (u : Sector) : Sector →L[ℂ] ℂ :=
  (pairFunctional (u : VectorL2)).comp ((StaticNewton.volumeBlock c).comp Sector.subtypeL)

theorem physicalLeft_annihilates (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S : ℝ) (hS : 0 ≤ S)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : Sector) (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (v : Sector) :
    physicalLeft c u (pencil c S z v) = 0 := by
  change vectorPair (StaticNewton.volumeBlock c ((pencil c S z v : Sector) : VectorL2)) u = 0
  rw [pencil_actual c ha hm S hS hc z v, ← ContinuousLinearMap.mul_apply,
    ← ComplexConvolutionAnalytic.volumeBlock_factor]
  rw [ComplexVolumeReciprocity.volumeBlock_reciprocity c S hS z v u,hu]
  simp [vectorPair,scalarPair]

/-- Rank-one residues with a genuine left annihilator have its canonical
normalization, independently of the Schur repair chosen to compute them. -/
theorem left_ratio {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A A₁ G R : E →L[ℂ] E) (φ ℓ : E →L[ℂ] ℂ) (u : E)
    (hℓ : ℓ (A₁ u) ≠ 0)
    (hann : ∀ x, ℓ (A x) = 0)
    (hres : ∀ x, R x = (φ x / φ (A₁ u)) • u)
    (hconstant : A.comp G + A₁.comp R = 1) (v : E) :
    φ v / φ (A₁ u) = ℓ v / ℓ (A₁ u) := by
  have he := congrArg (fun L : E →L[ℂ] E => ℓ (L v)) hconstant
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.one_apply,map_add,hann,zero_add,hres,map_smul,smul_eq_mul] at he
  apply (eq_div_iff hℓ).2
  exact he

/-- The static preconditioner cancels exactly when differentiating the actual
sector pencil, so its left crossing is the physical volume derivative. -/
theorem physicalLeft_crossing (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S : ℝ) (hS : 0 ≤ S)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : Sector) :
    physicalLeft c u (deriv (pencil c S) z u) =
      vectorPair (deriv (fun w => ComplexConvolutionAnalytic.volumeBlock c w S) z u) u := by
  have he (w : ℂ) : StaticNewton.volumeBlock c ((pencil c S w u : Sector) : VectorL2) =
      ComplexConvolutionAnalytic.volumeBlock c w S u := by
    rw [pencil_actual c ha hm S hS hc w u, ← ContinuousLinearMap.mul_apply,
      ← ComplexConvolutionAnalytic.volumeBlock_factor]
  have hp := (pencil_analyticAt c S hS z).differentiableAt.hasDerivAt.clm_apply
    (hasDerivAt_const z u)
  have hp' : HasDerivAt (fun w : ℂ => pencil c S w u) (deriv (pencil c S) z u) z := by
    simpa only [map_zero,add_zero] using hp
  let L : Sector →L[ℂ] VectorL2 := (StaticNewton.volumeBlock c).comp Sector.subtypeL
  have hl := L.hasFDerivAt.comp_hasDerivAt z hp'
  have hl' : HasDerivAt (fun w : ℂ => ComplexConvolutionAnalytic.volumeBlock c w S u)
      (L (deriv (pencil c S) z u)) z := by
    convert hl using 1
    funext w
    exact (he w).symm
  have hv := ((ComplexConvolutionAnalytic.volumeBlock_differentiable c S hS z).hasDerivAt.clm_apply
    (hasDerivAt_const z (u : VectorL2)))
  have hv' : HasDerivAt (fun w : ℂ => ComplexConvolutionAnalytic.volumeBlock c w S u)
      (deriv (fun w => ComplexConvolutionAnalytic.volumeBlock c w S) z u) z := by
    simpa only [map_zero,add_zero] using hv
  change vectorPair (L (deriv (pencil c S) z u)) u = _
  rw [hl'.unique hv']

#print axioms OQ14.Packet06ExternalLeft.physicalLeft_crossing
#print axioms OQ14.Packet06ExternalLeft.physicalLeft_annihilates
#print axioms OQ14.Packet06ExternalLeft.left_ratio
end OQ14.Packet06ExternalLeft
