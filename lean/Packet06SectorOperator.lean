import Packet04KernelClassification
import VolumeAnalyticAlternative
import ModalMeridionalVolume
import Mathlib.Analysis.InnerProductSpace.Projection

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SectorOperator
open Complex MeasureTheory Set Filter OQ14.ModalMeridionalReflection OQ14.ModalWeightedMode
open scoped Topology
abbrev Sector := ModalMeridionalReflection.electricSector
abbrev VectorL2 := VectorFourier.VectorL2
instance : CompleteSpace Sector := electricSector_closed.completeSpace_coe

def block (n : ℝ) (hn : 1 < n) (z : ℂ) : Sector →L[ℂ] Sector :=
  ((ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1).comp Sector.subtypeL).codRestrict
    Sector (fun u => ModalMeridionalVolume.electricSector_invariant n hn z u u.property)

theorem block_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (u : Sector) :
    ((block n hn z u : Sector) : VectorL2) =
      ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u := rfl

def numerator (n : ℝ) (hn : 1 < n) (z : ℂ) : Sector :=
  ⟨ModalVolumeData.numerator n hn z, numerator_in_electricSector n hn z⟩

theorem numerator_kernel (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) :
    numerator n hn z ≠ 0 ∧ block n hn z (numerator n hn z) = 0 := by
  have h := ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hd
  exact ⟨fun he => h.1 (congrArg Subtype.val he), Subtype.ext h.2⟩

theorem kernel_iff_unique_multiple (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (u : Sector) :
    block n hn z u = 0 ↔ ∃! c : ℂ, u = c • numerator n hn z := by
  have hh := Packet04KernelClassification.kernel_iff_unique_multiple n hn hna z hz hd u.val
  constructor
  · intro hu
    obtain ⟨c,hc,huniq⟩ := hh.mp ⟨u.property, congrArg Subtype.val hu⟩
    exact ⟨c,Subtype.ext hc,fun d hd => huniq d (congrArg Subtype.val hd)⟩
  · rintro ⟨c,hc,_⟩
    rw [hc, map_smul, (numerator_kernel n hn z hz hd).2, smul_zero]

theorem kernel_eq_span (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) :
    LinearMap.ker (block n hn z).toLinearMap = Submodule.span ℂ {numerator n hn z} := by
  ext u
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hu
    obtain ⟨c,hc,_⟩ := (kernel_iff_unique_multiple n hn hna z hz hd u).mp hu
    exact ⟨c,hc.symm⟩
  · rintro ⟨c,rfl⟩
    change block n hn z (c • numerator n hn z) = 0
    simp only [map_smul,(numerator_kernel n hn z hz hd).2,smul_zero]

theorem kernel_finrank_one (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) :
    Module.finrank ℂ (LinearMap.ker (block n hn z).toLinearMap) = 1 := by
  rw [kernel_eq_span n hn hna z hz hd]
  exact finrank_span_singleton (numerator_kernel n hn z hz hd).1

theorem block_not_isUnit (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) : ¬ IsUnit (block n hn z) := by
  intro hu
  obtain ⟨hne,hker⟩ := numerator_kernel n hn z hz hd
  have hh := congrArg (fun L : Sector →L[ℂ] Sector => L (numerator n hn z))
    (Ring.inverse_mul_cancel (block n hn z) hu)
  change Ring.inverse (block n hn z) (block n hn z (numerator n hn z)) = numerator n hn z at hh
  rw [hker, map_zero] at hh
  exact hne hh.symm

/-- Orthogonal compression of the actual ambient meromorphic inverse. -/
def compressedInverse (n : ℝ) (hn : 1 < n) (z : ℂ) : Sector →L[ℂ] Sector :=
  Sector.orthogonalProjection.comp
    ((Ring.inverse (ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1)).comp Sector.subtypeL)

theorem compressedInverse_meromorphicAt (n : ℝ) (hn : 1 < n) (z₀ : ℂ) :
    MeromorphicAt (compressedInverse n hn) z₀ := by
  have hi := VolumeAnalyticAlternative.inverse_meromorphicAt (coefficient n hn) 1 (by norm_num)
    (coefficient_support n hn) z₀
  have h1 := MeromorphicOperator.clm_comp
    (fun z : ℂ => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1))
    (fun _ : ℂ => Sector.subtypeL) z₀ hi (MeromorphicAt.const Sector.subtypeL z₀)
  exact MeromorphicOperator.clm_comp (fun _ : ℂ => Sector.orthogonalProjection) _ z₀
    (MeromorphicAt.const Sector.orthogonalProjection z₀) h1

/-- Invertibility and actual rotation/reflection commutation force the ambient
inverse to preserve the electric sector. -/
theorem ambient_inverse_mem_sector (n : ℝ) (hn : 1 < n) (z : ℂ)
    (hu : IsUnit (ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1))
    (v : VectorL2) (hv : v ∈ Sector) :
    Ring.inverse (ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1) v ∈ Sector := by
  let A := ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1
  let w := Ring.inverse A v
  have hleft : Ring.inverse A * A = 1 := Ring.inverse_mul_cancel A hu
  have hright : A * Ring.inverse A = 1 := Ring.mul_inverse_cancel A hu
  have hAv : A w = v := by
    have h := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L v) hright
    simpa [w] using h
  have hinj : Function.Injective A := by
    intro x y he
    have hh := congrArg (fun q : VectorL2 => Ring.inverse A q) he
    have hl (q : VectorL2) : Ring.inverse A (A q) = q := by
      have h := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L q) hleft
      simpa using h
    simpa only [hl] using hh
  have hrot : ∀ θ : ℝ, ModalAxialRotation.action θ v = v := by
    have h := hv.1
    change v ∈ ModalAxialRotation.axialSector at h
    simp only [ModalAxialRotation.axialSector, Submodule.mem_iInf, LinearMap.mem_ker,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero] at h
    exact h
  have href : ModalMeridionalReflection.action v = v := by
    have h := hv.2
    change (ModalMeridionalReflection.action - 1) v = 0 at h
    simpa using sub_eq_zero.mp h
  have hrotw : w ∈ ModalAxialRotation.axialSector := by
    simp only [ModalAxialRotation.axialSector, Submodule.mem_iInf, LinearMap.mem_ker,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero]
    intro θ
    apply hinj
    have hc := congrFun (congrArg DFunLike.coe (ModalAxialVolume.complex_comm n hn θ z)) w
    change ModalAxialRotation.action θ (A w) = A (ModalAxialRotation.action θ w) at hc
    calc
      A (ModalAxialRotation.action θ w) = ModalAxialRotation.action θ (A w) := hc.symm
      _ = v := by rw [hAv, hrot θ]
      _ = A w := hAv.symm
  have hrefw : (ModalMeridionalReflection.action - 1) w = 0 := by
    apply sub_eq_zero.mpr
    change ModalMeridionalReflection.action w = w
    apply hinj
    have hc := congrFun (congrArg DFunLike.coe (ModalMeridionalVolume.complex_comm n hn z)) w
    change ModalMeridionalReflection.action (A w) = A (ModalMeridionalReflection.action w) at hc
    calc
      A (ModalMeridionalReflection.action w) = ModalMeridionalReflection.action (A w) := hc.symm
      _ = v := by rw [hAv, href]
      _ = A w := hAv.symm
  exact ⟨hrotw,hrefw⟩

theorem compressedInverse_two_sided (n : ℝ) (hn : 1 < n) (z : ℂ)
    (hu : IsUnit (ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1)) :
    block n hn z * compressedInverse n hn z = 1 ∧
      compressedInverse n hn z * block n hn z = 1 := by
  let A := ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1
  let B := Ring.inverse A
  have hleft : B * A = 1 := Ring.inverse_mul_cancel A hu
  have hright : A * B = 1 := Ring.mul_inverse_cancel A hu
  have hb (u : Sector) : B (u : VectorL2) ∈ Sector := ambient_inverse_mem_sector n hn z hu u u.property
  constructor
  · apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    change A ((Sector.orthogonalProjection (B u) : Sector) : VectorL2) = (u : VectorL2)
    rw [Submodule.orthogonalProjection_mem_subspace_eq_self ⟨B u,hb u⟩]
    have h := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (u : VectorL2)) hright
    exact h
  · apply ContinuousLinearMap.ext
    intro u
    change Sector.orthogonalProjection (B (A u)) = u
    have h := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (u : VectorL2)) hleft
    change B (A u) = (u : VectorL2) at h
    rw [h, Submodule.orthogonalProjection_mem_subspace_eq_self]

theorem block_punctured_isUnit (n : ℝ) (hn : 1 < n) (z₀ : ℂ) :
    ∀ᶠ z in 𝓝[≠] z₀, IsUnit (block n hn z) := by
  filter_upwards [VolumeAnalyticAlternative.volumeBlock_punctured_isUnit
    (coefficient n hn) 1 (by norm_num) (coefficient_support n hn) z₀] with z hz
  obtain ⟨hl,hr⟩ := compressedInverse_two_sided n hn z hz
  exact ⟨⟨block n hn z,compressedInverse n hn z,hl,hr⟩,rfl⟩

theorem inverse_eq_compressed_eventually (n : ℝ) (hn : 1 < n) (z₀ : ℂ) :
    (fun z => Ring.inverse (block n hn z)) =ᶠ[𝓝[≠] z₀] compressedInverse n hn := by
  filter_upwards [VolumeAnalyticAlternative.volumeBlock_punctured_isUnit
    (coefficient n hn) 1 (by norm_num) (coefficient_support n hn) z₀] with z hz
  obtain ⟨hl,hr⟩ := compressedInverse_two_sided n hn z hz
  have hunit : IsUnit (block n hn z) := ⟨⟨block n hn z,compressedInverse n hn z,hl,hr⟩,rfl⟩
  calc
    Ring.inverse (block n hn z) = Ring.inverse (block n hn z) * 1 := by rw [mul_one]
    _ = Ring.inverse (block n hn z) * (block n hn z * compressedInverse n hn z) := by rw [hl]
    _ = compressedInverse n hn z := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hunit, one_mul]

theorem inverse_meromorphicAt (n : ℝ) (hn : 1 < n) (z₀ : ℂ) :
    MeromorphicAt (fun z => Ring.inverse (block n hn z)) z₀ :=
  (compressedInverse_meromorphicAt n hn z₀).congr (inverse_eq_compressed_eventually n hn z₀).symm

#print axioms OQ14.Packet06SectorOperator.ambient_inverse_mem_sector
#print axioms OQ14.Packet06SectorOperator.compressedInverse_two_sided
#print axioms OQ14.Packet06SectorOperator.block_punctured_isUnit
#print axioms OQ14.Packet06SectorOperator.inverse_eq_compressed_eventually
#print axioms OQ14.Packet06SectorOperator.inverse_meromorphicAt

#print axioms OQ14.Packet06SectorOperator.block_actual
#print axioms OQ14.Packet06SectorOperator.numerator_kernel
#print axioms OQ14.Packet06SectorOperator.kernel_iff_unique_multiple
#print axioms OQ14.Packet06SectorOperator.kernel_eq_span
#print axioms OQ14.Packet06SectorOperator.kernel_finrank_one
#print axioms OQ14.Packet06SectorOperator.block_not_isUnit
#print axioms OQ14.Packet06SectorOperator.compressedInverse_meromorphicAt
end OQ14.Packet06SectorOperator
