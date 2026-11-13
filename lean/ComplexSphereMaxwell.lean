import ComplexMagneticMaxwell
import ComplexSphereInterface
import ComplexRegionalMaxwell
import ComplexExteriorWeak
import CompactSmoothSchwartz

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexSphereMaxwell
open Complex MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.RegionalMaxwellHelmholtz OQ14.WeakHelmholtzRegularity
open OQ14.WeakCurl (next previous)
open scoped SchwartzMap Topology
abbrev VectorL2 := VectorFourier.VectorL2

def electric (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (u : VectorL2) : Field :=
  fun x i => ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
    (VectorFourier.coordinateMap x) i

def magnetic (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2) : Field :=
  ComplexMagneticLocal.magnetic z (DynamicVolume.source (ModalWeightedMode.coefficient n hn) u)

theorem source_pair_interior (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (hT : 1 ≤ T) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) (f : Space → ℂ) (hf : tsupport f ⊆ ball 0 1) :
    (∫ x, DynamicVolume.source (ModalWeightedMode.coefficient n hn) u i x * f x) =
      ((n : ℂ)^2-1) * (∫ x, electric n hn z T u x i * f x) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ComplexSphereInterface.source_actual n hn z T hT u hker i] with x hx
  by_cases hi : x ∈ ball (0 : Space) 1
  · rw [hx, ModalWeightedMode.coefficient_value, if_pos (by simpa using hi)]
    dsimp [electric]
    push_cast
    ring
  · have hz : f x = 0 := image_eq_zero_of_nmem_tsupport (fun h => hi (hf h))
    simp [hz]

theorem interior_maxwell (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (hT : 1 ≤ T) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0) :
    ComplexRegionalMaxwell.TestMaxwell z ((n : ℂ)^2) (ball 0 1) (electric n hn z T u) (magnetic n hn z u) := by
  intro i f
  let s := CompactSmoothSchwartz.ofCompact f.val f.property.1 f.property.2.1
  let g : DynamicSource.Test := ⟨s, f.property.2.1⟩
  have hg : tsupport (g.val : Space → ℂ) ⊆ closedBall 0 T :=
    f.property.2.2.trans (ball_subset_closedBall.trans (closedBall_subset_closedBall hT))
  have h := ComplexMagneticMaxwell.actual_maxwell (ModalWeightedMode.coefficient n hn) 1 T (by linarith) u
    (ModalWeightedMode.coefficient_support n hn) i g hg z
  have hs := source_pair_interior n hn z T hT u hker i f.val f.property.2.2
  have hd (j : Fin 3) : (DynamicSource.testPartial j g).val =
      CompactSmoothSchwartz.ofCompact (fun x => dcoord f.val x j)
        (RegionalMaxwellHelmholtz.testPartial j f).property.1
        (RegionalMaxwellHelmholtz.testPartial j f).property.2.1 := by
    apply SchwartzMap.ext
    intro x
    rfl
  have he : curlPair (fieldPair (electric n hn z T u)) i f = I*z*fieldPair (magnetic n hn z u) i f := by
    dsimp [curlPair, fieldPair, testPartial, electric, magnetic]
    simpa only [DynamicSource.testPartial, GradientProjection.pderivative_apply, s, g,
      CompactSmoothSchwartz.ofCompact_apply] using h.1
  have hh : curlPair (fieldPair (magnetic n hn z u)) i f = (-(I*z*(n : ℂ)^2))*fieldPair (electric n hn z T u) i f := by
    dsimp [curlPair, fieldPair, testPartial, electric, magnetic]
    simp only [DynamicSource.testPartial, GradientProjection.pderivative_apply, s, g,
      CompactSmoothSchwartz.ofCompact_apply] at h
    have hsfun : (CompactSmoothSchwartz.ofCompact f.val f.property.1 f.property.2.1 : Space → ℂ) = f.val := rfl
    rw [hsfun] at h
    dsimp only [electric] at hs
    linear_combination h.2 - (I*z)*hs
  exact ⟨he,hh⟩

theorem exterior_maxwell (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (hT : 0 ≤ T+1) (u : VectorL2) :
    ComplexRegionalMaxwell.TestMaxwell z 1 ((ball 0 T) \ (closedBall 0 1))
      (electric n hn z T u) (magnetic n hn z u) := by
  intro i f
  let s := CompactSmoothSchwartz.ofCompact f.val f.property.1 f.property.2.1
  let g : DynamicSource.Test := ⟨s, f.property.2.1⟩
  have hg : tsupport (g.val : Space → ℂ) ⊆ closedBall 0 T :=
    f.property.2.2.trans (fun x hx => ball_subset_closedBall hx.1)
  have ho : tsupport (g.val : Space → ℂ) ⊆ (closedBall (0 : Space) 1)ᶜ :=
    f.property.2.2.trans (fun x hx => hx.2)
  have h := ComplexMagneticMaxwell.actual_maxwell (ModalWeightedMode.coefficient n hn) 1 T hT u
    (ModalWeightedMode.coefficient_support n hn) i g hg z
  have hs := ComplexExteriorWeak.source_pair_zero n hn u i g ho
  have hsfun : (CompactSmoothSchwartz.ofCompact f.val f.property.1 f.property.2.1 : Space → ℂ) = f.val := rfl
  simp only [DynamicSource.testPartial, GradientProjection.pderivative_apply, s, g,
    CompactSmoothSchwartz.ofCompact_apply] at h
  rw [hsfun] at h
  change (∫ x, DynamicVolume.source (ModalWeightedMode.coefficient n hn) u i x * f.val x) = 0 at hs
  constructor
  · dsimp [curlPair, fieldPair, testPartial, electric, magnetic]
    exact h.1
  · dsimp [curlPair, fieldPair, testPartial, electric, magnetic]
    rw [hs] at h
    simpa only [add_zero, mul_one] using h.2

#print axioms OQ14.ComplexSphereMaxwell.exterior_maxwell
#print axioms OQ14.ComplexSphereMaxwell.interior_maxwell
#print axioms OQ14.ComplexSphereMaxwell.source_pair_interior
end OQ14.ComplexSphereMaxwell
