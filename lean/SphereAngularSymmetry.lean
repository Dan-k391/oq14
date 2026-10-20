import AngularPower
import SphereMeasure

/-! Orthogonal symmetries of the actual angular measure induced by Euclidean volume. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OQ14.SphereAngularSymmetry

open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower
open scoped Pointwise

def sphereMap (L : Space ≃ₗᵢ[ℝ] Space) : Sphere ≃ₜ Sphere :=
  L.toHomeomorph.subtype (by
    intro x
    simp only [Sphere, mem_sphere, dist_zero_right]
    change ‖x‖ = 1 ↔ ‖L x‖ = 1
    rw [L.norm_map])

theorem cone_preimage (L : Space ≃ₗᵢ[ℝ] Space) (s : Set Sphere) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereMap L ⁻¹' s)) =
      L ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨r, hr, L n, ⟨sphereMap L n, hn, rfl⟩, by simp⟩
  · rintro ⟨r, hr, y, ⟨n, hn, rfl⟩, hx⟩
    refine ⟨r, hr, L.symm n, ⟨sphereMap L.symm n, ?_, rfl⟩, ?_⟩
    · change sphereMap L (sphereMap L.symm n) ∈ s
      have he : sphereMap L (sphereMap L.symm n) = n :=
        Subtype.ext (L.apply_symm_apply n)
      rw [he]
      exact hn
    · apply L.injective
      simpa using hx

theorem measurePreserving_sphereMap (L : Space ≃ₗᵢ[ℝ] Space) :
    MeasurePreserving (sphereMap L) angularMeasure angularMeasure := by
  refine ⟨(sphereMap L).continuous.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereMap L).continuous.measurable hs]
  change (volume : Measure Space).toSphere (sphereMap L ⁻¹' s) =
    (volume : Measure Space).toSphere s
  rw [Measure.toSphere_apply' _ ((sphereMap L).continuous.measurable hs),
    Measure.toSphere_apply' _ hs, cone_preimage]
  congr 1
  exact L.measurePreserving.measure_preimage_emb L.toHomeomorph.measurableEmbedding _

theorem integral_sphereMap (L : Space ≃ₗᵢ[ℝ] Space) (f : Sphere → ℝ) :
    (∫ n, f (sphereMap L n) ∂angularMeasure) = ∫ n, f n ∂angularMeasure :=
  (measurePreserving_sphereMap L).integral_comp (sphereMap L).measurableEmbedding f

end OQ14.SphereAngularSymmetry

#print axioms OQ14.SphereAngularSymmetry.sphereMap
#print axioms OQ14.SphereAngularSymmetry.cone_preimage
#print axioms OQ14.SphereAngularSymmetry.measurePreserving_sphereMap
#print axioms OQ14.SphereAngularSymmetry.integral_sphereMap
