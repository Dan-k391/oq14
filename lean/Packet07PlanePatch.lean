import Packet07PlaneCoordinates

/-! Affine-plane projection is the literal orthogonal projection, and every
relatively open nonempty physical patch pulls back to an open planar patch. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07PlanePatch
open Maxwell Set Metric Packet07PlaneFrame Packet07PlaneCoordinates Packet07PlanarCenters
abbrev Space := Maxwell.Space
abbrev Plane := Packet07PlanarCenters.Plane

theorem projection_remainder (θ φ : ℝ) (a x : Space) :
    x-projection θ φ a x = ((normalRotation θ φ).symm (x-a) 2) •
      normalRotation θ φ (EuclideanSpace.single 2 1) := by
  let R := normalRotation θ φ
  let y := R.symm (x-a)
  have hy : y-planeEmbed (planeProject y)=y 2 • EuclideanSpace.single 2 1 := by
    ext i
    fin_cases i <;> simp [planeEmbed,planeProject,EuclideanSpace.single_apply,PiLp.smul_apply,PiLp.sub_apply]
  have hRy : R y=x-a := R.apply_symm_apply (x-a)
  have h := congrArg R hy
  simp only [map_sub,map_smul,hRy] at h
  change x-(a+R (planeEmbed (planeProject y))) = y 2 • R (EuclideanSpace.single 2 1)
  rw [← h]
  abel

theorem projection_orthogonal (θ φ : ℝ) (a x z : Space)
    (hz : z ∈ affinePlane (normalRotation θ φ (EuclideanSpace.single 2 1)) a) :
    @inner ℝ Space _ (x-projection θ φ a x) (z-a)=0 := by
  rw [projection_remainder,real_inner_smul_left]
  have h : @inner ℝ Space _ (z-a) (normalRotation θ φ (EuclideanSpace.single 2 1))=0 := hz
  rw [real_inner_comm,h,mul_zero]

theorem embed_continuous (θ φ : ℝ) (a : Space) : Continuous (embed θ φ a) := by
  apply (isometry_iff_dist_eq.mpr (embed_dist θ φ a)).continuous

theorem patch_pullback (θ φ : ℝ) (a : Space) (O : Set Space) (hO : IsOpen O)
    (hne : (affinePlane (normalRotation θ φ (EuclideanSpace.single 2 1)) a ∩ O).Nonempty) :
    let P : Set Plane := embed θ φ a ⁻¹' O
    IsOpen P ∧ P.Nonempty ∧ embed θ φ a '' P = affinePlane (normalRotation θ φ (EuclideanSpace.single 2 1)) a ∩ O := by
  dsimp only
  refine ⟨hO.preimage (embed_continuous θ φ a),?_,?_⟩
  · obtain ⟨x,hxp,hxO⟩ := hne
    exact ⟨coordinates θ φ a x,by simpa [embed_coordinates θ φ a x hxp] using hxO⟩
  · ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨embed_plane θ φ a u,hu⟩
    · rintro ⟨hp,hO⟩
      exact ⟨coordinates θ φ a x,by simpa [embed_coordinates θ φ a x hp] using hO,embed_coordinates θ φ a x hp⟩
end OQ14.Packet07PlanePatch
#print axioms OQ14.Packet07PlanePatch.projection_remainder
#print axioms OQ14.Packet07PlanePatch.projection_orthogonal
#print axioms OQ14.Packet07PlanePatch.embed_continuous
#print axioms OQ14.Packet07PlanePatch.patch_pullback
