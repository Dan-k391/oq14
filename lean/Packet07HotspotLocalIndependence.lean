import Packet07HotspotComponent

/-! A low sphere makes the full connected hotspot independent of all
choices of field extension outside its observation ball. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07HotspotLocalIndependence
open Set Metric Maxwell Packet07HotspotComponent

theorem component_eq_of_local_eq (S T : Set Space) (c x : Space) (r : ℝ)
    (hx : x ∈ S) (hxr : x ∈ ball c r)
    (heq : ∀ y ∈ closedBall c r, y ∈ S ↔ y ∈ T)
    (hbarrier : ∀ y ∈ S, dist y c ≠ r) :
    connectedComponentIn S x = connectedComponentIn T x := by
  have hxT : x ∈ T := (heq x (ball_subset_closedBall hxr)).mp hx
  have hbarrierT : ∀ y ∈ T, dist y c ≠ r := by
    intro y hy hd
    have hb : y ∈ closedBall c r := by
      change dist y c ≤ r
      exact hd.le
    exact hbarrier y ((heq y hb).mpr hy) hd
  have hs := connected_set_inside_of_no_sphere (connectedComponentIn S x)
    isPreconnected_connectedComponentIn c x r (mem_connectedComponentIn hx) hxr
    (fun y hy => hbarrier y (connectedComponentIn_subset S x hy))
  have ht := connected_set_inside_of_no_sphere (connectedComponentIn T x)
    isPreconnected_connectedComponentIn c x r (mem_connectedComponentIn hxT) hxr
    (fun y hy => hbarrierT y (connectedComponentIn_subset T x hy))
  apply Subset.antisymm
  · apply isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hx)
    intro y hy
    exact (heq y (ball_subset_closedBall (hs hy))).mp (connectedComponentIn_subset S x hy)
  · apply isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hxT)
    intro y hy
    exact (heq y (ball_subset_closedBall (ht hy))).mpr (connectedComponentIn_subset T x hy)

theorem branch_component_eq_of_local_eq {J : Type*}
    (D : J → Set Space) (f g : J → Space → ℝ) (t : ℝ)
    (c x : Space) (r : ℝ) (j : J) (hx : x ∈ D j) (hpeak : t ≤ f j x)
    (hxr : x ∈ ball c r)
    (heq : ∀ k y, y ∈ closedBall c r ∩ D k → f k y=g k y)
    (hbarrier : ∀ k y, y ∈ D k → dist y c=r → f k y<t) :
    connectedComponentIn (branchSuperlevel D f t) x =
      connectedComponentIn (branchSuperlevel D g t) x := by
  have hmem : x ∈ branchSuperlevel D f t := mem_iUnion.mpr ⟨j,hx,hpeak⟩
  apply component_eq_of_local_eq (branchSuperlevel D f t) (branchSuperlevel D g t) c x r hmem hxr
  · intro y hy
    constructor
    · intro h
      obtain ⟨k,hk,hle⟩ := mem_iUnion.mp h
      have hfg := heq k y ⟨hy,hk⟩
      change t ≤ f k y at hle
      exact mem_iUnion.mpr ⟨k,hk,by change t ≤ g k y; rwa [hfg] at hle⟩
    · intro h
      obtain ⟨k,hk,hle⟩ := mem_iUnion.mp h
      have hfg := heq k y ⟨hy,hk⟩
      change t ≤ g k y at hle
      exact mem_iUnion.mpr ⟨k,hk,by change t ≤ f k y; rwa [← hfg] at hle⟩
  · intro y hy hd
    obtain ⟨k,hk,hle⟩ := mem_iUnion.mp hy
    exact (not_le.mpr (hbarrier k y hk hd)) hle

end OQ14.Packet07HotspotLocalIndependence
#print axioms OQ14.Packet07HotspotLocalIndependence.component_eq_of_local_eq
#print axioms OQ14.Packet07HotspotLocalIndependence.branch_component_eq_of_local_eq
