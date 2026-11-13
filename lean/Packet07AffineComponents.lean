import Packet07ExactComponents
import Packet07AffineGeometry

noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07AffineComponents
open Set
abbrev Space := Maxwell.Space

theorem place_map (s : ℝ) (hs : s ≠ 0) (a x : Space) :
    Packet07AffineGeometry.place s a (Packet07AffineGeometry.map s a x) = x := by
  simp [Packet07AffineGeometry.place, Packet07AffineGeometry.map, smul_smul, hs]

theorem preimage_path_connected (s : ℝ) (hs : s ≠ 0) (a : Space) (S : Set Space)
    (hS : IsPathConnected S) :
    IsPathConnected (Packet07AffineGeometry.map s a ⁻¹' S) := by
  have hcont : Continuous (Packet07AffineGeometry.place s a) :=
    (continuous_const.smul continuous_id).add continuous_const
  have him := hS.image hcont
  have heq : Packet07AffineGeometry.place s a '' S = Packet07AffineGeometry.map s a ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [mem_preimage, Packet07AffineGeometry.map_place s hs] using hy
    · intro hx
      refine ⟨Packet07AffineGeometry.map s a x, hx, ?_⟩
      exact place_map s hs a x
  simpa only [heq] using him

theorem preimage_connected (s : ℝ) (hs : s ≠ 0) (a : Space) (S : Set Space)
    (hS : IsConnected S) : IsConnected (Packet07AffineGeometry.map s a ⁻¹' S) := by
  have hcont : Continuous (Packet07AffineGeometry.place s a) :=
    (continuous_const.smul continuous_id).add continuous_const
  have him := hS.image _ hcont.continuousOn
  have heq : Packet07AffineGeometry.place s a '' S = Packet07AffineGeometry.map s a ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [mem_preimage, Packet07AffineGeometry.map_place s hs] using hy
    · intro hx
      exact ⟨Packet07AffineGeometry.map s a x, hx, place_map s hs a x⟩
  simpa only [heq] using him
theorem affine_partition {ι : Type*} [DecidableEq ι] (s : ℝ) (hs : s ≠ 0)
    (a : Space) (L : ι → Set Space)
    (ho : ∀ i, IsOpen (L i)) (hc : ∀ i, IsConnected (L i))
    (hd : ∀ i j, i ≠ j → Disjoint (L i) (L j))
    (i : ι) (x : Space) (hx : x ∈ Packet07AffineGeometry.map s a ⁻¹' L i) :
    connectedComponentIn (Packet07AffineGeometry.map s a ⁻¹' ⋃ j, L j) x =
      Packet07AffineGeometry.map s a ⁻¹' L i := by
  let M : ι → Set Space := fun j => Packet07AffineGeometry.map s a ⁻¹' L j
  have ho' : ∀ j, IsOpen (M j) := fun j => Packet07AffineGeometry.preimage_open s a (L j) (ho j)
  have hc' : ∀ j, IsPreconnected (M j) := fun j =>
    (preimage_connected s hs a (L j) (hc j)).isPreconnected
  have hd' : ∀ i j, i ≠ j → Disjoint (M i) (M j) := fun i j hij =>
    Packet07AffineGeometry.preimage_disjoint s a (L i) (L j) (hd i j hij)
  have heq : (⋃ j, M j) = Packet07AffineGeometry.map s a ⁻¹' ⋃ j, L j := preimage_iUnion.symm
  rw [← heq]
  exact Packet07ComponentPartition.component_eq_piece M ho' hc' hd' i x hx

theorem affine_exact_partition {ι : Type*} [DecidableEq ι] (s : ℝ) (hs : s ≠ 0)
    (a : Space) (L : ι → Set Space) (B : Set Space)
    (ho : ∀ i, IsOpen (L i)) (hne : ∀ i, (L i).Nonempty)
    (hd : ∀ i j, i ≠ j → Disjoint (L i) (L j)) (heq : (⋃ i, L i) = B)
    (hexact : ∀ i, ∀ x ∈ L i, connectedComponentIn B x = L i) :
    (∀ i, ∀ x ∈ Packet07AffineGeometry.map s a ⁻¹' L i,
      connectedComponentIn (Packet07AffineGeometry.map s a ⁻¹' B) x =
        Packet07AffineGeometry.map s a ⁻¹' L i) ∧
    (∀ x ∈ Packet07AffineGeometry.map s a ⁻¹' B,
      ∃! i, connectedComponentIn (Packet07AffineGeometry.map s a ⁻¹' B) x =
        Packet07AffineGeometry.map s a ⁻¹' L i) := by
  have hc : ∀ i, IsConnected (L i) := by
    intro i
    obtain ⟨x,hx⟩ := hne i
    have hxB : x ∈ B := by rw [← heq]; exact mem_iUnion.mpr ⟨i,hx⟩
    rw [← hexact i x hx]
    exact isConnected_connectedComponentIn_iff.mpr hxB
  let M : ι → Set Space := fun i => Packet07AffineGeometry.map s a ⁻¹' L i
  have ho' : ∀ i, IsOpen (M i) := fun i => Packet07AffineGeometry.preimage_open s a (L i) (ho i)
  have hc' : ∀ i, IsPreconnected (M i) := fun i => (preimage_connected s hs a (L i) (hc i)).isPreconnected
  have hd' : ∀ i j, i ≠ j → Disjoint (M i) (M j) := fun i j hij =>
    Packet07AffineGeometry.preimage_disjoint s a (L i) (L j) (hd i j hij)
  have hn' : ∀ i, (M i).Nonempty := fun i => Packet07AffineGeometry.preimage_nonempty s hs a (L i) (hne i)
  have heq' : (⋃ i, M i) = Packet07AffineGeometry.map s a ⁻¹' B := by rw [← heq, preimage_iUnion]
  constructor
  · intro i x hx
    rw [← heq']
    exact Packet07ComponentPartition.component_eq_piece M ho' hc' hd' i x hx
  · intro x hx
    rw [← heq'] at hx ⊢
    exact Packet07ComponentPartition.every_component_unique_piece M ho' hc' hd' hn' x hx
end OQ14.Packet07AffineComponents
#print axioms OQ14.Packet07AffineComponents.place_map
#print axioms OQ14.Packet07AffineComponents.preimage_path_connected
#print axioms OQ14.Packet07AffineComponents.preimage_connected
#print axioms OQ14.Packet07AffineComponents.affine_partition
#print axioms OQ14.Packet07AffineComponents.affine_exact_partition
