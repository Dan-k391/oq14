import Packet07ComponentPartition

noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07ExactComponents
open Filter Set
abbrev Data := ConicalStaticVolume.Data
abbrev Space := Maxwell.Space

theorem eventually_exact_components {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
    (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
      (ConicalCommonMaterial.outer p center j)) (ha0 : ∀ i, 0 < a i) :
    ∀ᶠ n : ℕ in atTop,
      (∀ i : ι, ∀ up : Bool, (Packet07LobeGeometry.lobe p a center n i up).Nonempty) ∧
      (∀ i : ι × Bool, ∀ x ∈ Packet07LobeGeometry.lobe p a center n i.1 i.2,
        connectedComponentIn (CommonBinaryInterface.body p a center n) x =
          Packet07LobeGeometry.lobe p a center n i.1 i.2) ∧
      (∀ x ∈ CommonBinaryInterface.body p a center n,
        ∃! i : ι × Bool, connectedComponentIn (CommonBinaryInterface.body p a center n) x =
          Packet07LobeGeometry.lobe p a center n i.1 i.2) := by
  have hn := Packet07LobeNonempty.eventually_all_lobes_nonempty p a center ha0
  have hc := Packet07LobesEventually.eventually_lobes_path_connected p a center ha0
  filter_upwards [hn,hc] with n hn hc
  let L : ι × Bool → Set Space := fun i => Packet07LobeGeometry.lobe p a center n i.1 i.2
  have ho : ∀ i, IsOpen (L i) := fun i => Packet07LobeGeometry.lobe_open p a center n i.1 i.2
  have hpc : ∀ i, IsPreconnected (L i) := fun i => (hc i.1 i.2).isConnected.isPreconnected
  have hd : ∀ i j, i ≠ j → Disjoint (L i) (L j) :=
    Packet07LobeGeometry.lobes_pairwise_disjoint p a center ha hsep ha0 n
  have heq : (⋃ i, L i) = CommonBinaryInterface.body p a center n := by
    ext x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i.1,hi.1⟩
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      rcases (Packet07LobeGeometry.lobe_split p a center n i x).mp hi with h | h
      · exact mem_iUnion.mpr ⟨⟨i,false⟩,h⟩
      · exact mem_iUnion.mpr ⟨⟨i,true⟩,h⟩
  refine ⟨hn, ?_, ?_⟩
  · intro i x hx
    rw [← heq]
    exact Packet07ComponentPartition.component_eq_piece L ho hpc hd i x hx
  · intro x hx
    rw [← heq] at hx ⊢
    exact Packet07ComponentPartition.every_component_unique_piece L ho hpc hd (fun i => hn i.1 i.2) x hx

end OQ14.Packet07ExactComponents
#print axioms OQ14.Packet07ExactComponents.eventually_exact_components
