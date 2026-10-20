import Maxwell
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Logic.Relation

/-! # Actual material-cell bridges, graph reachability and AE covers -/

noncomputable section
set_option autoImplicit false

namespace OQ14.MaterialCellGraph

open MeasureTheory Filter Set OQ14.Maxwell
open scoped Topology

def Bridge (U V : Set Space) : Prop :=
  ∃ B : Set Space, IsOpen B ∧ IsConnected B ∧
    (∀ᵐ x : Space, x ∈ B → x ∈ U ∪ V) ∧ (B ∩ U).Nonempty ∧ (B ∩ V).Nonempty

theorem bridge_symm {U V : Set Space} (h : Bridge U V) : Bridge V U := by
  obtain ⟨B,hB,hconn,hcover,hU,hV⟩ := h
  refine ⟨B,hB,hconn,?_,hV,hU⟩
  simpa only [union_comm] using hcover

theorem bridge_comm (U V : Set Space) : Bridge U V ↔ Bridge V U :=
  ⟨bridge_symm,bridge_symm⟩

theorem reachable_property {ι : Type*} (cells : ι → Set Space) (P : ι → Prop)
    (hstep : ∀ i j, Bridge (cells i) (cells j) → P i → P j)
    {i j : ι} (hpath : Relation.ReflTransGen (fun i j => Bridge (cells i) (cells j)) i j)
    (hi : P i) : P j := by
  induction hpath with
  | refl => exact hi
  | @tail j k hpath hbridge ih => exact hstep j k hbridge ih

theorem reachable_symm {ι : Type*} (cells : ι → Set Space) {i j : ι}
    (hpath : Relation.ReflTransGen (fun i j => Bridge (cells i) (cells j)) i j) :
    Relation.ReflTransGen (fun i j => Bridge (cells i) (cells j)) j i := by
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | @tail j k hpath hbridge ih =>
      have hs : Relation.ReflTransGen (fun i j => Bridge (cells i) (cells j)) k j :=
        Relation.ReflTransGen.single (bridge_symm hbridge)
      exact hs.trans ih

theorem ae_zero_of_countable_cell_cover {ι Y : Type*} [Countable ι] [Zero Y]
    (cells : ι → Set Space) (hopen : ∀ i, IsOpen (cells i)) (u : Space → Y)
    (hzero : ∀ i, u =ᵐ[volume.restrict (cells i)] 0)
    (hcover : ∀ᵐ x : Space, ∃ i, x ∈ cells i) : u =ᵐ[volume] 0 := by
  have hz : ∀ᵐ x : Space, ∀ i, x ∈ cells i → u x = 0 :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hopen i).measurableSet).mp (hzero i))
  filter_upwards [hcover,hz] with x hx hz
  obtain ⟨i,hi⟩ := hx
  exact hz i hi

theorem ae_zero_of_open_cell_cover {ι Y : Type*} [Zero Y]
    (cells : ι → Set Space) (hopen : ∀ i, IsOpen (cells i)) (u : Space → Y)
    (hzero : ∀ i, u =ᵐ[volume.restrict (cells i)] 0)
    (hcover : ∀ᵐ x : Space, ∃ i, x ∈ cells i) : u =ᵐ[volume] 0 := by
  obtain ⟨T,hT,hTU⟩ := TopologicalSpace.isOpen_iUnion_countable cells hopen
  have hz : u =ᵐ[volume.restrict (⋃ i ∈ T, cells i)] 0 :=
    (ae_eq_restrict_biUnion_iff cells hT u 0).mpr (fun i _ => hzero i)
  rw [hTU] at hz
  have hz' : ∀ᵐ x : Space, x ∈ ⋃ i, cells i → u x = 0 :=
    (ae_restrict_iff' (isOpen_iUnion hopen).measurableSet).mp hz
  filter_upwards [hcover,hz'] with x hx hz
  exact hz (mem_iUnion.mpr hx)

theorem ae_zero_of_reachable_open_cover {ι Y : Type*} [Zero Y]
    (cells : ι → Set Space) (hopen : ∀ i, IsOpen (cells i)) (u : Space → Y)
    (hstep : ∀ i j, Bridge (cells i) (cells j) →
      u =ᵐ[volume.restrict (cells i)] 0 → u =ᵐ[volume.restrict (cells j)] 0)
    (i₀ : ι) (hzero : u =ᵐ[volume.restrict (cells i₀)] 0)
    (hreach : ∀ j, Relation.ReflTransGen (fun i j => Bridge (cells i) (cells j)) i₀ j)
    (hcover : ∀ᵐ x : Space, ∃ i, x ∈ cells i) : u =ᵐ[volume] 0 := by
  apply ae_zero_of_open_cell_cover cells hopen u _ hcover
  intro j
  exact reachable_property cells (fun i => u =ᵐ[volume.restrict (cells i)] 0)
    hstep (hreach j) hzero

end OQ14.MaterialCellGraph

#print axioms OQ14.MaterialCellGraph.bridge_symm
#print axioms OQ14.MaterialCellGraph.bridge_comm
#print axioms OQ14.MaterialCellGraph.reachable_property
#print axioms OQ14.MaterialCellGraph.reachable_symm
#print axioms OQ14.MaterialCellGraph.ae_zero_of_countable_cell_cover
#print axioms OQ14.MaterialCellGraph.ae_zero_of_open_cell_cover
#print axioms OQ14.MaterialCellGraph.ae_zero_of_reachable_open_cover
