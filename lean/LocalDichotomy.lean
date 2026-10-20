import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Neighborhoods

noncomputable section
set_option autoImplicit false

namespace OQ14.LocalDichotomy

open Filter Set
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

theorem closure_isOpen (s : Set X)
    (hd : ∀ x : X, (∀ᶠ y in 𝓝 x, y ∉ s) ∨ ∀ᶠ y in 𝓝[≠] x, y ∈ s) :
    IsOpen (closure s) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hd x with hno | hyes
  · exact False.elim ((mem_closure_iff_frequently.mp hx) hno)
  · rw [eventually_nhdsWithin_iff] at hyes
    filter_upwards [hyes] with y hy
    by_cases he : y = x
    · simpa only [he] using hx
    · exact subset_closure (hy he)

theorem dense_of_nonempty [PreconnectedSpace X] (s : Set X) (hs : s.Nonempty)
    (hd : ∀ x : X, (∀ᶠ y in 𝓝 x, y ∉ s) ∨ ∀ᶠ y in 𝓝[≠] x, y ∈ s) :
    closure s = univ :=
  IsClopen.eq_univ ⟨isClosed_closure, closure_isOpen s hd⟩ (hs.mono subset_closure)

theorem punctured_of_nonempty [PreconnectedSpace X] (s : Set X) (hs : s.Nonempty)
    (hd : ∀ x : X, (∀ᶠ y in 𝓝 x, y ∉ s) ∨ ∀ᶠ y in 𝓝[≠] x, y ∈ s) (x : X) :
    ∀ᶠ y in 𝓝[≠] x, y ∈ s := by
  rcases hd x with hno | hyes
  · have hx : x ∈ closure s := by rw [dense_of_nonempty s hs hd]; trivial
    exact False.elim ((mem_closure_iff_frequently.mp hx) hno)
  · exact hyes

end OQ14.LocalDichotomy

#print axioms OQ14.LocalDichotomy.closure_isOpen
#print axioms OQ14.LocalDichotomy.dense_of_nonempty
#print axioms OQ14.LocalDichotomy.punctured_of_nonempty
