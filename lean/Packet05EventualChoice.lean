import Packet05RegionalFamilyBootstrap

/-! Choose field-dependent auxiliary arrays while retaining the fixed
family-eventual quantifier. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05EventualChoice
open Filter

theorem choose_eventually {A : Type*} [Nonempty A] (P : ℕ → A → Prop)
    (h : ∀ᶠ j : ℕ in atTop, ∃ a, P j a) :
    ∃ f : ℕ → A, ∀ᶠ j : ℕ in atTop, P j (f j) := by
  classical
  let f : ℕ → A := fun j => if hj : ∃ a, P j a then Classical.choose hj else Classical.choice inferInstance
  refine ⟨f,?_⟩
  filter_upwards [h] with j hj
  simpa [f,hj] using Classical.choose_spec hj

end OQ14.Packet05EventualChoice
#print axioms OQ14.Packet05EventualChoice.choose_eventually
