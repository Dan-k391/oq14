import Packet05PhaseGluing

/-! Uniqueness of actual one-sided traces on an interior observation ball. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06InteriorTraceUnique
open MeasureTheory Set Metric Maxwell

theorem unique (U : Set Space) (hU : IsOpen U) (c : Space) (r R : ℝ) (hr : r < R)
    (E f g : Space → ℂ)
    (hf : ContinuousOn f (closedBall c R ∩ closure U))
    (hg : ContinuousOn g (closedBall c R ∩ closure U))
    (hfe : f =ᵐ[volume.restrict (closedBall c R ∩ U)] E)
    (hge : g =ᵐ[volume.restrict (closedBall c R ∩ U)] E) :
    EqOn f g (closedBall c r ∩ closure U) := by
  have hsub : U ∩ ball c R ⊆ closedBall c R ∩ U := fun _ hx => ⟨ball_subset_closedBall hx.2,hx.1⟩
  have hfe' : f =ᵐ[volume.restrict (U ∩ ball c R)] E := ae_restrict_of_ae_restrict_of_subset hsub hfe
  have hge' : g =ᵐ[volume.restrict (U ∩ ball c R)] E := ae_restrict_of_ae_restrict_of_subset hsub hge
  have hae : f =ᵐ[volume.restrict (U ∩ ball c R)] g := hfe'.trans hge'.symm
  have hop : IsOpen (U ∩ ball c R) := hU.inter isOpen_ball
  have hsmall : U ∩ ball c R ⊆ closedBall c R ∩ closure U :=
    fun _ hx => ⟨ball_subset_closedBall hx.2,subset_closure hx.1⟩
  have heq := Measure.eqOn_open_of_ae_eq hae hop (hf.mono hsmall) (hg.mono hsmall)
  have hclosed : IsClosed {x ∈ closedBall c R ∩ closure U | f x = g x} :=
    (isClosed_closedBall.inter isClosed_closure).isClosed_eq hf hg
  have hcover : U ∩ ball c R ⊆ {x ∈ closedBall c R ∩ closure U | f x = g x} :=
    fun x hx => ⟨hsmall hx,heq hx⟩
  intro x hx
  have hxball : x ∈ ball c R := lt_of_le_of_lt hx.1 hr
  have hxc : x ∈ closure (U ∩ ball c R) :=
    Packet05PhaseGluing.closure_inter_open isOpen_ball ⟨hx.2,hxball⟩
  exact (closure_minimal hcover hclosed hxc).2

end OQ14.Packet06InteriorTraceUnique
#print axioms OQ14.Packet06InteriorTraceUnique.unique
