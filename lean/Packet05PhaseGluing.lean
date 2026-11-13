import Packet07PeakAttainment
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Continuous local representatives of the same actual phase field glue on
its closure. The overlap argument uses the open phase, not interface values. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05PhaseGluing
open MeasureTheory Set Maxwell

theorem closure_inter_open {U O : Set Space} (hO : IsOpen O) :
    closure U ∩ O ⊆ closure (U ∩ O) := by
  intro x hx
  apply mem_closure_iff.mpr
  intro V hV hxV
  obtain ⟨y,hyVO,hyU⟩ := mem_closure_iff.mp hx.1 (V ∩ O) (hV.inter hO) ⟨hxV,hx.2⟩
  exact ⟨y,hyVO.1,hyU,hyVO.2⟩

theorem overlap {U O P : Set Space} (hU : IsOpen U) (hO : IsOpen O) (hP : IsOpen P)
    (E f g : Space → ℂ) (hf : Continuous f) (hg : Continuous g)
    (hfe : f =ᵐ[volume.restrict (U ∩ O)] E)
    (hge : g =ᵐ[volume.restrict (U ∩ P)] E) :
    EqOn f g (closure U ∩ (O ∩ P)) := by
  have ho : U ∩ (O ∩ P) ⊆ U ∩ O := fun _ hx => ⟨hx.1,hx.2.1⟩
  have hp : U ∩ (O ∩ P) ⊆ U ∩ P := fun _ hx => ⟨hx.1,hx.2.2⟩
  have hf' : f =ᵐ[volume.restrict (U ∩ (O ∩ P))] E :=
    ae_restrict_of_ae_restrict_of_subset ho hfe
  have hg' : g =ᵐ[volume.restrict (U ∩ (O ∩ P))] E :=
    ae_restrict_of_ae_restrict_of_subset hp hge
  have hfg : f =ᵐ[volume.restrict (U ∩ (O ∩ P))] g := hf'.trans hg'.symm
  have he := Measure.eqOn_open_of_ae_eq hfg (hU.inter (hO.inter hP)) hf.continuousOn hg.continuousOn
  exact (closure_inter_open (hO.inter hP)).trans (closure_minimal he (isClosed_eq hf hg))

theorem finite_phase_gluing {J : Type*} [Fintype J]
    (U : Set Space) (hU : IsOpen U) (O : J → Set Space) (hO : ∀ j, IsOpen (O j))
    (E : Space → ℂ) (f : J → Space → ℂ) (hf : ∀ j, Continuous (f j))
    (hae : ∀ j, f j =ᵐ[volume.restrict (U ∩ O j)] E) :
    ∃ F : Space → ℂ,
      ContinuousOn F (closure U ∩ ⋃ j, O j) ∧
      (∀ j, EqOn F (f j) (closure U ∩ O j)) ∧
      F =ᵐ[volume.restrict (U ∩ ⋃ j, O j)] E := by
  classical
  let F : Space → ℂ := fun x => if h : ∃ j, x ∈ O j then f h.choose x else 0
  have he (j : J) : EqOn F (f j) (closure U ∩ O j) := by
    intro x hx
    have hh : ∃ j, x ∈ O j := ⟨j,hx.2⟩
    dsimp only [F]
    rw [dif_pos hh]
    exact overlap hU (hO hh.choose) (hO j) E _ _ (hf _) (hf _) (hae _) (hae _)
      ⟨hx.1,hh.choose_spec,hx.2⟩
  refine ⟨F,?_,he,?_⟩
  · apply continuousOn_of_locally_continuousOn
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx.2
    refine ⟨O j,hO j,hj,?_⟩
    apply (hf j).continuousOn.congr
    intro y hy
    exact he j ⟨hy.1.1,hy.2⟩
  · have hall : ∀ᵐ x ∂volume, ∀ j, x ∈ U ∩ O j → f j x=E x := by
      exact ae_all_iff.mpr (fun j => (ae_restrict_iff' (hU.inter (hO j)).measurableSet).mp (hae j))
    apply (ae_restrict_iff' (hU.inter (isOpen_iUnion hO)).measurableSet).mpr
    filter_upwards [hall] with x hx hxU
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxU.2
    exact (he j ⟨subset_closure hxU.1,hj⟩).trans (hx j ⟨hxU.1,hj⟩)

end OQ14.Packet05PhaseGluing
#print axioms OQ14.Packet05PhaseGluing.closure_inter_open
#print axioms OQ14.Packet05PhaseGluing.overlap
#print axioms OQ14.Packet05PhaseGluing.finite_phase_gluing
