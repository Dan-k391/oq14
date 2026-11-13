import Packet05LocalPhaseSymmetry

/-! A physical field's a.e. symmetry passes to its actual continuous phase
representative, including the one-sided boundary trace. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05PhaseRepresentativeSymmetry
open MeasureTheory Set Maxwell

theorem representative_symmetry (U V : Set Space) (hU : IsOpen U) (hV : IsOpen V)
    (f a : Space → ℝ) (hf : ContinuousOn f (closure U ∩ V))
    (T : Space → Space) (hT : Continuous T) (hμ : MeasurePreserving T volume volume)
    (hmapU : MapsTo T U U) (hmapV : MapsTo T V V)
    (hfa : f =ᵐ[volume.restrict (U ∩ V)] a)
    (ha : (a ∘ T) =ᵐ[volume.restrict V] a) :
    EqOn (f ∘ T) f (closure U ∩ V) := by
  have hglobal : ∀ᵐ x : Space, x ∈ U ∩ V → f x=a x :=
    (ae_restrict_iff' (hU.inter hV).measurableSet).mp hfa
  have hrot := hμ.quasiMeasurePreserving.ae hglobal
  apply Packet05LocalPhaseSymmetry.local_phase_symmetry U V hU hV f hf T hT
    (fun x hx => ⟨hmapU.closure hT hx.1,hmapV hx.2⟩)
  have har : (a ∘ T) =ᵐ[volume.restrict (U ∩ V)] a :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right ha
  filter_upwards [ae_restrict_of_ae hglobal,ae_restrict_of_ae hrot,har,
    ae_restrict_mem (hU.inter hV).measurableSet] with x hx htx hax hmem
  exact (htx ⟨hmapU hmem.1,hmapV hmem.2⟩).trans (hax.trans (hx hmem).symm)

end OQ14.Packet05PhaseRepresentativeSymmetry
#print axioms OQ14.Packet05PhaseRepresentativeSymmetry.representative_symmetry
