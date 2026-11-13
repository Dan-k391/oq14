import Packet05HighMaximum

/-! Compact attainment and positive-volume peak adapter for arbitrary curved
material phases, once actual continuous side representatives are supplied. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05CurvedMaximumAdapter
open MeasureTheory Set OQ14.Maxwell OQ14.Packet05ActualMaximum
  OQ14.Packet05HighMaximum OQ14.Packet05FiniteBranchMaximum

/-- The geometric phases need not be flat.  The required side representatives
and the almost-everywhere phase cover are exposed as explicit inputs. -/
theorem two_phase_attained_high_given_side_representatives
    (K Vminus Vplus : Set Space) (hK : IsCompact K) (hne : K.Nonempty)
    (hVm : MeasurableSet Vminus) (hVp : MeasurableSet Vplus)
    (hcover : K ⊆ closure Vminus ∪ closure Vplus)
    (hcoverae : ∀ᵐ x ∂volume.restrict K, x ∈ Vminus ∨ x ∈ Vplus)
    (E Rminus Rplus : Fin 3 → Space → ℂ)
    (hRmc : ∀ j, Continuous (Rminus j)) (hRpc : ∀ j, Continuous (Rplus j))
    (hRmae : ∀ j, E j =ᵐ[volume.restrict Vminus] Rminus j)
    (hRpae : ∀ j, E j =ᵐ[volume.restrict Vplus] Rplus j)
    (j : Fin 3) (M : ℝ) (hpeak : 0 < (volume.restrict K) {x | M < ‖E j x‖}) :
    ∃ b : Fin 2, ∃ x ∈ K ∩ (if b = 0 then closure Vminus else closure Vplus),
      M < physicalAmplitude (if b = 0 then Rminus else Rplus) x ∧
      ∀ b' : Fin 2, ∀ y ∈ K ∩ (if b' = 0 then closure Vminus else closure Vplus),
        physicalAmplitude (if b' = 0 then Rminus else Rplus) y ≤
          physicalAmplitude (if b = 0 then Rminus else Rplus) x := by
  let D : Fin 2 → Set Space := fun b => if b = 0 then closure Vminus else closure Vplus
  let amp : Fin 2 → Space → ℝ := fun b x => physicalAmplitude (if b = 0 then Rminus else Rplus) x
  have hclosed (b : Fin 2) : IsClosed (D b) := by
    dsimp [D]
    split_ifs <;> exact isClosed_closure
  have hcov : K ⊆ ⋃ b, D b := by
    intro x hx
    rcases hcover hx with hm | hp
    · exact mem_iUnion.mpr ⟨0, by simpa [D] using hm⟩
    · exact mem_iUnion.mpr ⟨1, by simpa [D] using hp⟩
  have hcont (b : Fin 2) : ContinuousOn (amp b) (K ∩ D b) := by
    apply Continuous.continuousOn
    by_cases hb : b = 0
    · simp only [amp, hb, if_true]
      exact physicalAmplitude_continuous Rminus hRmc
    · simp only [amp, hb, if_false]
      exact physicalAmplitude_continuous Rplus hRpc
  obtain ⟨b,x,hx,hmax⟩ := finite_closed_branches_attain_max K hK hne D hclosed hcov amp hcont
  have hhigh := attained_max_exceeds_positive_volume_peak K Vminus Vplus hK.isClosed hVm hVp
    E Rminus Rplus hRmae hRpae hcoverae b x hmax j M hpeak
  exact ⟨b,x,hx,hhigh,hmax⟩

end OQ14.Packet05CurvedMaximumAdapter
#print axioms OQ14.Packet05CurvedMaximumAdapter.two_phase_attained_high_given_side_representatives
