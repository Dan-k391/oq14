import Packet05ActualMaximum

/-! Positive-volume actual field peaks force an attained one-sided maximum
above the same threshold. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05HighMaximum
open MeasureTheory Set OQ14.Maxwell OQ14.Packet05ActualMaximum

theorem component_le_physicalAmplitude (R : Fin 3 → Space → ℂ) (x : Space) (j : Fin 3) :
    ‖R j x‖ ≤ physicalAmplitude R x := by
  unfold physicalAmplitude
  apply (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg ‖R i x‖))).mpr
  exact Finset.single_le_sum (fun i _ => sq_nonneg ‖R i x‖) (Finset.mem_univ j)

theorem flat_phase_cover_ae (K Vminus Vplus : Set Space) (hK : MeasurableSet K)
    (hcover : ∀ x ∈ K, x 2 ≠ 0 → x ∈ Vminus ∨ x ∈ Vplus) :
    ∀ᵐ x ∂volume.restrict K, x ∈ Vminus ∨ x ∈ Vplus := by
  have hplane : ∀ᵐ x : Space ∂volume, x 2 ≠ 0 := by
    rw [ae_iff]
    simpa using Packet05LocalDerivative.interface_plane_null
  filter_upwards [ae_restrict_of_ae hplane, ae_restrict_mem hK] with x hx hxK
  exact hcover x hxK hx

theorem attained_max_exceeds_positive_volume_peak
    (K Vminus Vplus : Set Space) (hK : IsClosed K)
    (hVm : MeasurableSet Vminus) (hVp : MeasurableSet Vplus)
    (E Rminus Rplus : Fin 3 → Space → ℂ)
    (hRm : ∀ j, E j =ᵐ[volume.restrict Vminus] Rminus j)
    (hRp : ∀ j, E j =ᵐ[volume.restrict Vplus] Rplus j)
    (hcover : ∀ᵐ x ∂volume.restrict K, x ∈ Vminus ∨ x ∈ Vplus)
    (b : Fin 2) (x : Space)
    (hmax : ∀ b' : Fin 2, ∀ y ∈ K ∩ (if b' = 0 then closure Vminus else closure Vplus),
      physicalAmplitude (if b' = 0 then Rminus else Rplus) y ≤
        physicalAmplitude (if b = 0 then Rminus else Rplus) x)
    (j : Fin 3) (M : ℝ)
    (hpeak : 0 < (volume.restrict K) {y | M < ‖E j y‖}) :
    M < physicalAmplitude (if b = 0 then Rminus else Rplus) x := by
  by_contra hn
  have hupper : physicalAmplitude (if b = 0 then Rminus else Rplus) x ≤ M := not_lt.mp hn
  have hnot : ¬∀ᵐ y ∂volume.restrict K, ‖E j y‖ ≤ M := by
    intro hh
    rw [ae_iff] at hh
    have : (volume.restrict K) {y | M < ‖E j y‖} = 0 := by
      simpa only [not_le] using hh
    exact (ne_of_gt hpeak) this
  apply hnot
  have hm : ∀ᵐ y ∂volume.restrict K, y ∈ Vminus → E j y = Rminus j y :=
    ae_restrict_of_ae ((ae_restrict_iff' hVm).mp (hRm j))
  have hp : ∀ᵐ y ∂volume.restrict K, y ∈ Vplus → E j y = Rplus j y :=
    ae_restrict_of_ae ((ae_restrict_iff' hVp).mp (hRp j))
  filter_upwards [hm, hp, hcover, ae_restrict_mem hK.measurableSet] with y hm hp hside hyK
  rcases hside with hminus | hplus
  · rw [hm hminus]
    have hpoint : y ∈ K ∩ (if (0 : Fin 2) = 0 then closure Vminus else closure Vplus) := by
      simpa using And.intro hyK (subset_closure hminus)
    have hpointmax : physicalAmplitude Rminus y ≤
        physicalAmplitude (if b = 0 then Rminus else Rplus) x := by simpa using hmax 0 y hpoint
    exact (component_le_physicalAmplitude Rminus y j).trans (hpointmax.trans hupper)
  · rw [hp hplus]
    have hpoint : y ∈ K ∩ (if (1 : Fin 2) = 0 then closure Vminus else closure Vplus) := by
      simpa using And.intro hyK (subset_closure hplus)
    have hpointmax : physicalAmplitude Rplus y ≤
        physicalAmplitude (if b = 0 then Rminus else Rplus) x := by simpa using hmax 1 y hpoint
    exact (component_le_physicalAmplitude Rplus y j).trans (hpointmax.trans hupper)

end OQ14.Packet05HighMaximum
#print axioms OQ14.Packet05HighMaximum.component_le_physicalAmplitude
#print axioms OQ14.Packet05HighMaximum.flat_phase_cover_ae
#print axioms OQ14.Packet05HighMaximum.attained_max_exceeds_positive_volume_peak
