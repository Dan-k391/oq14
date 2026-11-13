import Packet05RoundedCompactBranches
import Packet07PeakAttainment

/-! Actual phase representatives on compact closures turn positive-volume
field peaks into attained maxima of the physical Euclidean amplitude. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05BinaryPhaseMaximum
open MeasureTheory Set Maxwell Packet05ActualMaximum

def phaseDomain (body : Set Space) : Bool → Set Space
  | true => closure body
  | false => closure (closure body)ᶜ

def phaseField (inside outside : Fin 3 → Space → ℂ) : Bool → Fin 3 → Space → ℂ
  | true => inside
  | false => outside

theorem amplitude_continuousOn (R : Fin 3 → Space → ℂ) (K : Set Space)
    (hR : ∀ i, ContinuousOn (R i) K) : ContinuousOn (physicalAmplitude R) K := by
  unfold physicalAmplitude
  exact Real.continuous_sqrt.comp_continuousOn
    (continuousOn_finset_sum _ (fun i _ => (hR i).norm.pow 2))

theorem phase_domains_cover (body K : Set Space) : K ⊆ ⋃ b, phaseDomain body b := by
  intro x hx
  by_cases hb : x ∈ closure body
  · exact mem_iUnion.mpr ⟨true,hb⟩
  · exact mem_iUnion.mpr ⟨false,subset_closure hb⟩

theorem actual_amplitude_ae (body K : Set Space) (hb : IsOpen body) (hK : MeasurableSet K)
    (hnull : volume (frontier body)=0) (E : Field) (inside outside : Fin 3 → Space → ℂ)
    (hin : ∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ body)] inside i)
    (hout : ∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside i) :
    ∀ᵐ y ∂volume.restrict K, ∃ b, y ∈ phaseDomain body b ∧
      physicalAmplitude (fun i x => E x i) y=physicalAmplitude (phaseField inside outside b) y := by
  have hi : ∀ᵐ y ∂volume, ∀ i, y ∈ K ∩ body → E y i=inside i y :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hK.inter hb.measurableSet)).mp (hin i))
  have ho : ∀ᵐ y ∂volume, ∀ i, y ∈ K ∩ (closure body)ᶜ → E y i=outside i y :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hK.inter isClosed_closure.measurableSet.compl)).mp (hout i))
  have hn : ∀ᵐ y : Space ∂volume, y ∉ frontier body := by simpa only [ae_iff,not_not] using hnull
  filter_upwards [ae_restrict_of_ae hi,ae_restrict_of_ae ho,ae_restrict_of_ae hn,ae_restrict_mem hK]
    with y hi ho hn hyK
  by_cases hybody : y ∈ body
  · refine ⟨true,subset_closure hybody,?_⟩
    simp only [phaseField,physicalAmplitude]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hi i ⟨hyK,hybody⟩]
  · have hyext : y ∉ closure body := by
      intro hyc
      apply hn
      rw [hb.frontier_eq]
      exact ⟨hyc,hybody⟩
    refine ⟨false,subset_closure hyext,?_⟩
    simp only [phaseField,physicalAmplitude]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [ho i ⟨hyK,hyext⟩]

theorem attained_above_peak (body K : Set Space) (hb : IsOpen body) (hK : IsCompact K)
    (hne : K.Nonempty) (hnull : volume (frontier body)=0)
    (E : Field) (inside outside : Fin 3 → Space → ℂ)
    (hinc : ∀ i, ContinuousOn (inside i) (K ∩ closure body))
    (houtc : ∀ i, ContinuousOn (outside i) (K ∩ closure (closure body)ᶜ))
    (hin : ∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ body)] inside i)
    (hout : ∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside i)
    (M : ℝ) (hpeak : 0 < (volume.restrict K) {y | M < physicalAmplitude (fun i x => E x i) y}) :
    ∃ b x, x ∈ K ∩ phaseDomain body b ∧
      M < physicalAmplitude (phaseField inside outside b) x ∧
      ∀ b' y, y ∈ K ∩ phaseDomain body b' →
        physicalAmplitude (phaseField inside outside b') y ≤ physicalAmplitude (phaseField inside outside b) x := by
  have hcont (b : Bool) : ContinuousOn (physicalAmplitude (phaseField inside outside b)) (K ∩ phaseDomain body b) := by
    cases b
    · exact amplitude_continuousOn outside _ houtc
    · exact amplitude_continuousOn inside _ hinc
  obtain ⟨b,x,hx,hmax⟩ := Packet05FiniteBranchMaximum.finite_closed_branches_attain_max
    K hK hne (phaseDomain body) (fun b => by cases b <;> exact isClosed_closure)
    (phase_domains_cover body K) (fun b => physicalAmplitude (phaseField inside outside b)) hcont
  have hh := Packet07PeakAttainment.positive_volume_exceeds_maximum K hK.isClosed.measurableSet
    (phaseDomain body) (fun b => physicalAmplitude (phaseField inside outside b))
    (physicalAmplitude (fun i x => E x i))
    (actual_amplitude_ae body K hb hK.isClosed.measurableSet hnull E inside outside hin hout)
    b x hmax M hpeak
  exact ⟨b,x,hx,hh,hmax⟩

end OQ14.Packet05BinaryPhaseMaximum
#print axioms OQ14.Packet05BinaryPhaseMaximum.amplitude_continuousOn
#print axioms OQ14.Packet05BinaryPhaseMaximum.phase_domains_cover
#print axioms OQ14.Packet05BinaryPhaseMaximum.actual_amplitude_ae
#print axioms OQ14.Packet05BinaryPhaseMaximum.attained_above_peak
