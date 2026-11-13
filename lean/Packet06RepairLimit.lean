import Packet06SchurLimit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06RepairLimit
open Filter Metric Set Packet06RankOneRepair Packet06ScalarSchur
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem locally_uniform_repairs (A : ℕ → ℂ → E →L[ℂ] E) (A₀ : ℂ → E →L[ℂ] E)
    (w : E) (ψ : E →L[ℂ] ℂ) (z₀ : ℂ)
    (hA : TendstoLocallyUniformlyOn A A₀ atTop univ)
    (hcont : Continuous A₀) (hunit : IsUnit (repair (A₀ z₀) w ψ)) :
    ∃ r > 0,
      (∀ z ∈ ball z₀ r, IsUnit (repair (A₀ z) w ψ)) ∧
      (∀ᶠ n in atTop, ∀ z ∈ ball z₀ r, IsUnit (repair (A n z) w ψ)) ∧
      TendstoLocallyUniformlyOn
        (fun n z => Ring.inverse (repair (A n z) w ψ))
        (fun z => Ring.inverse (repair (A₀ z) w ψ)) atTop (ball z₀ r) ∧
      TendstoLocallyUniformlyOn (fun n z => scalar (A n z) w ψ)
        (fun z => scalar (A₀ z) w ψ) atTop (ball z₀ r) := by
  let C : ℕ → ℂ → E →L[ℂ] E := fun n z => repair (A n z) w ψ
  let C₀ : ℂ → E →L[ℂ] E := fun z => repair (A₀ z) w ψ
  have hCcont : Continuous C₀ := hcont.add continuous_const
  have hC : TendstoLocallyUniformlyOn C C₀ atTop univ := by
    apply Packet06SchurLimit.locally_uniform_comp univ A A₀ (fun B => repair B w ψ) hA hcont.continuousOn
    intro x hx
    exact (continuous_id.add continuous_const).continuousAt
  have hnear : {B : E →L[ℂ] E | IsUnit B} ∈ 𝓝 (C₀ z₀) := Units.isOpen.mem_nhds hunit
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hz := hCcont.continuousAt.tendsto (Metric.ball_mem_nhds (C₀ z₀) (show 0 < δ/2 by positivity))
  obtain ⟨t,ht,htn⟩ := (Metric.tendstoLocallyUniformlyOn_iff.mp hC) (δ/2) (by positivity) z₀ (mem_univ _)
  have ht' : t ∈ 𝓝 z₀ := by simpa only [nhdsWithin_univ] using ht
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (inter_mem ht' hz)
  have hC₀unit : ∀ z ∈ ball z₀ r, IsUnit (C₀ z) := by
    intro z hzball
    have hz' := (hrsub hzball).2
    apply hδsub
    change C₀ z ∈ ball (C₀ z₀) (δ/2) at hz'
    rw [mem_ball] at hz' ⊢
    linarith
  have hCnunit : ∀ᶠ n in atTop, ∀ z ∈ ball z₀ r, IsUnit (C n z) := by
    filter_upwards [htn] with n hn z hzball
    have hz' := hrsub hzball
    apply hδsub
    rw [mem_ball]
    have h1 := hn z hz'.1
    have h2 := hz'.2
    change C₀ z ∈ ball (C₀ z₀) (δ/2) at h2
    rw [mem_ball] at h2
    have htri := dist_triangle (C n z) (C₀ z) (C₀ z₀)
    rw [dist_comm] at h1
    linarith
  have hinv : TendstoLocallyUniformlyOn (fun n z => Ring.inverse (C n z))
      (fun z => Ring.inverse (C₀ z)) atTop (ball z₀ r) := by
    apply Packet06SchurLimit.locally_uniform_comp (ball z₀ r) C C₀ Ring.inverse
      (hC.mono (subset_univ _)) hCcont.continuousOn
    intro z hz
    exact ((analyticOnNhd_inverse (𝕜 := ℂ) _ (hC₀unit z hz)).continuousAt)
  have hscalar : TendstoLocallyUniformlyOn (fun n z => scalar (A n z) w ψ)
      (fun z => scalar (A₀ z) w ψ) atTop (ball z₀ r) := by
    let G : (E →L[ℂ] E) → ℂ := fun B => 1-ψ (B w)
    have hG : Continuous G := continuous_const.sub (ψ.continuous.comp ((ContinuousLinearMap.apply ℂ E w).continuous))
    have h := Packet06SchurLimit.locally_uniform_comp (ball z₀ r)
      (fun n z => Ring.inverse (C n z)) (fun z => Ring.inverse (C₀ z)) G hinv ?_ (fun _ _ => hG.continuousAt)
    · exact h
    · have hcontinv : ContinuousOn (fun z => Ring.inverse (C₀ z)) (ball z₀ r) := by
        intro z hz
        exact ((analyticOnNhd_inverse (𝕜 := ℂ) _ (hC₀unit z hz)).continuousAt.comp
          hCcont.continuousAt).continuousWithinAt
      exact hcontinv
  exact ⟨r,hr,hC₀unit,hCnunit,hinv,hscalar⟩
#print axioms OQ14.Packet06RepairLimit.locally_uniform_repairs
end OQ14.Packet06RepairLimit
