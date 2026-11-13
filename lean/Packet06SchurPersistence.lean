import Packet06RepairLimit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SchurPersistence
open Filter Metric Set Packet06RankOneRepair Packet06ScalarSchur Packet06SchurAnalytic
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem simple_schur_persistence (A : ℕ → ℂ → E →L[ℂ] E) (A₀ : ℂ → E →L[ℂ] E)
    (w : E) (ψ : E →L[ℂ] ℂ) (z₀ : ℂ) (d : ℂ)
    (hA : TendstoLocallyUniformlyOn A A₀ atTop univ)
    (hA₀ : Differentiable ℂ A₀) (hAn : ∀ᶠ n in atTop, Differentiable ℂ (A n))
    (hunit : IsUnit (repair (A₀ z₀) w ψ))
    (hzero : scalar (A₀ z₀) w ψ = 0)
    (hder : HasDerivAt (fun z => scalar (A₀ z) w ψ) d z₀) (hd : d ≠ 0) :
    ∃ z : ℕ → ℂ, Tendsto z atTop (𝓝 z₀) ∧
      ∀ᶠ n in atTop, ¬ IsUnit (A n (z n)) ∧
        deriv (fun v => scalar (A n v) w ψ) (z n) ≠ 0 ∧
        (let u := Ring.inverse (repair (A n (z n)) w ψ) w
         u ≠ 0 ∧ A n (z n) u = 0 ∧ ψ u = 1 ∧
          ∀ x, A n (z n) x = 0 ↔ x = ψ x • u) := by
  obtain ⟨r,hr,hbase,hunitn,_,hconv⟩ :=
    Packet06RepairLimit.locally_uniform_repairs A A₀ w ψ z₀ hA hA₀.continuous hunit
  let U := ball z₀ r
  let S : ℕ → ℂ → ℂ := fun n z => scalar (A n z) w ψ
  let S₀ : ℂ → ℂ := fun z => scalar (A₀ z) w ψ
  have hzU : z₀ ∈ U := mem_ball_self hr
  have hsbase : DifferentiableOn ℂ S₀ U := by
    intro z hz
    exact (scalar_analyticAt A₀ w ψ z (hA₀.analyticAt z) (hbase z hz)).differentiableAt.differentiableWithinAt
  have hsn : ∀ᶠ n in atTop, DifferentiableOn ℂ (S n) U := by
    filter_upwards [hAn,hunitn] with n hn hu z hz
    exact (scalar_analyticAt (A n) w ψ z (hn.analyticAt z) (hu z hz)).differentiableAt.differentiableWithinAt
  have hd' : deriv S₀ z₀ ≠ 0 := by simpa only [S₀,hder.deriv] using hd
  obtain ⟨z,hz,hroots⟩ := Packet06SimpleZero.simple_zero_sequence U isOpen_ball z₀ hzU S S₀
    hsbase hzero hd' hsn hconv
  refine ⟨z,hz,?_⟩
  have hzball : ∀ᶠ n in atTop, z n ∈ U := hz.eventually (isOpen_ball.mem_nhds hzU)
  filter_upwards [hroots,hunitn,hzball] with n hn hunitn hnU
  have hu := hunitn (z n) hnU
  have hz0 : scalar (A n (z n)) w ψ = 0 := hn.1
  have hnunit : ¬ IsUnit (A n (z n)) := by
    intro h
    exact (isUnit_iff_scalar _ w ψ hu).mp h hz0
  exact ⟨hnunit,hn.2,scalar_kernel _ w ψ hu hz0⟩
#print axioms OQ14.Packet06SchurPersistence.simple_schur_persistence
end OQ14.Packet06SchurPersistence
