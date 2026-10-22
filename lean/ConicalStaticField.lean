import ConicalStaticDivergence
import ConicalWeakCurl
import ConicalNontrivial

/-! A genuine locally square-integrable singular static transmission field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.ConicalStaticField
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1
  OQ14.ConicalCapField
open scoped Topology ENNReal

/-- The three displayed identities specify the actual static distribution equations. -/
def IsStaticTransmission (ν a d t : ℝ) : Prop :=
  (∀ (ψ : Space → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ i : Fin 3,
    (∫ x : Space, potential ν a t x*fderiv ℝ ψ x (basis i)) =
      -(∫ x : Space, electric ν a t x i*ψ x)) ∧
  (∀ (ψ : Space → ℝ), ContDiff ℝ 2 ψ → HasCompactSupport ψ →
    ConicalWeakCurl.weakCurlPairing ν a t ψ = 0) ∧
  (∀ (ψ : Space → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
    (∫ x : Space, permittivity d t x*fderiv ℝ ψ x (electric ν a t x)) = 0)

theorem permittivity_bounds (d t : ℝ) (hd : 0 ≤ d) (x : Space) :
    1 ≤ permittivity d t x ∧ permittivity d t x ≤ 1+d := by
  unfold permittivity CapSturmLiouville.coefficient
  split_ifs <;> constructor <;> linarith

theorem shooting_static_transmission (a d t : ℝ) (ha : a ∈ Ioo (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a = 0) :
    IsStaticTransmission (CapAngularShooting.exponent a) a d t := by
  have hν := (CapAngularShooting.exponent_range a ha).1
  exact ⟨fun ψ hψ hc i => ConicalWeakGradient.weak_partial _ a t hν ⟨ha.1.le,ha.2.le⟩ ht ht1 i ψ hψ hc,
    fun ψ hψ hc => ConicalWeakCurl.weak_curl_zero _ a t hν ⟨ha.1.le,ha.2.le⟩ ht ht1 ψ hψ hc,
    fun ψ hψ hc => ConicalStaticDivergence.shooting_weak_divergence a d t ha ht ht1 hroot ψ hψ hc⟩

theorem exists_singular_static_transmission (d t : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ a ∈ Ioo (0 : ℝ) 2, CapAngularShooting.exponent a ∈ Ioo (0 : ℝ) 1 ∧
      IsStaticTransmission (CapAngularShooting.exponent a) a d t ∧
      (∀ R : ℝ, MemLp (potential (CapAngularShooting.exponent a) a t) 2 (volume.restrict (closedBall 0 R)) ∧
        MemLp (electric (CapAngularShooting.exponent a) a t) 2 (volume.restrict (closedBall 0 R))) ∧
      (∃ S : Set Sphere, IsOpen S ∧ S.Nonempty ∧ 0 < angularMeasure S ∧
        ∀ M : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ n ∈ S,
          M < ‖electric (CapAngularShooting.exponent a) a t (r • (n : Space))‖) ∧
      (∃ S : Set Sphere, IsOpen S ∧ S.Nonempty ∧ 0 < angularMeasure S ∧
        ∀ n ∈ S, 0 < ‖SphereCapH1.gradient a t n‖) := by
  obtain ⟨a,ha,hroot⟩ := CapAngularShooting.exists_root d t hd ht ht1
  have hν := CapAngularShooting.exponent_range a ha
  refine ⟨a,ha,hν,shooting_static_transmission a d t ha ht ht1 hroot,?_,
    ConicalNontrivial.exists_open_cone_blowup _ a t hν ⟨ha.1.le,ha.2.le⟩ ht ht1,
    ConicalNontrivial.exists_open_gradient_positive a t ha ht ht1⟩
  intro R
  exact ⟨potential_memLp_two_ball _ a t R hν.1.le ⟨ha.1.le,ha.2.le⟩ ht ht1,
    electric_memLp_two_ball _ a t R hν.1.le ⟨ha.1.le,ha.2.le⟩ ht ht1⟩

end OQ14.ConicalStaticField

#print axioms OQ14.ConicalStaticField.permittivity_bounds
#print axioms OQ14.ConicalStaticField.shooting_static_transmission
#print axioms OQ14.ConicalStaticField.exists_singular_static_transmission
