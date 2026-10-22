import PointMaxwellTail
import SphereMagneticParity
import MaxwellPlaneL1

/-! Genuine point Herglotz columns have integrable whole-plane coherent flux. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.HerglotzPointTail
open MeasureTheory Metric Set SphereReactionKernel SphereMagneticKernel
open Maxwell (conjugate)
open MaxwellPlaneTail (planePoint planePoint_norm planePoint_continuous)
open scoped ComplexConjugate Topology
abbrev Plane := PlaneInverseCube.Plane

def outgoingFlux (k l : ℝ) (x y z : Space) (j m : Fin 3) : ℂ :=
  crossProduct (fun i => DyadicKernel.dyadic k (x-y) i j)
    (conjugate (fun i => magneticDyadic l (x-z) i m)) 2

def regularFlux (k : ℝ) (x y z : Space) (j m : Fin 3) : ℂ :=
  crossProduct (fun i => J k (x-y) i j) (conjugate (fun i => K k (x-z) i m)) 2

theorem flux_expansion (k : ℝ) (x y z : Space) (hk : k ≠ 0)
    (hy : x-y ≠ 0) (hz : x-z ≠ 0) (j m : Fin 3) :
    regularFlux k x y z j m = (1/4 : ℂ)*
      (outgoingFlux k k x y z j m+outgoingFlux k (-k) x y z j m-
        outgoingFlux (-k) k x y z j m-outgoingFlux (-k) (-k) x y z j m) := by
  unfold regularFlux outgoingFlux
  change J k (x-y) 0 j*star (K k (x-z) 1 m)-J k (x-y) 1 j*star (K k (x-z) 0 m) = _
  rw [SphereDyadicTransform.J_dyadic k (x-y) hk hy 0 j,
    SphereDyadicTransform.J_dyadic k (x-y) hk hy 1 j,
    K_magnetic k (x-z) hk hz 1 m, K_magnetic k (x-z) hk hz 0 m]
  simp only [map_div, map_add, map_mul, Complex.star_def, map_ofNat, Complex.conj_I]
  simp [cross_apply, conjugate]
  field_simp
  ring_nf
  norm_num [Complex.I_sq, Complex.conj_ofNat]
  ring

theorem regular_flux_tail (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0) (x y z : Space)
    (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (hp : x 2=0)
    (hy : y ∈ closedBall 0 R) (hz : z ∈ closedBall 0 R) (j m : Fin 3) :
    ‖regularFlux k x y z j m‖ ≤ PointMaxwellTail.tailConstant k k R/‖x‖^3 := by
  have hxy := (ScalarRadiation.distance_lower_bound R hR x y hx hy).2.1
  have hxz := (ScalarRadiation.distance_lower_bound R hR x z hx hz).2.1
  have h₁ := PointMaxwellTail.flux_tail k k R hR x y z hx hx₂ hp hy hz j m
  have h₂ := PointMaxwellTail.flux_tail k (-k) R hR x y z hx hx₂ hp hy hz j m
  have h₃ := PointMaxwellTail.flux_tail (-k) k R hR x y z hx hx₂ hp hy hz j m
  have h₄ := PointMaxwellTail.flux_tail (-k) (-k) R hR x y z hx hx₂ hp hy hz j m
  simp only [PointMaxwellTail.tailConstant, MaxwellPlaneTail.electricErrorConstant,
    MaxwellPlaneTail.magneticErrorConstant, MaxwellPlaneTail.leadingConstant, neg_sq, abs_neg] at h₂ h₃ h₄
  change ‖outgoingFlux k k x y z j m‖ ≤ _ at h₁
  change ‖outgoingFlux k (-k) x y z j m‖ ≤ _ at h₂
  change ‖outgoingFlux (-k) k x y z j m‖ ≤ _ at h₃
  change ‖outgoingFlux (-k) (-k) x y z j m‖ ≤ _ at h₄
  rw [flux_expansion k x y z hk hxy hxz j m, norm_mul]
  have hc : ‖(1/4 : ℂ)‖=(1/4 : ℝ) := by norm_num
  rw [hc]
  have hn : ‖outgoingFlux k k x y z j m+outgoingFlux k (-k) x y z j m-
      outgoingFlux (-k) k x y z j m-outgoingFlux (-k) (-k) x y z j m‖ ≤
      ‖outgoingFlux k k x y z j m‖+‖outgoingFlux k (-k) x y z j m‖+
        ‖outgoingFlux (-k) k x y z j m‖+‖outgoingFlux (-k) (-k) x y z j m‖ :=
    (norm_sub_le _ _).trans (add_le_add_right ((norm_sub_le _ _).trans
      (add_le_add_right (norm_add_le _ _) _)) _)
  apply (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 1/4)).trans
  unfold PointMaxwellTail.tailConstant MaxwellPlaneTail.electricErrorConstant
    MaxwellPlaneTail.magneticErrorConstant MaxwellPlaneTail.leadingConstant at h₁ ⊢
  linarith

theorem regular_flux_continuous (k : ℝ) (y z : Space) (j m : Fin 3) :
    Continuous (fun q : Plane => regularFlux k (planePoint q) y z j m) := by
  have hJ (i : Fin 3) : Continuous (fun q : Plane => J k (planePoint q-y) i j) :=
    (J_continuous k i j).comp (planePoint_continuous.sub continuous_const)
  have hK (i : Fin 3) : Continuous (fun q : Plane => K k (planePoint q-z) i m) :=
    (K_continuous k i m).comp (planePoint_continuous.sub continuous_const)
  exact ((hJ 0).mul (hK 1).star).sub ((hJ 1).mul (hK 0).star)

theorem global_envelope (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0) :
    ∃ w : Plane → ℝ, Integrable w ∧ (∀ q, 0 ≤ w q) ∧
      ∀ y z : Space, y ∈ closedBall 0 R → z ∈ closedBall 0 R →
        ∀ j m : Fin 3, ∀ q : Plane, ‖regularFlux k (planePoint q) y z j m‖ ≤ w q := by
  let T := max (2*R) 2+1
  let A := 2*(entryBound k)^2
  let B := PointMaxwellTail.tailConstant k k R
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right (2*R) 2]
  have hT₂ : 2 ≤ T := by dsimp [T]; linarith [le_max_right (2*R) 2]
  have hTR : 2*R ≤ T := by dsimp [T]; linarith [le_max_left (2*R) 2]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by
    dsimp [B, PointMaxwellTail.tailConstant, MaxwellPlaneTail.electricErrorConstant,
      MaxwellPlaneTail.magneticErrorConstant, MaxwellPlaneTail.leadingConstant]
    positivity
  refine ⟨MaxwellPlaneL1.envelope T A B, MaxwellPlaneL1.envelope_integrable T A B hT,
    MaxwellPlaneL1.envelope_nonnegative T A B hA hB, ?_⟩
  intro y z hy hz j m q
  by_cases hq : ‖q‖ ≤ T
  · have hb := MaxwellPlaneTail.cross_norm_bound
      (fun i => J k (planePoint q-y) i j) (fun i => K k (planePoint q-z) i m)
      (entryBound k) (entryBound k) (entryBound_nonnegative k) (entryBound_nonnegative k)
      (fun i => J_bound k _ i j) (fun i => K_bound k _ i m) 2
    have he : MaxwellPlaneL1.envelope T A B q=A := by
      simp [MaxwellPlaneL1.envelope, PlaneInverseCube.profile, Set.indicator,
        mem_closedBall, dist_zero_right, hq, not_lt.mpr hq]
    rw [he]
    exact hb.trans_eq (by dsimp [A]; ring)
  · have ht : T < ‖q‖ := lt_of_not_ge hq
    have hb := regular_flux_tail k R hR hk (planePoint q) y z
      (by rw [planePoint_norm]; linarith) (by rw [planePoint_norm]; linarith) (by rfl) hy hz j m
    have he : MaxwellPlaneL1.envelope T A B q=B/‖q‖^3 := by
      simp [MaxwellPlaneL1.envelope, PlaneInverseCube.profile, Set.indicator,
        mem_closedBall, dist_zero_right, hq, ht, div_eq_mul_inv]
    rw [he]
    simpa only [planePoint_norm] using hb

theorem whole_plane_bound (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y z : Space, y ∈ closedBall 0 R → z ∈ closedBall 0 R →
      ∀ j m : Fin 3,
        Integrable (fun q : Plane => regularFlux k (planePoint q) y z j m) ∧
        (∫ q : Plane, ‖regularFlux k (planePoint q) y z j m‖) ≤ C := by
  obtain ⟨w, hw, hpos, hb⟩ := global_envelope k R hR hk
  refine ⟨∫ q, w q, integral_nonneg hpos, ?_⟩
  intro y z hy hz j m
  have hi : Integrable (fun q : Plane => regularFlux k (planePoint q) y z j m) :=
    hw.mono' (regular_flux_continuous k y z j m).aestronglyMeasurable
      (Filter.Eventually.of_forall (hb y z hy hz j m))
  exact ⟨hi, integral_mono_ae hi.norm hw (Filter.Eventually.of_forall (hb y z hy hz j m))⟩

theorem plane_tail_mass (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0) (y z : Space)
    (hy : y ∈ closedBall 0 R) (hz : z ∈ closedBall 0 R) (j m : Fin 3)
    (T : ℝ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) :
    (∫ q : Plane in {q : Plane | T < ‖q‖}, ‖regularFlux k (planePoint q) y z j m‖) ≤
      PointMaxwellTail.tailConstant k k R*PlaneInverseCube.diskConstant/T := by
  apply PlaneInverseCube.tail_integral_bound T _ (by linarith)
    (regular_flux_continuous k y z j m).aestronglyMeasurable.restrict
  intro q hq
  simpa only [planePoint_norm] using regular_flux_tail k R hR hk (planePoint q) y z
    (by rw [planePoint_norm]; linarith) (by rw [planePoint_norm]; linarith) (by rfl) hy hz j m
end OQ14.HerglotzPointTail
#print axioms OQ14.HerglotzPointTail.flux_expansion
#print axioms OQ14.HerglotzPointTail.regular_flux_tail
#print axioms OQ14.HerglotzPointTail.regular_flux_continuous

#print axioms OQ14.HerglotzPointTail.global_envelope
#print axioms OQ14.HerglotzPointTail.whole_plane_bound
#print axioms OQ14.HerglotzPointTail.plane_tail_mass
