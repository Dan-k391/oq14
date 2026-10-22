import HerglotzParityPlane

/-! Genuine finite-center parity Herglotz fields and their coherent plane flux. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteHerglotzFlux
open MeasureTheory Metric Set SphereReactionKernel SphereMagneticParity
open scoped ComplexConjugate Topology
abbrev Plane := PlaneInverseCube.Plane
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def electric (k : ℝ) (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) : Maxwell.Field :=
  fun x i => ∑ s, A s*reaction (e s) k x (p s) i (j s)

def magnetic (k : ℝ) (h : κ → Bool) (p : κ → Space) (j : κ → Fin 3) (A : κ → ℂ) : Maxwell.Field :=
  fun x i => ∑ s, A s*magneticReaction (h s) k x (p s) i (j s)

def flux (k : ℝ) (e : ι → Bool) (h : κ → Bool) (p : ι → Space) (q : κ → Space)
    (j : ι → Fin 3) (m : κ → Fin 3) (A : ι → ℂ) (B : κ → ℂ) (x : Space) : ℂ :=
  crossProduct (electric k e p j A x) (Maxwell.conjugate (magnetic k h q m B x)) 2

theorem flux_expansion (k : ℝ) (e : ι → Bool) (h : κ → Bool) (p : ι → Space) (q : κ → Space)
    (j : ι → Fin 3) (m : κ → Fin 3) (A : ι → ℂ) (B : κ → ℂ) (x : Space) :
    flux k e h p q j m A B x = ∑ s, ∑ t,
      (A s*conj (B t))*HerglotzParityPlane.flux (e s) (h t) k x (p s) (q t) (j s) (m t) := by
  classical
  unfold flux HerglotzParityPlane.flux
  change (∑ s, A s*reaction (e s) k x (p s) 0 (j s))*
      star (∑ t, B t*magneticReaction (h t) k x (q t) 1 (m t))-
    (∑ s, A s*reaction (e s) k x (p s) 1 (j s))*
      star (∑ t, B t*magneticReaction (h t) k x (q t) 0 (m t)) = _
  simp only [star_sum, star_mul]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp [cross_apply, Maxwell.conjugate]
  ring
private theorem sum_norm_bound (f : ι → κ → ℂ) :
    ‖∑ s, ∑ t, f s t‖ ≤ ∑ s, ∑ t, ‖f s t‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))

theorem whole_plane_bound (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : ι → Bool) (h : κ → Bool) (p : ι → Space) (q : κ → Space)
      (j : ι → Fin 3) (m : κ → Fin 3) (A : ι → ℂ) (B : κ → ℂ),
      (∀ s, p s ∈ closedBall 0 R) → (∀ t, q t ∈ closedBall 0 R) →
      Integrable (fun u : Plane => flux k e h p q j m A B (MaxwellPlaneTail.planePoint u)) ∧
      (∫ u : Plane, ‖flux k e h p q j m A B (MaxwellPlaneTail.planePoint u)‖) ≤
        C*(∑ s, ‖A s‖)*(∑ t, ‖B t‖) := by
  classical
  obtain ⟨C,hC,hb⟩ := HerglotzParityPlane.whole_plane_bound k R hR hk
  refine ⟨C,hC,?_⟩
  intro e h p q j m A B hp hq
  let f := fun s t (u : Plane) => (A s*conj (B t))*
    HerglotzParityPlane.flux (e s) (h t) k (MaxwellPlaneTail.planePoint u) (p s) (q t) (j s) (m t)
  have hi (s : ι) (t : κ) : Integrable (f s t) :=
    (hb (e s) (h t) (p s) (q t) (hp s) (hq t) (j s) (m t)).1.const_mul _
  have hm (s : ι) (t : κ) : (∫ u : Plane, ‖f s t u‖) ≤ ‖A s‖*‖B t‖*C := by
    simp only [f, norm_mul, Complex.norm_conj, integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (hb (e s) (h t) (p s) (q t) (hp s) (hq t) (j s) (m t)).2 (by positivity)
  have he (u : Plane) : flux k e h p q j m A B (MaxwellPlaneTail.planePoint u) = ∑ s, ∑ t, f s t u :=
    flux_expansion k e h p q j m A B _
  have hs : Integrable (fun u : Plane => ∑ s, ∑ t, f s t u) :=
    integrable_finset_sum Finset.univ (fun s _ => integrable_finset_sum Finset.univ (fun t _ => hi s t))
  simp_rw [he]
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∫ u : Plane, ∑ s, ∑ t, ‖f s t u‖ := integral_mono_ae hs.norm
      (integrable_finset_sum Finset.univ (fun s _ => integrable_finset_sum Finset.univ (fun t _ => (hi s t).norm)))
      (Filter.Eventually.of_forall (fun u => sum_norm_bound (fun s t => f s t u)))
    _ = ∑ s, ∑ t, ∫ u : Plane, ‖f s t u‖ := by
      rw [integral_finset_sum _ (fun s _ => integrable_finset_sum Finset.univ (fun t _ => (hi s t).norm))]
      exact Finset.sum_congr rfl (fun s _ => integral_finset_sum _ (fun t _ => (hi s t).norm))
    _ ≤ ∑ s, ∑ t, ‖A s‖*‖B t‖*C := Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun t _ => hm s t))
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro s _
      ring

theorem flux_tail (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0)
    (e : ι → Bool) (h : κ → Bool) (p : ι → Space) (q : κ → Space)
    (j : ι → Fin 3) (m : κ → Fin 3) (A : ι → ℂ) (B : κ → ℂ)
    (hp : ∀ s, p s ∈ closedBall 0 R) (hq : ∀ t, q t ∈ closedBall 0 R)
    (x : Space) (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (hplane : x 2=0) :
    ‖flux k e h p q j m A B x‖ ≤
      (PointMaxwellTail.tailConstant k k R/‖x‖^3)*(∑ s, ‖A s‖)*(∑ t, ‖B t‖) := by
  rw [flux_expansion]
  apply (sum_norm_bound _).trans
  calc
    _ ≤ ∑ s, ∑ t, ‖A s‖*‖B t‖*(PointMaxwellTail.tailConstant k k R/‖x‖^3) := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      rw [norm_mul, norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left
        (HerglotzParityPlane.flux_tail (e s) (h t) k R hR hk x (p s) (q t) hx hx₂ hplane (hp s) (hq t) (j s) (m t))
        (by positivity)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro s _
      ring

theorem plane_tail_mass (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0)
    (e : ι → Bool) (h : κ → Bool) (p : ι → Space) (q : κ → Space)
    (j : ι → Fin 3) (m : κ → Fin 3) (A : ι → ℂ) (B : κ → ℂ)
    (hp : ∀ s, p s ∈ closedBall 0 R) (hq : ∀ t, q t ∈ closedBall 0 R)
    (T : ℝ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) :
    (∫ u : Plane in {u : Plane | T < ‖u‖},
      ‖flux k e h p q j m A B (MaxwellPlaneTail.planePoint u)‖) ≤
      (PointMaxwellTail.tailConstant k k R*(∑ s, ‖A s‖)*(∑ t, ‖B t‖))*PlaneInverseCube.diskConstant/T := by
  obtain ⟨C,_,hb⟩ := whole_plane_bound (ι := ι) (κ := κ) k R hR hk
  have hi := (hb e h p q j m A B hp hq).1
  apply PlaneInverseCube.tail_integral_bound T _ (by linarith) hi.aestronglyMeasurable.restrict
  intro u hu
  have ht := flux_tail k R hR hk e h p q j m A B hp hq (MaxwellPlaneTail.planePoint u)
    (by rw [MaxwellPlaneTail.planePoint_norm]; linarith)
    (by rw [MaxwellPlaneTail.planePoint_norm]; linarith) (by rfl)
  rw [MaxwellPlaneTail.planePoint_norm] at ht
  exact ht.trans_eq (by ring)
end OQ14.FiniteHerglotzFlux
#print axioms OQ14.FiniteHerglotzFlux.flux_expansion
#print axioms OQ14.FiniteHerglotzFlux.whole_plane_bound
#print axioms OQ14.FiniteHerglotzFlux.flux_tail

#print axioms OQ14.FiniteHerglotzFlux.plane_tail_mass
