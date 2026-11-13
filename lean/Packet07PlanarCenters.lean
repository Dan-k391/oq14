import Packet07BinaryLobes

/-! Explicit arbitrary finite planar placement inside a prescribed open patch. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07PlanarCenters
open Set Metric
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := Maxwell.Space

def planeEmbed (u : Plane) : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![u 0, u 1, 0]

theorem planeEmbed_coord (u : Plane) : planeEmbed u 2 = 0 := by simp [planeEmbed]

theorem planeEmbed_injective : Function.Injective planeEmbed := by
  intro u v h
  ext i
  fin_cases i
  · have hh := congrArg (fun x : Space => x 0) h
    simpa [planeEmbed] using hh
  · have hh := congrArg (fun x : Space => x 1) h
    simpa [planeEmbed] using hh

def offset (N : ℕ) (r : ℝ) (i : Fin N) : ℝ := (((i : ℕ) : ℝ) + 1) * r / ((N : ℝ) + 1)
def planarPoint (N : ℕ) (u : Plane) (r : ℝ) (i : Fin N) : Plane := u + EuclideanSpace.single 0 (offset N r i)

theorem offset_positive (N : ℕ) (r : ℝ) (hr : 0 < r) (i : Fin N) : 0 < offset N r i := by
  unfold offset
  positivity

theorem offset_le (N : ℕ) (r : ℝ) (hr : 0 < r) (i : Fin N) : offset N r i ≤ r := by
  unfold offset
  have hi : ((i : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast i.isLt
  have hd : 0 < (N : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hd]
  nlinarith

theorem planarPoint_injective (N : ℕ) (u : Plane) (r : ℝ) (hr : 0 < r) :
    Function.Injective (planarPoint N u r) := by
  intro i j h
  have hc := congrArg (fun x : Plane => x 0) h
  have hden : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hr0 : r ≠ 0 := hr.ne'
  simp only [planarPoint, PiLp.add_apply, EuclideanSpace.single_apply, ite_true] at hc
  have heq : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
    unfold offset at hc
    field_simp at hc
    exact_mod_cast hc.resolve_right hr0
  exact Fin.ext (by exact_mod_cast heq)

theorem planarPoint_mem (N : ℕ) (u : Plane) (r : ℝ) (hr : 0 < r)
    (P : Set Plane) (hP : ball u (2*r) ⊆ P) (i : Fin N) : planarPoint N u r i ∈ P := by
  apply hP
  rw [mem_ball, dist_eq_norm]
  have hdist : planarPoint N u r i - u = EuclideanSpace.single 0 (offset N r i) := by simp [planarPoint]
  rw [hdist, EuclideanSpace.norm_single, Real.norm_eq_abs, abs_of_pos (offset_positive N r hr i)]
  linarith [offset_le N r hr i]

/-- Any nonempty relatively open plane patch contains arbitrarily many distinct
    physical 3D centers, all on the same plane. -/
theorem exists_planar_centers (N : ℕ) (P : Set Plane) (hopen : IsOpen P) (hne : P.Nonempty) :
    ∃ c : Fin N → Plane, Function.Injective c ∧ (∀ i, c i ∈ P) ∧
      Function.Injective (fun i => planeEmbed (c i)) ∧ (∀ i, planeEmbed (c i) 2 = 0) := by
  obtain ⟨u,hu⟩ := hne
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hopen u hu
  let c := planarPoint N u (r/2)
  have hr2 : 0 < r/2 := by positivity
  have hs : ball u (2*(r/2)) ⊆ P := by
    rw [show 2*(r/2)=r by ring]
    exact hball
  refine ⟨c, planarPoint_injective N u _ hr2, ?_, ?_, fun i => planeEmbed_coord (c i)⟩
  · intro i
    exact planarPoint_mem N u _ hr2 P hs i
  · exact planeEmbed_injective.comp (planarPoint_injective N u _ hr2)

/-- Orthogonal projection from physical space to the reference plane. -/
def planeProject (x : Space) : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x 0, x 1]

theorem planeProject_embed (u : Plane) : planeProject (planeEmbed u) = u := by
  ext i
  fin_cases i <;> simp [planeProject, planeEmbed]

theorem planeProject_sub (x y : Space) : planeProject (x-y) = planeProject x - planeProject y := by
  ext i
  fin_cases i <;> simp [planeProject, PiLp.sub_apply]

theorem planeProject_norm_le (x : Space) : ‖planeProject x‖ ≤ ‖x‖ := by
  have hp := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (planeProject x)
  have hx := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x
  simp only [Fin.sum_univ_two, Fin.sum_univ_three] at hp hx
  have h0 : planeProject x 0 = x 0 := by simp [planeProject]
  have h1 : planeProject x 1 = x 1 := by simp [planeProject]
  rw [h0,h1] at hp
  nlinarith [norm_nonneg (planeProject x), norm_nonneg x, sq_nonneg ‖x 2‖]

/-- Orthogonal projection does not enlarge any physical distance. -/
theorem planeProject_dist_le (x y : Space) : dist (planeProject x) (planeProject y) ≤ dist x y := by
  simp only [dist_eq_norm, ← planeProject_sub]
  exact planeProject_norm_le (x-y)

end OQ14.Packet07PlanarCenters
#print axioms OQ14.Packet07PlanarCenters.planeEmbed_coord
#print axioms OQ14.Packet07PlanarCenters.planeEmbed_injective
#print axioms OQ14.Packet07PlanarCenters.offset_positive
#print axioms OQ14.Packet07PlanarCenters.offset_le
#print axioms OQ14.Packet07PlanarCenters.planarPoint_injective
#print axioms OQ14.Packet07PlanarCenters.planarPoint_mem
#print axioms OQ14.Packet07PlanarCenters.exists_planar_centers

#print axioms OQ14.Packet07PlanarCenters.planeProject_embed
#print axioms OQ14.Packet07PlanarCenters.planeProject_sub
#print axioms OQ14.Packet07PlanarCenters.planeProject_norm_le
#print axioms OQ14.Packet07PlanarCenters.planeProject_dist_le
