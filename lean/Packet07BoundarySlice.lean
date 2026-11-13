import Packet07BoundaryNormalSign

/-! Exact phase orientation on a differentiable normal slice. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundarySlice
open Set Packet07BoundaryTriangular

theorem positive_slice (F : Point → ℝ) (U : Set Point) (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (u : Plane) (lo hi z r : ℝ)
    (hlo : lo ≤ z) (hhi : z ≤ hi) (hrlo : lo ≤ r) (hrhi : r ≤ hi)
    (hseg : ∀ t ∈ Icc lo hi, (u,t) ∈ U)
    (hder : ∀ t ∈ Icc lo hi, 0 < fderiv ℝ F (u,t) (0,1)) (hroot : F (u,r) = 0) :
    0 < F (u,z) ↔ r < z := by
  let f : ℝ → ℝ := fun t => F (u,t)
  have hdiff (t : ℝ) (ht : t ∈ Icc lo hi) :
      HasDerivAt f (fderiv ℝ F (u,t) (0,1)) t := by
    have hf : DifferentiableAt ℝ F (u,t) :=
      (hF.contDiffAt (hU.mem_nhds (hseg t ht))).differentiableAt (by norm_num)
    have ht' : HasDerivAt (fun w : ℝ => (u,w)) ((0,1) : Point) t :=
      (hasDerivAt_const t u).prodMk (hasDerivAt_id t)
    exact hf.hasFDerivAt.comp_hasDerivAt t ht'
  have hcont : ContinuousOn f (Icc lo hi) := fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Icc lo hi) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc lo hi) hcont
    intro t ht
    have ht' : t ∈ Icc lo hi := interior_subset ht
    rw [(hdiff t ht').deriv]
    exact hder t ht'
  exact Packet07BoundarySides.increasing_side hmono ⟨hlo,hhi⟩ ⟨hrlo,hrhi⟩ hroot

theorem negative_slice (F : Point → ℝ) (U : Set Point) (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F U) (u : Plane) (lo hi z r : ℝ)
    (hlo : lo ≤ z) (hhi : z ≤ hi) (hrlo : lo ≤ r) (hrhi : r ≤ hi)
    (hseg : ∀ t ∈ Icc lo hi, (u,t) ∈ U)
    (hder : ∀ t ∈ Icc lo hi, fderiv ℝ F (u,t) (0,1) < 0) (hroot : F (u,r) = 0) :
    0 < F (u,z) ↔ z < r := by
  let f : ℝ → ℝ := fun t => F (u,t)
  have hdiff (t : ℝ) (ht : t ∈ Icc lo hi) :
      HasDerivAt f (fderiv ℝ F (u,t) (0,1)) t := by
    have hf : DifferentiableAt ℝ F (u,t) :=
      (hF.contDiffAt (hU.mem_nhds (hseg t ht))).differentiableAt (by norm_num)
    have ht' : HasDerivAt (fun w : ℝ => (u,w)) ((0,1) : Point) t :=
      (hasDerivAt_const t u).prodMk (hasDerivAt_id t)
    exact hf.hasFDerivAt.comp_hasDerivAt t ht'
  have hcont : ContinuousOn f (Icc lo hi) := fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn f (Icc lo hi) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc lo hi) hcont
    intro t ht
    have ht' : t ∈ Icc lo hi := interior_subset ht
    rw [(hdiff t ht').deriv]
    exact hder t ht'
  exact Packet07BoundarySides.decreasing_side hanti ⟨hlo,hhi⟩ ⟨hrlo,hrhi⟩ hroot

end OQ14.Packet07BoundarySlice
#print axioms OQ14.Packet07BoundarySlice.positive_slice
#print axioms OQ14.Packet07BoundarySlice.negative_slice
