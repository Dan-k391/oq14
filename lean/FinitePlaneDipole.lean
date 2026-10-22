import StaticBallPlaneDipole

/-! Exact actual static plane profiles of finite uniformly polarized balls. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.FinitePlaneDipole

open MeasureTheory Metric StaticPlaneKernel NewtonSeparatedResponse
open scoped Topology BigOperators

abbrev Vector := StaticBallNewton.Vector

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def source (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (j : Fin 3) (y : Space) : ℂ :=
  ∑ l : ι, StaticBallPlaneDipole.source (p l) (r l) (P l) j y

def dipoles (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (x : Space) (i : Fin 3) : ℂ :=
  ∑ l : ι, StaticBallPlaneDipole.dipole (p l) (r l) (P l) x i

omit [DecidableEq ι] in
theorem source_integrable (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (j : Fin 3) :
    Integrable (source p r P j) :=
  integrable_finset_sum _ (fun l _ => StaticBallDipole.indicator_integrable (p l) (r l) (P l j))

theorem source_ae (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (j : Fin 3) :
    source p r P j =ᵐ[volume]
      fun y => FiniteSphereStatic.sumSource p r P (VectorFourier.coordinateMap y) j :=
  (FiniteSphereStatic.sumSource_ae p r P j).symm

omit [DecidableEq ι] in
theorem field_sum (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (d : ℝ)
    (hd : 0 < d) (hh : ∀ l, d+r l ≤ |p l 2|) (q : PlaneInverseCube.Plane) (i j : Fin 3) :
    StaticPlaneSource.field (source p r P j) i j q=
      ∑ l : ι, StaticPlaneSource.field (StaticBallPlaneDipole.source (p l) (r l) (P l) j) i j q := by
  have hx : MaxwellPlaneTail.planePoint q ∈ strip d := by
    simp [strip, MaxwellPlaneTail.planePoint, hd]
  have hi (l : ι) : Integrable (fun y =>
      GreenKernel.phiHessian 0 (MaxwellPlaneTail.planePoint q-y) i j*
        StaticBallPlaneDipole.source (p l) (r l) (P l) j y) := by
    simpa only [mul_comm] using scalar_integrand_integrable
      (StaticBallPlaneDipole.source (p l) (r l) (P l) j)
      (StaticBallDipole.indicator_integrable (p l) (r l) (P l j)) d hd
      (StaticBallPlaneDipole.source_gap (p l) (r l) d (P l) (hh l) j)
      (MaxwellPlaneTail.planePoint q) hx i j
  unfold StaticPlaneSource.field
  calc
    _ = ∫ y, ∑ l : ι, GreenKernel.phiHessian 0 (MaxwellPlaneTail.planePoint q-y) i j*
        StaticBallPlaneDipole.source (p l) (r l) (P l) j y := by
      apply integral_congr_ae
      filter_upwards with y
      exact Finset.mul_sum _ _ _
    _ = _ := integral_finset_sum _ (fun l _ => hi l)

omit [DecidableEq ι] in
theorem plane_response_eq_dipoles (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (d : ℝ)
    (hr : ∀ l, 0 < r l) (hd : 0 < d) (hh : ∀ l, d+r l ≤ |p l 2|)
    (q : PlaneInverseCube.Plane) (i : Fin 3) :
    response (source p r P) (MaxwellPlaneTail.planePoint q) i=
      dipoles p r P (MaxwellPlaneTail.planePoint q) i := by
  rw [response_plane]
  simp only [field_sum p r P d hd hh q]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  exact StaticBallPlaneDipole.plane_response_eq_dipole (p l) (r l) d (hr l) hd (hh l) (P l) i q

end OQ14.FinitePlaneDipole

#print axioms OQ14.FinitePlaneDipole.source_integrable
#print axioms OQ14.FinitePlaneDipole.source_ae
#print axioms OQ14.FinitePlaneDipole.field_sum
#print axioms OQ14.FinitePlaneDipole.plane_response_eq_dipoles
