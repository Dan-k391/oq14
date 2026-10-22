import SphereReactionDipole

/-! Actual finite-ball reaction fields and their derived point-moment errors. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.FiniteSphereReaction

open MeasureTheory Metric SphereReactionKernel
open scoped Topology BigOperators

abbrev Vector := StaticBallNewton.Vector

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_sum_ae (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (j : Fin 3) :
    (fun y => FiniteSphereStatic.sumSource p r P (VectorFourier.coordinateMap y) j) =ᵐ[volume]
      fun y => ∑ l : ι, StaticBallCentered.source (p l) (r l) (P l) (VectorFourier.coordinateMap y) j := by
  have hs : ∀ᵐ y : Space, ∀ l : ι,
      StaticBallCentered.source (p l) (r l) (P l) (VectorFourier.coordinateMap y) j =
        (ball (p l) (r l)).indicator (fun _ => P l j) y :=
    ae_all_iff.mpr (fun l => StaticBallCentered.source_ae (p l) (r l) (P l) j)
  filter_upwards [FiniteSphereStatic.sumSource_ae p r P j, hs] with y hy hs
  rw [hy]
  exact Finset.sum_congr rfl (fun l _ => (hs l).symm)

theorem source_integrable (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (j : Fin 3) :
    Integrable (fun y => FiniteSphereStatic.sumSource p r P (VectorFourier.coordinateMap y) j) :=
  (integrable_finset_sum Finset.univ (fun l _ =>
    StaticBallDipole.source_integrable (p l) (r l) (P l) j)).congr (source_sum_ae p r P j).symm

theorem reaction_sum (electric : Bool) (k : ℝ) (x : Space) (i j : Fin 3)
    (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) :
    (∫ y, reaction electric k x y i j*
      FiniteSphereStatic.sumSource p r P (VectorFourier.coordinateMap y) j) =
      ∑ l : ι, ∫ y, reaction electric k x y i j*
        StaticBallCentered.source (p l) (r l) (P l) (VectorFourier.coordinateMap y) j := by
  calc
    _ = ∫ y, ∑ l : ι, reaction electric k x y i j*
        StaticBallCentered.source (p l) (r l) (P l) (VectorFourier.coordinateMap y) j := by
      apply integral_congr_ae
      filter_upwards [source_sum_ae p r P j] with y hy
      rw [hy, Finset.mul_sum]
    _ = _ := integral_finset_sum _ (fun l _ => SphereReactionDipole.integrand_integrable
      electric k x i j _ (StaticBallDipole.source_integrable (p l) (r l) (P l) j))

theorem trial_moment_error (electric : Bool) (k : ℝ) (x : Space) (i j : Fin 3)
    (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) :
    ‖(∫ y, reaction electric k x y i j*
      FiniteSphereStatic.sumSource p r P (VectorFourier.coordinateMap y) j)-
      ∑ l : ι, reaction electric k x (p l) i j*((volume.real (ball (p l) (r l)) : ℂ)*P l j)‖ ≤
        SphereReactionLipschitz.bound k*
          ∑ l : ι, r l*(volume.real (ball (p l) (r l))*‖P l j‖) := by
  rw [reaction_sum, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ l : ι, SphereReactionLipschitz.bound k*r l*
        (volume.real (ball (p l) (r l))*‖P l j‖) :=
      Finset.sum_le_sum (fun l _ => SphereReactionDipole.ball_source_error electric k x
        (p l) (r l) (P l) i j)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring

theorem source_moment_error (electric : Bool) (k : ℝ) (x : Space) (i j : Fin 3)
    (p : ι → Space) (r : ι → ℝ) (P : ι → Vector)
    (f : Space → ℂ) (hf : Integrable f) :
    ‖(∫ y, reaction electric k x y i j*f y)-
      ∑ l : ι, reaction electric k x (p l) i j*((volume.real (ball (p l) (r l)) : ℂ)*P l j)‖ ≤
      entryBound k*(∫ y, ‖f y-FiniteSphereStatic.sumSource p r P (VectorFourier.coordinateMap y) j‖)+
        SphereReactionLipschitz.bound k*
          ∑ l : ι, r l*(volume.real (ball (p l) (r l))*‖P l j‖) := by
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (∫ y, reaction electric k x y i j*
      FiniteSphereStatic.sumSource p r P (VectorFourier.coordinateMap y) j) _).trans
    (add_le_add (SphereReactionDipole.integral_difference_bound electric k x i j f _ hf
      (source_integrable p r P j)) (trial_moment_error electric k x i j p r P))

end OQ14.FiniteSphereReaction

#print axioms OQ14.FiniteSphereReaction.source_sum_ae
#print axioms OQ14.FiniteSphereReaction.source_integrable
#print axioms OQ14.FiniteSphereReaction.reaction_sum
#print axioms OQ14.FiniteSphereReaction.trial_moment_error
#print axioms OQ14.FiniteSphereReaction.source_moment_error
