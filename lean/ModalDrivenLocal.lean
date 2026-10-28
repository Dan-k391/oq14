import ModalDrivenClassical
import ModalLocal
import ModalWeightedMode

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OQ14.ModalDrivenLocal
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.ModalDriven OQ14.ModalProfiles
  OQ14.ModalDrivenProfiles OQ14.ModalOrigin OQ14.ModalLocal OQ14.ModalDipole

theorem outerB'_differentiableAt (k b d z : ℂ) (hk : k ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ (outerB' k b d) z :=
  (ModalLocal.outerB_differentiableAt k b z hk hz).add ((innerB_differentiable 1 k d) z)

theorem outerA'_differentiableAt (k b d z : ℂ) (hk : k ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ (outerA' k b d) z :=
  (outerA_differentiableAt k b z hk hz).add ((innerA_differentiable 1 k d) z)

theorem electric_memLp_compact (n k : ℂ) (hk : k ≠ 0)
    (K : Set Space) (hK : IsCompact K) (p : ENNReal) (i : Fin 3) :
    MemLp (fun x => ModalDriven.electric n k x i) p (volume.restrict K) := by
  have hA := radial_memLp_compact _ _ (entire_real_profile _ (innerA_differentiable n k (numerator n k).1)).1
    (punctured_real_profile _ (fun z hz => outerA'_differentiableAt k (numerator n k).2 (determinant n k) z hk hz)).1 K hK p
  have hB (j : Fin 3) := radial_mul_memLp_compact _ _
    (entire_real_profile _ (innerB_differentiable n k (numerator n k).1)).1
    (punctured_real_profile _ (fun z hz => outerB'_differentiableAt k (numerator n k).2 (determinant n k) z hk hz)).1
    (fun x => (x 2 : ℂ) * (x j : ℂ))
    ((coordinate 2).continuous.mul (coordinate j).continuous) K hK p
  rw [funext (ModalDrivenProfiles.electric_profiles n k)]
  fin_cases i <;> dsimp
  · simpa only [mul_assoc] using hB 0
  · simpa only [mul_assoc] using hB 1
  · simpa only [mul_assoc] using hA.add (hB 2)

theorem magnetic_memLp_compact (n k : ℂ) (hk : k ≠ 0)
    (K : Set Space) (hK : IsCompact K) (p : ENNReal) (i : Fin 3) :
    MemLp (fun x => ModalDriven.magnetic n k x i) p (volume.restrict K) := by
  have hC (j : Fin 3) := radial_mul_memLp_compact _ _
    (entire_real_profile _ (innerC_differentiable n k (numerator n k).1)).1
    (punctured_real_profile _ (fun z hz => outerC'_differentiableAt k (numerator n k).2 (determinant n k) z hk hz)).1
    (fun x => (x j : ℂ)) (coordinate j).continuous K hK p
  rw [funext (ModalDrivenProfiles.magnetic_profiles n k hk)]
  fin_cases i <;> dsimp
  · exact hC 1
  · simpa only [neg_mul] using (hC 0).neg
  · exact MemLp.zero'

theorem local_L2 (n k : ℂ) (hk : k ≠ 0) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => ModalDriven.electric n k x i) 2 (volume.restrict (closedBall 0 T)) ∧
    MemLp (fun x => ModalDriven.magnetic n k x i) 2 (volume.restrict (closedBall 0 T)) :=
  ⟨electric_memLp_compact n k hk _ (isCompact_closedBall 0 T) 2 i,
   magnetic_memLp_compact n k hk _ (isCompact_closedBall 0 T) 2 i⟩

#print axioms OQ14.ModalDrivenLocal.local_L2
end OQ14.ModalDrivenLocal

