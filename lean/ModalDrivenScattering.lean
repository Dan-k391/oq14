import ModalDrivenLocal
import ForcedMaxwellResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OQ14.ModalDrivenScattering
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.ModalOrigin OQ14.ModalLocal
  OQ14.ModalDriven OQ14.ModalDrivenLocal

def scatteredE (n k : ℂ) : Field :=
  fun x => ModalDriven.electric n k x - determinant n k • centerE k x

def scatteredH (n k : ℂ) : Field :=
  fun x => ModalDriven.magnetic n k x - determinant n k • centerH k k x

theorem scattered_exterior (n k : ℂ) (x : Space) (hx : 1 < ‖x‖) :
    scatteredE n k x = (numerator n k).2 • ModalDipole.outgoingE k x ∧
    scatteredH n k x = (numerator n k).2 • ModalDipole.outgoingH k k x :=
  ModalDriven.scattered_exterior n k x hx

theorem scattered_local_L2 (n k : ℂ) (hk : k ≠ 0) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => scatteredE n k x i) 2 (volume.restrict (closedBall 0 T)) ∧
    MemLp (fun x => scatteredH n k x i) 2 (volume.restrict (closedBall 0 T)) := by
  have he := (continuous_memLp_compact _ (centerE_continuous k i) _ (isCompact_closedBall 0 T) 2).const_mul (determinant n k)
  have hh := (continuous_memLp_compact _ (centerH_continuous k k i) _ (isCompact_closedBall 0 T) 2).const_mul (determinant n k)
  exact ⟨(local_L2 n k hk T i).1.sub he, (local_L2 n k hk T i).2.sub hh⟩

theorem outerE_smooth (k b : ℂ) (hk : k ≠ 0) (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ModalInterface.outerE k b y i) x := by
  have hr : (‖x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hn : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => (‖y‖ : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_norm ℝ hx)
  have hA : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => ModalProfiles.outerA k b (‖y‖ : ℂ)) x := by
    have hhol : DifferentiableOn ℂ (ModalProfiles.outerA k b) {z | z ≠ 0} :=
      fun z hz => (ModalProfiles.outerA_differentiableAt k b z hk hz).differentiableWithinAt
    exact ContDiffAt.comp (g := ModalProfiles.outerA k b) (f := fun y : Space => (‖y‖ : ℂ)) x ((hhol.analyticOnNhd isOpen_ne _ hr).contDiffAt.restrict_scalars ℝ) hn
  have hB : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => ModalProfiles.outerB k b (‖y‖ : ℂ)) x := by
    have hhol : DifferentiableOn ℂ (ModalProfiles.outerB k b) {z | z ≠ 0} :=
      fun z hz => (ModalLocal.outerB_differentiableAt k b z hk hz).differentiableWithinAt
    exact ContDiffAt.comp (g := ModalProfiles.outerB k b) (f := fun y : Space => (‖y‖ : ℂ)) x ((hhol.analyticOnNhd isOpen_ne _ hr).contDiffAt.restrict_scalars ℝ) hn
  have hc (j : Fin 3) : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => (y j : ℂ)) x :=
    (coordinate j).contDiff.contDiffAt
  have he (y : Space) : ModalInterface.outerE k b y =
      ![ModalProfiles.outerB k b (‖y‖ : ℂ) * (y 2 : ℂ) * (y 0 : ℂ),
        ModalProfiles.outerB k b (‖y‖ : ℂ) * (y 2 : ℂ) * (y 1 : ℂ),
        ModalProfiles.outerA k b (‖y‖ : ℂ) + ModalProfiles.outerB k b (‖y‖ : ℂ) * (y 2 : ℂ) * (y 2 : ℂ)] := by
    ext j; fin_cases j <;> simp [ModalInterface.outerE, ModalDipole.outgoingE, ModalDipole.dipoleE,
      ModalDipole.axisField, ModalProfiles.outerA, ModalProfiles.outerB, ModalDipole.electricA,
      ModalDipole.electricB, ModalDipole.scaledRadial, ModalDipole.scaledRadialD, div_eq_mul_inv] <;> ring
  have hf : (fun y => ModalInterface.outerE k b y i) = fun y =>
      (![ModalProfiles.outerB k b (‖y‖ : ℂ) * (y 2 : ℂ) * (y 0 : ℂ),
        ModalProfiles.outerB k b (‖y‖ : ℂ) * (y 2 : ℂ) * (y 1 : ℂ),
        ModalProfiles.outerA k b (‖y‖ : ℂ) + ModalProfiles.outerB k b (‖y‖ : ℂ) * (y 2 : ℂ) * (y 2 : ℂ)] : Fin 3 → ℂ) i := by
    funext y; exact congrFun (he y) i
  rw [hf]
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]
  · exact (hB.mul (hc 2)).mul (hc 0)
  · exact (hB.mul (hc 2)).mul (hc 1)
  · exact hA.add ((hB.mul (hc 2)).mul (hc 2))

theorem scattered_smooth_exterior (n k : ℂ) (hk : k ≠ 0) (i : Fin 3) (x : Space) (hx : 1 < ‖x‖) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => scatteredE n k y i) x := by
  have hx0 : x ≠ 0 := by intro h; norm_num [h] at hx
  apply (outerE_smooth k (numerator n k).2 hk x hx0 i).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  exact congrFun (scattered_exterior n k y hy).1 i

#print axioms OQ14.ModalDrivenScattering.scattered_smooth_exterior
#print axioms OQ14.ModalDrivenScattering.scattered_local_L2
#print axioms OQ14.ModalDrivenScattering.scattered_exterior
end OQ14.ModalDrivenScattering



