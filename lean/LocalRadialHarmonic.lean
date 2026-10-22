import RadialNormTest
import DebyeCalculus

/-! Actual radial harmonic calculus on punctured Euclidean space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.LocalRadialHarmonic
open Set Filter OQ14.Maxwell OQ14.GreenKernel OQ14.ExteriorClassical
  OQ14.ExteriorHelmholtz OQ14.HelmholtzTestCalculus OQ14.RadialNormTest
open scoped Topology

theorem radial_smooth (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (x : Space) (hx : x ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) (radialNorm η) x :=
  (hη.contDiffAt (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr hx))).comp x (contDiffAt_norm ℝ hx)

theorem radial_partial (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    dcoord (radialNorm η) x i = deriv η ‖x‖*unitCoordinate i x := by
  exact radial_composition_partial η _ x hx
    ((hη.contDiffAt (isOpen_Ioi.mem_nhds (norm_pos_iff.mpr hx))).differentiableAt (by simp)).hasDerivAt i

theorem radial_second_partial (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    dcoord (fun y => dcoord (radialNorm η) y i) x i =
      deriv (deriv η) ‖x‖*(x i : ℂ)^2/(‖x‖ : ℂ)^2+
        deriv η ‖x‖*(1/(‖x‖ : ℂ)-(x i : ℂ)^2/(‖x‖ : ℂ)^3) := by
  have hη' : ContDiffOn ℝ (⊤ : ℕ∞) (deriv η) (Ioi 0) :=
    hη.deriv_of_isOpen isOpen_Ioi (by simp)
  have hd := (radial_smooth (deriv η) hη' x hx).differentiableAt (by simp)
  change DifferentiableAt ℝ (fun y : Space => deriv η ‖y‖) x at hd
  have he : (fun y => dcoord (radialNorm η) y i) =ᶠ[𝓝 x]
      (fun y => deriv η ‖y‖*unitCoordinate i y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact radial_partial η hη y hy i
  rw [DebyeCalculus.partial_congr he,
    partial_mul hd (unitCoordinate_differentiableAt i x hx), unitCoordinate_partial i i x hx]
  rw [show dcoord (fun y => deriv η ‖y‖) x i = deriv (deriv η) ‖x‖*unitCoordinate i x from
    radial_partial (deriv η) hη' x hx i]
  simp only [ite_true,unitCoordinate,radialNorm]
  push_cast
  ring

theorem radial_laplacian (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (x : Space) (hx : x ≠ 0) :
    laplacian (radialNorm η) x = deriv (deriv η) ‖x‖+2/(‖x‖ : ℂ)*deriv η ‖x‖ := by
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  simp only [laplacian,radial_second_partial η hη x hx,Fin.sum_univ_three]
  calc
    _ = deriv (deriv η) ‖x‖*((x 0 : ℂ)^2+(x 1 : ℂ)^2+(x 2 : ℂ)^2)/(‖x‖ : ℂ)^2+
      deriv η ‖x‖*(3/(‖x‖ : ℂ)-((x 0 : ℂ)^2+(x 1 : ℂ)^2+(x 2 : ℂ)^2)/(‖x‖ : ℂ)^3) := by ring
    _ = _ := by rw [coordinate_squares]; field_simp [hr]; ring

theorem harmonic_laplacian (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (P : Space → ℂ) (x : Space) (hx : x ≠ 0)
    (hP : ContDiffAt ℝ (⊤ : ℕ∞) P x) (l : ℕ) (hH : laplacian P x=0)
    (hEuler : (∑ i : Fin 3, (x i : ℂ)*dcoord P x i)=(l : ℂ)*P x) :
    laplacian (fun y => radialNorm η y*P y) x =
      P x*(deriv (deriv η) ‖x‖+(2*(l : ℂ)+2)/(‖x‖ : ℂ)*deriv η ‖x‖) := by
  rw [laplacian_mul _ _ x (radial_smooth η hη x hx) hP,hH,mul_zero,zero_add,
    radial_laplacian η hη x hx]
  simp only [radial_partial η hη x hx,unitCoordinate,Fin.sum_univ_three] at hEuler ⊢
  push_cast
  linear_combination (2*deriv η ‖x‖/(‖x‖ : ℂ))*hEuler

theorem polynomial_helmholtz (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) (q : ℂ)
    (hode : ∀ r > 0, deriv (deriv η) r+(2*(l : ℂ)+2)/(r : ℂ)*deriv η r+q^2*η r=0)
    (x : Space) (hx : x ≠ 0) :
    laplacian (fun y => radialNorm η y*HarmonicPolynomial.complexEvaluate p y) x+
      q^2*(radialNorm η x*HarmonicPolynomial.complexEvaluate p x)=0 := by
  have hH : laplacian (HarmonicPolynomial.complexEvaluate p) x=0 := by
    rw [HarmonicPolynomial.complexEvaluate_laplacian,hh]
    simp [HarmonicPolynomial.evaluate]
  rw [harmonic_laplacian η hη _ x hx (HarmonicPolynomial.complexEvaluate_regular p).contDiffAt
    l hH (HarmonicPolynomial.complexEvaluate_euler p l hp x)]
  dsimp [radialNorm]
  linear_combination HarmonicPolynomial.complexEvaluate p x*hode ‖x‖ (norm_pos_iff.mpr hx)

end OQ14.LocalRadialHarmonic

#print axioms OQ14.LocalRadialHarmonic.radial_smooth
#print axioms OQ14.LocalRadialHarmonic.radial_partial
#print axioms OQ14.LocalRadialHarmonic.radial_second_partial
#print axioms OQ14.LocalRadialHarmonic.radial_laplacian
#print axioms OQ14.LocalRadialHarmonic.harmonic_laplacian
#print axioms OQ14.LocalRadialHarmonic.polynomial_helmholtz
