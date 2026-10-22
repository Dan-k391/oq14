import LocalRadialHarmonic

/-! Actual radial and tangential components of Debye fields for harmonic polynomials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.DebyeRadialTrace
open Set Filter OQ14.Maxwell OQ14.GreenKernel OQ14.ExteriorClassical
  OQ14.ExteriorHelmholtz OQ14.ModalDipole OQ14.DebyeCalculus OQ14.RadialNormTest
  OQ14.HarmonicPolynomial
open scoped Topology

def scalar (η : ℝ → ℂ) (p : Poly) (x : Space) : ℂ := η ‖x‖*complexEvaluate p x
def angularToroidal (p : Poly) (x : Space) : Vector :=
  ![dcoord (complexEvaluate p) x 1*(x 2 : ℂ)-dcoord (complexEvaluate p) x 2*(x 1 : ℂ),
    dcoord (complexEvaluate p) x 2*(x 0 : ℂ)-dcoord (complexEvaluate p) x 0*(x 2 : ℂ),
    dcoord (complexEvaluate p) x 0*(x 1 : ℂ)-dcoord (complexEvaluate p) x 1*(x 0 : ℂ)]

theorem scalar_smooth (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (p : Poly) (x : Space) (hx : x ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) (scalar η p) x :=
  (LocalRadialHarmonic.radial_smooth η hη x hx).mul (complexEvaluate_regular p).contDiffAt

theorem scalar_partial (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (p : Poly) (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    dcoord (scalar η p) x i = η ‖x‖*dcoord (complexEvaluate p) x i+
      deriv η ‖x‖*(x i : ℂ)/(‖x‖ : ℂ)*complexEvaluate p x := by
  have hd := (LocalRadialHarmonic.radial_smooth η hη x hx).differentiableAt (by simp)
  change DifferentiableAt ℝ (fun y : Space => η ‖y‖) x at hd
  unfold scalar
  rw [partial_mul hd ((complexEvaluate_regular p).contDiffAt.differentiableAt (by simp))]
  rw [show dcoord (fun y : Space => η ‖y‖) x i=deriv η ‖x‖*unitCoordinate i x from
    LocalRadialHarmonic.radial_partial η hη x hx i]
  simp only [unitCoordinate]
  push_cast
  ring

theorem toroidal_components (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (p : Poly) (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    toroidal (scalar η p) x i = η ‖x‖*angularToroidal p x i := by
  have hd := (scalar_smooth η hη p x hx).differentiableAt (by simp)
  fin_cases i <;> dsimp [toroidal,curl,pd,radialVector,angularToroidal] <;>
    simp only [partial_mul (coordinate_differentiableAt x _) hd,coordinate_partial,
      scalar_partial η hη p x hx] <;> norm_num [Fin.ext_iff] <;> ring

def eulerProfile (l : ℕ) (η : ℝ → ℂ) (r : ℝ) : ℂ :=
  (l+3 : ℂ)*η r+(r : ℂ)*deriv η r

theorem radial_divergence (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (x : Space) (hx : x ≠ 0) :
    divergence (radialVector (scalar η p)) x = scalar (eulerProfile l η) p x := by
  have hd := (scalar_smooth η hη p x hx).differentiableAt (by simp)
  have he := complexEvaluate_euler p l hp x
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  dsimp only [divergence,pd,radialVector]
  simp only [partial_mul (coordinate_differentiableAt x _) hd,coordinate_partial,ite_true,
    mul_one,scalar_partial η hη p x hx,Fin.sum_univ_three] at he ⊢
  dsimp only [scalar,eulerProfile]
  have hs := coordinate_squares x
  field_simp [hr]
  linear_combination (‖x‖ : ℂ)*η ‖x‖*he+deriv η ‖x‖*complexEvaluate p x*hs

theorem eulerProfile_smooth (l : ℕ) (η : ℝ → ℂ)
    (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (eulerProfile l η) (Ioi 0) :=
  (contDiffOn_const.mul hη).add (Complex.ofRealCLM.contDiff.contDiffOn.mul
    (hη.deriv_of_isOpen isOpen_Ioi (by simp)))

theorem eulerProfile_deriv (l : ℕ) (η : ℝ → ℂ)
    (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0)) (r : ℝ) (hr : 0 < r) :
    deriv (eulerProfile l η) r=(l+4 : ℂ)*deriv η r+(r : ℂ)*deriv (deriv η) r := by
  have hd := ((hη.contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  have hη' : ContDiffOn ℝ (⊤ : ℕ∞) (deriv η) (Ioi 0) :=
    hη.deriv_of_isOpen isOpen_Ioi (by simp)
  have hd' := ((hη'.contDiffAt
    (isOpen_Ioi.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  convert ((hd.const_mul (l+3 : ℂ)).add ((complex_radius_hasDerivAt r).mul hd')).deriv using 1
  ring

theorem toroidal_curl (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    curl (toroidal (scalar η p)) x i=
      ((‖x‖ : ℂ)*deriv η ‖x‖+(l+1 : ℂ)*η ‖x‖)*dcoord (complexEvaluate p) x i-
        (l : ℂ)*deriv η ‖x‖/(‖x‖ : ℂ)*(x i : ℂ)*complexEvaluate p x := by
  have hs := scalar_smooth η hη p x hx
  have he : divergence (radialVector (scalar η p)) =ᶠ[𝓝 x] scalar (eulerProfile l η) p := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact radial_divergence η hη p l hp y hy
  have hH : laplacian (complexEvaluate p) x=0 := by
    rw [complexEvaluate_laplacian,hh]
    simp [evaluate]
  change curl (curl (radialVector (scalar η p))) x i = _
  rw [curl_curl_laplacian _ x (radialVector_smooth _ x hs),partial_congr he,
    scalar_partial _ (eulerProfile_smooth l η hη) p x hx,
    radialVector_laplacian _ x hs]
  rw [show laplacian (scalar η p) x=complexEvaluate p x*
      (deriv (deriv η) ‖x‖+(2*(l : ℂ)+2)/(‖x‖ : ℂ)*deriv η ‖x‖) from
    LocalRadialHarmonic.harmonic_laplacian η hη _ x hx (complexEvaluate_regular p).contDiffAt
      l hH (complexEvaluate_euler p l hp x)]
  rw [scalar_partial η hη p x hx,eulerProfile_deriv l η hη ‖x‖ (norm_pos_iff.mpr hx)]
  dsimp only [eulerProfile]
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  field_simp [hr]
  ring

def position (x : Space) : Vector := fun i => (x i : ℂ)

def angularPoloidal (p : Poly) (l : ℕ) (x : Space) : Vector := fun i =>
  (‖x‖ : ℂ)^2*dcoord (complexEvaluate p) x i-(l : ℂ)*complexEvaluate p x*(x i : ℂ)

theorem toroidal_radial_zero (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (p : Poly) (x : Space) (hx : x ≠ 0) : dot (position x) (toroidal (scalar η p) x)=0 := by
  simp only [dot,toroidal_components η hη p x hx]
  dsimp [position,angularToroidal]
  ring

theorem curl_radial (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x ≠ 0) :
    dot (position x) (curl (toroidal (scalar η p)) x)=(l : ℂ)*(l+1)*η ‖x‖*complexEvaluate p x := by
  have he := complexEvaluate_euler p l hp x
  have hs := coordinate_squares x
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  simp only [dot,toroidal_curl η hη p l hp hh x hx,position,Fin.sum_univ_three] at he ⊢
  field_simp [hr]
  linear_combination (‖x‖ : ℂ)*((‖x‖ : ℂ)*deriv η ‖x‖+(l+1)*η ‖x‖)*he-
    (l : ℂ)*deriv η ‖x‖*complexEvaluate p x*hs

theorem toroidal_cross (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    crossProduct (position x) (toroidal (scalar η p) x) i=η ‖x‖*angularPoloidal p l x i := by
  have he := complexEvaluate_euler p l hp x
  have hs := coordinate_squares x
  simp only [Fin.sum_univ_three] at he
  rw [cross_apply]
  simp only [toroidal_components η hη p x hx]
  fin_cases i <;> dsimp [position,angularToroidal,angularPoloidal]
  · linear_combination η ‖x‖*dcoord (complexEvaluate p) x 0*hs-(x 0 : ℂ)*η ‖x‖*he
  · linear_combination η ‖x‖*dcoord (complexEvaluate p) x 1*hs-(x 1 : ℂ)*η ‖x‖*he
  · linear_combination η ‖x‖*dcoord (complexEvaluate p) x 2*hs-(x 2 : ℂ)*η ‖x‖*he

theorem curl_cross (η : ℝ → ℂ) (hη : ContDiffOn ℝ (⊤ : ℕ∞) η (Ioi 0))
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    crossProduct (position x) (curl (toroidal (scalar η p)) x) i=
      -((‖x‖ : ℂ)*deriv η ‖x‖+(l+1 : ℂ)*η ‖x‖)*angularToroidal p x i := by
  rw [cross_apply]
  simp only [toroidal_curl η hη p l hp hh x hx]
  fin_cases i <;> dsimp [position,angularToroidal] <;> ring

end OQ14.DebyeRadialTrace

#print axioms OQ14.DebyeRadialTrace.scalar_smooth
#print axioms OQ14.DebyeRadialTrace.scalar_partial
#print axioms OQ14.DebyeRadialTrace.toroidal_components
#print axioms OQ14.DebyeRadialTrace.radial_divergence
#print axioms OQ14.DebyeRadialTrace.eulerProfile_smooth
#print axioms OQ14.DebyeRadialTrace.eulerProfile_deriv
#print axioms OQ14.DebyeRadialTrace.toroidal_curl
#print axioms OQ14.DebyeRadialTrace.toroidal_radial_zero
#print axioms OQ14.DebyeRadialTrace.curl_radial
#print axioms OQ14.DebyeRadialTrace.toroidal_cross
#print axioms OQ14.DebyeRadialTrace.curl_cross
