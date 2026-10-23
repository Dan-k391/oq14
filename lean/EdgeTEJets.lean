import DebyePlanarJets
import SymmetricScalarJets

/-! Exact TE electric/magnetic edge jets and their explicit scalar-jet right inverse. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.EdgeTEJets
open Maxwell ModalDipole ExteriorClassical ExteriorHelmholtz

theorem fields (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k r y : ℝ) (x : Space)
    (h0 : x 0=r) (h1 : x 1=y) (h2 : x 2=0) (hHelm : laplacian f x+(k : ℂ)^2*f x=0) :
    DebyeMaxwell.teElectric f x 2=(y : ℂ)*dcoord f x 0-(r : ℂ)*dcoord f x 1 ∧
    DebyeMaxwell.teMagnetic k f x 0=(-Complex.I/(k : ℂ))*
      (2*dcoord f x 0+(r : ℂ)*dcoord (fun z => dcoord f z 0) x 0+
        (y : ℂ)*dcoord (fun z => dcoord f z 1) x 0+(k : ℂ)^2*(r : ℂ)*f x) ∧
    DebyeMaxwell.teMagnetic k f x 1=(-Complex.I/(k : ℂ))*
      (2*dcoord f x 1+(r : ℂ)*dcoord (fun z => dcoord f z 1) x 0+
        (y : ℂ)*dcoord (fun z => dcoord f z 1) x 1+(k : ℂ)^2*(y : ℂ)*f x) := by
  have hl : laplacian f x=-(k : ℂ)^2*f x := by linear_combination hHelm
  have hc := partial_comm_at (hf.contDiffAt (x := x)) (0 : Fin 3) (1 : Fin 3)
  constructor
  · rw [DebyePlanarJets.electric_components f hf]
    change dcoord f x 0*(x 1 : ℂ)-dcoord f x 1*(x 0 : ℂ)=_
    rw [h0,h1]
    ring
  constructor
  · change (-Complex.I/(k : ℂ))*curl (DebyeMaxwell.teElectric f) x 0=_
    rw [DebyePlanarJets.curl_components f hf]
    simp only [Fin.sum_univ_three,h0,h1,h2,Complex.ofReal_zero,zero_mul,add_zero,hl,hc]
    ring
  · change (-Complex.I/(k : ℂ))*curl (DebyeMaxwell.teElectric f) x 1=_
    rw [DebyePlanarJets.curl_components f hf]
    simp only [Fin.sum_univ_three,h0,h1,h2,Complex.ofReal_zero,zero_mul,add_zero,hl]
    ring

def scalarTarget {ι : Type*} (k r : ℝ) (y : ι → ℝ) (v : (ι × Fin 3) → ℂ) :
    EdgeScalarInterpolation.Jet ι := fun q =>
  let fy := -v (q.1,0)/(r : ℂ)
  let fxy := (Complex.I*(k : ℂ)*v (q.1,2)-2*fy)/(r : ℂ)
  match q.2.val with
  | 0 => 0
  | 1 => 0
  | 2 => fy
  | 3 => (Complex.I*(k : ℂ)*v (q.1,1)-(y q.1 : ℂ)*fxy)/(r : ℂ)
  | 4 => fxy
  | _ => 0

theorem realizes {ι : Type*} (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (k r : ℝ) (hk : k≠0) (hr : r≠0) (y : ι → ℝ) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0)
    (hHelm : ∀ x, laplacian f x+(k : ℂ)^2*f x=0)
    (v : (ι × Fin 3) → ℂ) (hj : SymmetricScalarJets.jet f p=scalarTarget k r y v) :
    ∀ j, DebyeMaxwell.teElectric f (p j) 2=v (j,0) ∧
      DebyeMaxwell.teMagnetic k f (p j) 0=v (j,1) ∧ DebyeMaxwell.teMagnetic k f (p j) 1=v (j,2) := by
  intro j
  have hjet (n : Fin 6) := congrFun hj (j,n)
  have hv := hjet 0
  have hx := hjet 1
  have hy := hjet 2
  have hxx := hjet 3
  have hxy := hjet 4
  have hyy := hjet 5
  dsimp only [SymmetricScalarJets.jet,scalarTarget] at hv hx hy hxx hxy hyy
  obtain ⟨he,hm0,hm1⟩ := fields f hf k r (y j) (p j) (h0 j) (h1 j) (h2 j) (hHelm (p j))
  rw [he,hm0,hm1,hv,hx,hy,hxx,hxy,hyy]
  have hkc : (k : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hk
  have hrc : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  constructor
  · field_simp
  constructor
  all_goals field_simp
  all_goals ring_nf
  all_goals simp [Complex.I_sq]
  all_goals field_simp

end OQ14.EdgeTEJets
#print axioms OQ14.EdgeTEJets.fields
#print axioms OQ14.EdgeTEJets.realizes
