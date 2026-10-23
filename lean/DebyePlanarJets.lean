import DebyeMaxwell

/-! Literal scalar-to-TE field jets on the measurement plane. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.DebyePlanarJets
open Maxwell ModalDipole ExteriorClassical ExteriorHelmholtz DebyeCalculus
open WeakCurl (next previous)

theorem electric_components (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space) (i : Fin 3) :
    DebyeMaxwell.teElectric f x i=
      dcoord f x (next i)*(x (previous i) : ℂ)-dcoord f x (previous i)*(x (next i) : ℂ) := by
  fin_cases i <;> dsimp [DebyeMaxwell.teElectric,toroidal,curl,pd,radialVector,next,previous] <;>
    simp only [partial_mul (coordinate_differentiableAt x _) (hf.contDiffAt.differentiableAt (by simp)),coordinate_partial] <;>
    norm_num [next,previous,Fin.ext_iff] <;> ring

theorem curl_components (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space) (i : Fin 3) :
    curl (DebyeMaxwell.teElectric f) x i=
      2*dcoord f x i+(∑ j : Fin 3, (x j : ℂ)*dcoord (fun y => dcoord f y i) x j)-
        (x i : ℂ)*laplacian f x := by
  have he : DebyeMaxwell.teElectric f=fun y n =>
      dcoord f y (next n)*(y (previous n) : ℂ)-dcoord f y (previous n)*(y (next n) : ℂ) :=
    funext (fun y => funext (fun n => electric_components f hf y n))
  have hd (j : Fin 3) : DifferentiableAt ℝ (fun y => dcoord f y j) x :=
    (partial_smooth hf.contDiffAt j).differentiableAt (by simp)
  have h01 := partial_comm_at (hf.contDiffAt (x := x)) (0 : Fin 3) (1 : Fin 3)
  have h02 := partial_comm_at (hf.contDiffAt (x := x)) (0 : Fin 3) (2 : Fin 3)
  have h12 := partial_comm_at (hf.contDiffAt (x := x)) (1 : Fin 3) (2 : Fin 3)
  rw [he]
  fin_cases i <;> dsimp [curl,pd,next,previous]
  all_goals rw [partial_sub ((hd _).mul (coordinate_differentiableAt x _)) ((hd _).mul (coordinate_differentiableAt x _)),
    partial_sub ((hd _).mul (coordinate_differentiableAt x _)) ((hd _).mul (coordinate_differentiableAt x _))]
  all_goals simp only [partial_mul (hd _) (coordinate_differentiableAt x _),coordinate_partial,laplacian,Fin.sum_univ_three]
  all_goals norm_num [Fin.ext_iff]
  all_goals try simp only [h01,h02,h12]
  all_goals ring

theorem edge_jet (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k r : ℝ) (x : Space)
    (h0 : x 0=r) (h1 : x 1=0) (h2 : x 2=0) (hHelm : laplacian f x+(k : ℂ)^2*f x=0) :
    DebyeMaxwell.teElectric f x 2=-(r : ℂ)*dcoord f x 1 ∧
    DebyeMaxwell.teMagnetic k f x 0=(-Complex.I/(k : ℂ))*
      (2*dcoord f x 0+(r : ℂ)*dcoord (fun y => dcoord f y 0) x 0+(k : ℂ)^2*(r : ℂ)*f x) ∧
    DebyeMaxwell.teMagnetic k f x 1=(-Complex.I/(k : ℂ))*
      (2*dcoord f x 1+(r : ℂ)*dcoord (fun y => dcoord f y 1) x 0) := by
  have hl : laplacian f x=-(k : ℂ)^2*f x := by linear_combination hHelm
  constructor
  · rw [electric_components f hf]
    change dcoord f x 0*(x 1 : ℂ)-dcoord f x 1*(x 0 : ℂ)=_
    simp only [h0,h1,Complex.ofReal_zero,mul_zero,zero_sub]
    ring
  constructor
  · change (-Complex.I/(k : ℂ))*curl (DebyeMaxwell.teElectric f) x 0=_
    rw [curl_components f hf]
    simp only [Fin.sum_univ_three,h0,h1,h2,Complex.ofReal_zero,zero_mul,add_zero,hl]
    ring
  · change (-Complex.I/(k : ℂ))*curl (DebyeMaxwell.teElectric f) x 1=_
    rw [curl_components f hf]
    simp only [Fin.sum_univ_three,h0,h1,h2,Complex.ofReal_zero,zero_mul,add_zero,sub_zero]
end OQ14.DebyePlanarJets
#print axioms OQ14.DebyePlanarJets.electric_components
#print axioms OQ14.DebyePlanarJets.curl_components
#print axioms OQ14.DebyePlanarJets.edge_jet
