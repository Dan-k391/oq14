import DensityDerivatives

/-! Actual finite-component density fields and curl through genuine integrals. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.DensityCurl
open MeasureTheory Metric Set Maxwell
open WeakCurl (next previous)
open scoped Topology
abbrev Space := FourierL2.Space
abbrev Source := Fin 3 → Space → ℂ
abbrev Kernel := Space → Space → Fin 3 → Fin 3 → ℂ

def field (K : Kernel) (ρ : Source) : Field := fun x i => ∑ j : Fin 3, ∫ y, K x y i j*ρ j y

theorem differentiable (K : Kernel) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (hd : ∀ x y i j, DifferentiableAt ℝ (fun z => K z y i j) x)
    (hc : ∀ x i j, Continuous (fun y => fderiv ℝ (fun z => K z y i j) x))
    (D : ℝ) (hb : ∀ x y i j, ‖fderiv ℝ (fun z => K z y i j) x‖ ≤ D)
    (hi : ∀ x i j, Integrable (fun y => K x y i j*ρ j y)) (x : Space) (i : Fin 3) :
    DifferentiableAt ℝ (fun z => field K ρ z i) x := by
  apply DifferentiableAt.sum
  intro j _
  exact (DensityDerivatives.hasFDerivAt (fun x y => K x y i j) (ρ j) (hρ j)
    (fun x y => hd x y i j) (fun x => hc x i j) D (fun x y => hb x y i j) (fun x => hi x i j) x).differentiableAt

theorem coordinate_derivative (K : Kernel) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (hd : ∀ x y i j, DifferentiableAt ℝ (fun z => K z y i j) x)
    (hc : ∀ x i j, Continuous (fun y => fderiv ℝ (fun z => K z y i j) x))
    (D : ℝ) (hb : ∀ x y i j, ‖fderiv ℝ (fun z => K z y i j) x‖ ≤ D)
    (hi : ∀ x i j, Integrable (fun y => K x y i j*ρ j y)) (x : Space) (a i : Fin 3) :
    dcoord (fun z => field K ρ z i) x a=∑ j : Fin 3, ∫ y, ρ j y*dcoord (fun z => K z y i j) x a := by
  unfold field dcoord
  rw [fderiv_sum (fun j _ => (DensityDerivatives.hasFDerivAt (fun x y => K x y i j) (ρ j) (hρ j)
    (fun x y => hd x y i j) (fun x => hc x i j) D (fun x y => hb x y i j) (fun x => hi x i j) x).differentiableAt)]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact DensityDerivatives.coordinate_derivative (fun x y => K x y i j) (ρ j) (hρ j)
    (fun x y => hd x y i j) (fun x => hc x i j) D (fun x y => hb x y i j) (fun x => hi x i j) x a

theorem curl_integral (K L : Kernel) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (hd : ∀ x y i j, DifferentiableAt ℝ (fun z => K z y i j) x)
    (hc : ∀ x i j, Continuous (fun y => fderiv ℝ (fun z => K z y i j) x))
    (D : ℝ) (hb : ∀ x y i j, ‖fderiv ℝ (fun z => K z y i j) x‖ ≤ D)
    (hi : ∀ x i j, Integrable (fun y => K x y i j*ρ j y)) (c : ℂ)
    (hcurl : ∀ x y i j, curl (fun z a => K z y a j) x i=c*L x y i j) (x : Space) (i : Fin 3) :
    curl (field K ρ) x i=c*field L ρ x i := by
  have hcoord (F : Field) : curl F x i=dcoord (fun z => F z (previous i)) x (next i)-
      dcoord (fun z => F z (next i)) x (previous i) := by fin_cases i <;> rfl
  rw [hcoord,coordinate_derivative K ρ hρ hd hc D hb hi,coordinate_derivative K ρ hρ hd hc D hb hi,
    ← Finset.sum_sub_distrib]
  unfold field
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hp (a b : Fin 3) := DensityDerivatives.partial_integrable (fun x y => K x y b j) (ρ j) (hρ j)
    x (hc x b j) D (fun y => hb x y b j) a
  rw [← integral_sub (hp (next i) (previous i)) (hp (previous i) (next i)),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← mul_sub,← hcoord (fun z a => K z y a j)]
  rw [hcurl]
  ring

end OQ14.DensityCurl
#print axioms OQ14.DensityCurl.differentiable
#print axioms OQ14.DensityCurl.coordinate_derivative
#print axioms OQ14.DensityCurl.curl_integral
