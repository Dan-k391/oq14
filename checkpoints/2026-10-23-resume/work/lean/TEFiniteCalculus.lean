import ScalarFiniteCalculus

/-! Genuine finite linearity of Debye electric and magnetic fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.TEFiniteCalculus
open Maxwell ModalDipole ExteriorClassical ExteriorHelmholtz
variable {κ : Type*}

theorem curl_sum (s : Finset κ) (F : κ → Field) (A : κ → ℂ) (x : Space)
    (hF : ∀ q ∈ s, ∀ j, DifferentiableAt ℝ (fun y => F q y j) x) (i : Fin 3) :
    curl (fun y j => ∑ q ∈ s, A q*F q y j) x i=∑ q ∈ s, A q*curl (F q) x i := by
  have hp (a b : Fin 3) : dcoord (fun y => ∑ q ∈ s, A q*F q y b) x a=
      ∑ q ∈ s, A q*dcoord (fun y => F q y b) x a :=
    ScalarFiniteCalculus.partial_sum s (fun q y => F q y b) A x a (fun q hq => hF q hq b)
  have hc (G : Field) : curl G x i=dcoord (fun y => G y (WeakCurl.previous i)) x (WeakCurl.next i)-
      dcoord (fun y => G y (WeakCurl.next i)) x (WeakCurl.previous i) := by fin_cases i <;> rfl
  rw [hc,hp,hp,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [hc]
  ring

theorem electric_sum (s : Finset κ) (F : κ → Space → ℂ) (A : κ → ℂ)
    (hF : ∀ q ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F q)) (x : Space) (i : Fin 3) :
    DebyeMaxwell.teElectric (fun y => ∑ q ∈ s, A q*F q y) x i=
      ∑ q ∈ s, A q*DebyeMaxwell.teElectric (F q) x i := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ q ∈ s, A q*F q y) :=
    ContDiff.sum (fun q hq => contDiff_const.mul (hF q hq))
  rw [DebyePlanarJets.electric_components _ hs]
  rw [ScalarFiniteCalculus.partial_sum s F A x _ (fun q hq => (hF q hq).contDiffAt.differentiableAt (by simp)),
    ScalarFiniteCalculus.partial_sum s F A x _ (fun q hq => (hF q hq).contDiffAt.differentiableAt (by simp)),
    Finset.sum_mul,Finset.sum_mul,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [DebyePlanarJets.electric_components _ (hF q hq)]
  ring

theorem magnetic_sum (s : Finset κ) (F : κ → Space → ℂ) (A : κ → ℂ)
    (hF : ∀ q ∈ s, ContDiff ℝ (⊤ : ℕ∞) (F q)) (k : ℂ) (x : Space) (i : Fin 3) :
    DebyeMaxwell.teMagnetic k (fun y => ∑ q ∈ s, A q*F q y) x i=
      ∑ q ∈ s, A q*DebyeMaxwell.teMagnetic k (F q) x i := by
  have he : DebyeMaxwell.teElectric (fun y => ∑ q ∈ s, A q*F q y)=
      (fun y j => ∑ q ∈ s, A q*DebyeMaxwell.teElectric (F q) y j) :=
    funext (fun y => funext (electric_sum s F A hF y))
  change (-Complex.I/k)*curl (DebyeMaxwell.teElectric (fun y => ∑ q ∈ s, A q*F q y)) x i=_
  rw [he,curl_sum s (fun q => DebyeMaxwell.teElectric (F q)) A x (fun q hq j =>
    (DebyeCalculus.toroidal_smooth _ x (hF q hq).contDiffAt j).differentiableAt (by simp)) i,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  dsimp [DebyeMaxwell.teMagnetic,DebyeMaxwell.teElectric]
  ring

end OQ14.TEFiniteCalculus
#print axioms OQ14.TEFiniteCalculus.curl_sum
#print axioms OQ14.TEFiniteCalculus.electric_sum
#print axioms OQ14.TEFiniteCalculus.magnetic_sum
