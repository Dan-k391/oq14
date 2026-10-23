import SymmetricScalarWaves
import EdgeScalarInterpolation

/-! The actual Frechet two-jets of literal symmetric scalar waves equal their interpolation vectors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SymmetricScalarJets
open Maxwell ModalDipole SymmetricScalarWaves

theorem product_partial (v w : Fin 3 → ℝ) (x : Space) (i : Fin 3) :
    dcoord (fun y => cosine v y*cosine w y) x i=
      -(v i : ℂ)*sine v x*cosine w x-(w i : ℂ)*cosine v x*sine w x := by
  rw [partial_mul ((cosine_smooth v).contDiffAt.differentiableAt (by simp))
    ((cosine_smooth w).contDiffAt.differentiableAt (by simp)),cosine_partial,cosine_partial]
  ring

theorem product_second (v w : Fin 3 → ℝ) (x : Space) (i j : Fin 3) :
    dcoord (fun y => dcoord (fun z => cosine v z*cosine w z) y i) x j=
      -((v i : ℂ)*(v j : ℂ)+(w i : ℂ)*(w j : ℂ))*(cosine v x*cosine w x)+
        ((v i : ℂ)*(w j : ℂ)+(w i : ℂ)*(v j : ℂ))*(sine v x*sine w x) := by
  have hvs : ContDiff ℝ (⊤ : ℕ∞) (sine v) := Complex.ofRealCLM.contDiff.comp (linear v).contDiff.sin
  have hws : ContDiff ℝ (⊤ : ℕ∞) (sine w) := Complex.ofRealCLM.contDiff.comp (linear w).contDiff.sin
  have hvc := (cosine_smooth v).differentiable (by simp) x
  have hwc := (cosine_smooth w).differentiable (by simp) x
  have hvs := hvs.differentiable (by simp) x
  have hws := hws.differentiable (by simp) x
  rw [show (fun y => dcoord (fun z => cosine v z*cosine w z) y i)=
    (fun y => -(v i : ℂ)*(sine v y*cosine w y)-(w i : ℂ)*(cosine v y*sine w y)) from
    funext (fun y => (product_partial v w y i).trans (by ring))]
  rw [partial_sub ((hvs.mul hwc).const_mul _) ((hvc.mul hws).const_mul _),
    partial_const_mul (hvs.mul hwc),partial_const_mul (hvc.mul hws),
    partial_mul hvs hwc,partial_mul hvc hws,sine_partial,cosine_partial,cosine_partial,sine_partial]
  ring

variable {ι : Type*}
def jet (f : Space → ℂ) (p : ι → Space) : EdgeScalarInterpolation.Jet ι := fun q =>
  match q.2.val with
  | 0 => f (p q.1)
  | 1 => dcoord f (p q.1) 0
  | 2 => dcoord f (p q.1) 1
  | 3 => dcoord (fun x => dcoord f x 0) (p q.1) 0
  | 4 => dcoord (fun x => dcoord f x 1) (p q.1) 0
  | _ => dcoord (fun x => dcoord f x 1) (p q.1) 1

theorem scalar_jet (a b c r : ℝ) (y : ι → ℝ) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0) :
    jet (scalar a b c) p=EdgeScalarInterpolation.scalarJet r y a b := by
  have hcos (j : ι) : cosine ![a,b,0] (p j)=Complex.cos ((r : ℂ)*(a : ℂ)+(y j : ℂ)*(b : ℂ)) := by
    simp [cosine,linear,Fin.sum_univ_three,smul_eq_mul,h0,h1,h2,Complex.ofReal_cos]
    congr 1
    ring
  have hsin (j : ι) : sine ![a,b,0] (p j)=Complex.sin ((r : ℂ)*(a : ℂ)+(y j : ℂ)*(b : ℂ)) := by
    simp [sine,linear,Fin.sum_univ_three,smul_eq_mul,h0,h1,h2,Complex.ofReal_sin]
    congr 1
    ring
  have hc (j : ι) : cosine ![0,0,c] (p j)=1 := by
    simp [cosine,linear,Fin.sum_univ_three,smul_eq_mul,h2]
  have hs (j : ι) : sine ![0,0,c] (p j)=0 := by
    simp [sine,linear,Fin.sum_univ_three,smul_eq_mul,h2]
  funext q
  rcases q with ⟨j,n⟩
  fin_cases n <;> dsimp [jet,EdgeScalarInterpolation.scalarJet]
  all_goals rw [show scalar a b c=(fun x => cosine ![a,b,0] x*cosine ![0,0,c] x) from rfl]
  all_goals try rw [product_second]
  all_goals try rw [product_partial]
  all_goals try simp only [hcos,hsin,hc,hs]
  all_goals try simp only [Complex.ofReal_zero,zero_mul,mul_zero,one_mul,mul_one,add_zero,zero_add,sub_zero,neg_zero]
  all_goals simp only [show (![a,b,0] : Fin 3 → ℝ) 0=a from rfl,
    show (![a,b,0] : Fin 3 → ℝ) 1=b from rfl,show (![0,0,c] : Fin 3 → ℝ) 0=0 from rfl,
    show (![0,0,c] : Fin 3 → ℝ) 1=0 from rfl,Complex.ofReal_zero,zero_mul,mul_zero,zero_pow,sub_zero]
  all_goals ring

end OQ14.SymmetricScalarJets
#print axioms OQ14.SymmetricScalarJets.product_partial
#print axioms OQ14.SymmetricScalarJets.product_second
#print axioms OQ14.SymmetricScalarJets.scalar_jet
