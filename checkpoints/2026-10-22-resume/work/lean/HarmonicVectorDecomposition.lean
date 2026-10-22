import PolynomialVectorCalculus

/-! Genuine homogeneous harmonic vector polynomial decomposition with all sectors explicit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.HarmonicVectorDecomposition
open MvPolynomial OQ14.HarmonicPolynomial OQ14.PolynomialVectorCalculus

def upper (n : ℕ) (Q : Vec) : Poly := C (2*(n : ℝ)+3)*radialDot Q-radiusSq*div Q
def middle (Q : Vec) : Poly := radialDot (curl Q)

theorem radialDot_homogeneous (Q : Vec) (n : ℕ) (hp : ∀ i,(Q i).IsHomogeneous n) :
    (radialDot Q).IsHomogeneous (n+1) := by
  apply IsHomogeneous.sum Finset.univ _ _
  intro i _
  simpa only [Nat.add_comm] using (isHomogeneous_X ℝ i).mul (hp i)

theorem div_homogeneous (Q : Vec) (n : ℕ) (hp : ∀ i,(Q i).IsHomogeneous (n+1)) :
    (div Q).IsHomogeneous n := by
  apply IsHomogeneous.sum Finset.univ _ _
  intro i _
  simpa only [Nat.add_sub_cancel] using (hp i).pderiv (i := i)

theorem curl_homogeneous (Q : Vec) (n : ℕ) (hp : ∀ i,(Q i).IsHomogeneous (n+1)) (i : Fin 3) :
    (curl Q i).IsHomogeneous n := by
  have hd (i j : Fin 3) : (pderiv i (Q j)).IsHomogeneous n := by
    simpa only [Nat.add_sub_cancel] using (hp j).pderiv (i := i)
  fin_cases i <;> dsimp [curl]
  · exact (homogeneousSubmodule (Fin 3) ℝ n).sub_mem (hd 1 2) (hd 2 1)
  · exact (homogeneousSubmodule (Fin 3) ℝ n).sub_mem (hd 2 0) (hd 0 2)
  · exact (homogeneousSubmodule (Fin 3) ℝ n).sub_mem (hd 0 1) (hd 1 0)

theorem upper_homogeneous (Q : Vec) (n : ℕ) (hp : ∀ i,(Q i).IsHomogeneous (n+1)) :
    (upper n Q).IsHomogeneous (n+2) := by
  have hF : (radialDot Q).IsHomogeneous (n+2) := radialDot_homogeneous Q (n+1) hp
  have hD : (radiusSq*div Q).IsHomogeneous (n+2) := by
    simpa only [Nat.add_comm] using radiusSq_homogeneous.mul (div_homogeneous Q n hp)
  exact (homogeneousSubmodule (Fin 3) ℝ (n+2)).sub_mem
    (by simpa only [smul_eq_C_mul] using (homogeneousSubmodule (Fin 3) ℝ (n+2)).smul_mem (2*(n : ℝ)+3) hF) hD

theorem middle_homogeneous (Q : Vec) (n : ℕ) (hp : ∀ i,(Q i).IsHomogeneous (n+1)) :
    (middle Q).IsHomogeneous (n+1) := radialDot_homogeneous (curl Q) n (curl_homogeneous Q n hp)

theorem div_harmonic (Q : Vec) (hh : ∀ i,formalLaplacian (Q i)=0) : formalLaplacian (div Q)=0 := by
  rw [laplacian_div]
  simp only [div,hh,map_zero,Finset.sum_const_zero]

theorem middle_harmonic (Q : Vec) (hh : ∀ i,formalLaplacian (Q i)=0) : formalLaplacian (middle Q)=0 := by
  rw [middle,laplacian_radialDot,div_curl,mul_zero,zero_add]
  have hl (i : Fin 3) : formalLaplacian (curl Q i)=0 := by
    rw [laplacian_curl]
    fin_cases i <;> simp [curl,hh]
  simp only [radialDot,hl,mul_zero,Finset.sum_const_zero]

theorem upper_harmonic (Q : Vec) (n : ℕ) (hp : ∀ i,(Q i).IsHomogeneous (n+1))
    (hh : ∀ i,formalLaplacian (Q i)=0) : formalLaplacian (upper n Q)=0 := by
  have hF : formalLaplacian (radialDot Q)=2*div Q := by
    rw [laplacian_radialDot]
    simp only [radialDot,hh,mul_zero,Finset.sum_const_zero,add_zero]
  have hD := homogeneous_radiusSq_mul (div Q) n (div_homogeneous Q n hp)
  rw [div_harmonic Q hh,mul_zero,add_zero] at hD
  unfold upper
  rw [← smul_eq_C_mul]
  rw [map_sub,map_smul,hF,hD,smul_eq_C_mul]
  simp only [map_add,map_mul,map_ofNat,map_one]
  ring

theorem decomposition_scaled (Q : Vec) (n : ℕ) (hp : ∀ i,(Q i).IsHomogeneous (n+1))
    (hh : ∀ i,formalLaplacian (Q i)=0) (i : Fin 3) :
    C (((n : ℝ)+1)*((n : ℝ)+2)*(2*(n : ℝ)+3))*Q i=
      C ((n : ℝ)+1)*grad (upper n Q) i+C (2*(n : ℝ)+3)*tor (grad (middle Q)) i+
      C ((n : ℝ)+2)*(C (2*(n : ℝ)+1)*X i*div Q-radiusSq*grad (div Q) i) := by
  have hEuler (V : Vec) (d : ℕ) (hV : ∀ j,(V j).IsHomogeneous d) (j : Fin 3) :
      (∑ k : Fin 3,X k*pderiv k (V j))=C (d : ℝ)*V j := by
    simpa only [smul_eq_C_mul] using AngularHarmonicEnergy.euler (V j) d (hV j)
  have hg := grad_radialDot Q ((n : ℝ)+1) (by simpa only [Nat.cast_add,Nat.cast_one] using hEuler Q (n+1) hp) i
  have hcc : curl (curl Q)=grad (div Q) := by
    funext j
    rw [curl_curl,hh,sub_zero]
  have hgc : grad (middle Q)=(fun j => C ((n : ℝ)+1)*curl Q j-tor (grad (div Q)) j) := by
    funext j
    simpa only [middle,hcc] using grad_radialDot (curl Q) (n : ℝ) (hEuler (curl Q) n (curl_homogeneous Q n hp)) j
  have hD : radialDot (grad (div Q))=C (n : ℝ)*div Q := by
    simpa only [radialDot,grad,smul_eq_C_mul] using AngularHarmonicEnergy.euler (div Q) n (div_homogeneous Q n hp)
  have ht := congrArg (fun V : Vec => tor V i) hgc
  dsimp only at ht
  rw [tor_sub,tor_Cmul,tor_tor,hD] at ht
  have hu : grad (upper n Q) i=C (2*(n : ℝ)+3)*grad (radialDot Q) i-
      (2*X i*div Q+radiusSq*grad (div Q) i) := by
    simp only [upper,grad,map_sub,pderiv_C_mul,pderiv_mul,pderiv_radiusSq,pderiv_C,zero_mul,zero_add]
  simp only [map_add,map_mul,map_ofNat,map_one] at hg ht hu ⊢
  linear_combination -(C (n : ℝ)+1)*hu-(2*C (n : ℝ)+3)*ht-
    (C (n : ℝ)+1)*(2*C (n : ℝ)+3)*hg

end OQ14.HarmonicVectorDecomposition

#print axioms OQ14.HarmonicVectorDecomposition.radialDot_homogeneous
#print axioms OQ14.HarmonicVectorDecomposition.div_homogeneous
#print axioms OQ14.HarmonicVectorDecomposition.curl_homogeneous
#print axioms OQ14.HarmonicVectorDecomposition.upper_homogeneous
#print axioms OQ14.HarmonicVectorDecomposition.middle_homogeneous
#print axioms OQ14.HarmonicVectorDecomposition.div_harmonic
#print axioms OQ14.HarmonicVectorDecomposition.middle_harmonic
#print axioms OQ14.HarmonicVectorDecomposition.upper_harmonic
#print axioms OQ14.HarmonicVectorDecomposition.decomposition_scaled
