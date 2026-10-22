import SphereMagneticKernel

/-! Actual reflected electric and magnetic sphere parity, including their literal curl. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SphereMagneticParity
open MeasureTheory Metric Set SphereReactionKernel SphereWaveCalculus SphereMagneticKernel
open Maxwell (dcoord basis partial_const_mul partial_add curl pd)
open WeakCurl (next previous)
open scoped Topology

def reflection : Space →L[ℝ] Space := ContinuousLinearMap.id ℝ Space-
  (2 : ℝ) • (EuclideanSpace.proj 2).smulRight (basis 2)

theorem reflection_apply (x : Space) : reflection x = reflect x := by
  ext i
  fin_cases i <;> simp [reflection, reflect, sign, basis, smul_eq_mul, EuclideanSpace.single_apply]
  all_goals ring

theorem reflection_basis (a : Fin 3) : reflection (basis a) = sign a • basis a := by
  rw [reflection_apply]
  ext i
  fin_cases a <;> fin_cases i <;> simp [reflect, sign, basis, smul_eq_mul, EuclideanSpace.single_apply]

private theorem J_diff (k : ℝ) (x : Space) (i j : Fin 3) :
    DifferentiableAt ℝ (fun z => J k z i j) x := by
  have ha : Continuous (fun θ : Sphere => amplitude θ i j) :=
    continuous_const.sub ((coordinate_continuous i).mul (coordinate_continuous j))
  exact ((moment_hasFDerivAt _ ha 2 (fun θ => amplitude_bound θ i j) k x).const_mul _).differentiableAt

private theorem affine_partial (k : ℝ) (x y : Space) (L : Space →L[ℝ] Space)
    (a i j : Fin 3) (c : ℝ) (hc : L (basis a) = c • basis a) :
    dcoord (fun z => J k (L z-y) i j) x a =
      (c : ℂ)*dcoord (fun z => J k z i j) (L x-y) a := by
  have hd := (J_diff k (L x-y) i j).hasFDerivAt.comp x (L.hasFDerivAt.sub_const y)
  simp only [Function.comp_def] at hd
  rw [dcoord, hd.fderiv]
  simp [ContinuousLinearMap.comp_apply, hc, dcoord, smul_eq_mul]

private theorem J_affine_diff (k : ℝ) (x y : Space) (L : Space →L[ℝ] Space) (i j : Fin 3) :
    DifferentiableAt ℝ (fun z => J k (L z-y) i j) x := by
  have hd := (J_diff k (L x-y) i j).hasFDerivAt.comp x (L.hasFDerivAt.sub_const y)
  simpa only [Function.comp_def] using hd.differentiableAt

theorem reaction_partial (electric : Bool) (k : ℝ) (x y : Space) (a i j : Fin 3) :
    dcoord (fun z => reaction electric k z y i j) x a = (Complex.I/2)*
      (dcoord (fun z => J k z i j) (x-y) a+
        (if electric then -1 else 1 : ℂ)*(sign i : ℂ)*(sign a : ℂ)*
          dcoord (fun z => J k z i j) (reflect x-y) a) := by
  have hi := J_affine_diff k x y (ContinuousLinearMap.id ℝ Space) i j
  have hr := J_affine_diff k x y reflection i j
  simp only [ContinuousLinearMap.id_apply] at hi
  simp only [reflection_apply] at hr
  unfold reaction
  rw [partial_const_mul (hi.add (hr.const_mul _)), partial_add hi (hr.const_mul _),
    partial_const_mul hr]
  have hd := affine_partial k x y (ContinuousLinearMap.id ℝ Space) a i j 1 (by simp)
  simp only [ContinuousLinearMap.id_apply, Complex.ofReal_one, one_mul] at hd
  have he := affine_partial k x y reflection a i j (sign a) (reflection_basis a)
  simp only [reflection_apply] at he
  rw [hd, he]
  ring

def magneticReaction (electric : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) : ℂ :=
  (Complex.I/2)*(K k (x-y) i j-
    (if electric then -1 else 1 : ℂ)*(sign i : ℂ)*K k (reflect x-y) i j)

theorem curl_reaction (electric : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) :
    curl (fun z a => reaction electric k z y a j) x i =
      (Complex.I*(k : ℂ))*magneticReaction electric k x y i j := by
  have hcurl (z : Space) := curl_J k z i j
  have hsign : (sign (previous i) : ℂ)*(sign (next i) : ℂ) = -(sign i : ℂ) := by
    fin_cases i <;> norm_num [sign, next, previous, Fin.ext_iff]
  have he : curl (fun z a => reaction electric k z y a j) x i =
      dcoord (fun z => reaction electric k z y (previous i) j) x (next i)-
        dcoord (fun z => reaction electric k z y (next i) j) x (previous i) := by fin_cases i <;> rfl
  rw [he, reaction_partial, reaction_partial]
  have hbase (z : Space) :
      dcoord (fun t => J k t (previous i) j) z (next i)-
        dcoord (fun t => J k t (next i) j) z (previous i) = (Complex.I*(k : ℂ))*K k z i j := by
    convert hcurl z using 1
    fin_cases i <;> rfl
  unfold magneticReaction
  calc
    _ = (Complex.I/2)*
      ((dcoord (fun t => J k t (previous i) j) (x-y) (next i)-
        dcoord (fun t => J k t (next i) j) (x-y) (previous i))-
       (if electric then -1 else 1 : ℂ)*(sign i : ℂ)*
       (dcoord (fun t => J k t (previous i) j) (reflect x-y) (next i)-
        dcoord (fun t => J k t (next i) j) (reflect x-y) (previous i))) := by
      linear_combination (Complex.I/2)*(if electric then -1 else 1 : ℂ)*
        dcoord (fun t => J k t (previous i) j) (reflect x-y) (next i)*hsign -
        (Complex.I/2)*(if electric then -1 else 1 : ℂ)*
        dcoord (fun t => J k t (next i) j) (reflect x-y) (previous i)*hsign
    _ = _ := by rw [hbase, hbase]; ring

theorem reflect_plane (x : Space) (hx : x 2=0) : reflect x=x := by
  ext i
  fin_cases i <;> simp [reflect, sign, hx]

theorem reaction_on_plane (electric : Bool) (k : ℝ) (x y : Space) (hx : x 2=0) (i j : Fin 3) :
    reaction electric k x y i j = (Complex.I/2)*
      (1+(if electric then -1 else 1 : ℂ)*(sign i : ℂ))*J k (x-y) i j := by
  unfold reaction
  rw [reflect_plane x hx]
  ring

theorem magnetic_on_plane (electric : Bool) (k : ℝ) (x y : Space) (hx : x 2=0) (i j : Fin 3) :
    magneticReaction electric k x y i j = (Complex.I/2)*
      (1-(if electric then -1 else 1 : ℂ)*(sign i : ℂ))*K k (x-y) i j := by
  unfold magneticReaction
  rw [reflect_plane x hx]
  ring

theorem same_parity_normal_cross_zero (electric : Bool) (k : ℝ) (x y z : Space)
    (hx : x 2=0) (j l : Fin 3) :
    crossProduct (fun i => reaction electric k x y i j)
      (Maxwell.conjugate (fun i => magneticReaction electric k x z i l)) 2 = 0 := by
  change reaction electric k x y 0 j*star (magneticReaction electric k x z 1 l)-
    reaction electric k x y 1 j*star (magneticReaction electric k x z 0 l)=0
  rw [reaction_on_plane electric k x y hx 0 j, reaction_on_plane electric k x y hx 1 j,
    magnetic_on_plane electric k x z hx 1 l, magnetic_on_plane electric k x z hx 0 l]
  cases electric <;> norm_num [sign, Fin.ext_iff]

theorem magnetic_bound (electric : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) :
    ‖magneticReaction electric k x y i j‖ ≤ entryBound k := by
  have hs : ‖(sign i : ℂ)‖=1 := by unfold sign; split_ifs <;> norm_num
  have he : ‖(if electric then -1 else 1 : ℂ)‖=1 := by cases electric <;> norm_num
  unfold magneticReaction
  rw [norm_mul]
  have hh := norm_sub_le (K k (x-y) i j)
    ((if electric then -1 else 1 : ℂ)*(sign i : ℂ)*K k (reflect x-y) i j)
  simp only [norm_mul, hs, he, one_mul] at hh
  have hc : ‖Complex.I/2‖=1/2 := by norm_num [norm_div]
  rw [hc]
  nlinarith [K_bound k (x-y) i j, K_bound k (reflect x-y) i j]
end OQ14.SphereMagneticParity
#print axioms OQ14.SphereMagneticParity.reflection_apply
#print axioms OQ14.SphereMagneticParity.reflection_basis
#print axioms OQ14.SphereMagneticParity.reaction_partial
#print axioms OQ14.SphereMagneticParity.curl_reaction
#print axioms OQ14.SphereMagneticParity.reflect_plane
#print axioms OQ14.SphereMagneticParity.reaction_on_plane
#print axioms OQ14.SphereMagneticParity.magnetic_on_plane

#print axioms OQ14.SphereMagneticParity.same_parity_normal_cross_zero
#print axioms OQ14.SphereMagneticParity.magnetic_bound
