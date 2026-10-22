import SphereMaxwell
import SphereMagneticParity

/-! Both genuine global vacuum Maxwell equations for actual reflected sphere parity fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SphereParityMaxwell
open MeasureTheory Metric Set SphereReactionKernel SphereWaveCalculus SphereMagneticKernel SphereMagneticParity
open Maxwell (dcoord basis partial_const_mul partial_sub curl MaxwellAt)
open WeakCurl (next previous)
open scoped Topology

private theorem K_diff (k : ℝ) (x : Space) (i j : Fin 3) :
    DifferentiableAt ℝ (fun z => K k z i j) x :=
  ((moment_hasFDerivAt _ (transverse_continuous i j) 2 (transverse_bound i j) k x).const_mul _).differentiableAt

private theorem affine_partial (k : ℝ) (x y : Space) (L : Space →L[ℝ] Space)
    (a i j : Fin 3) (c : ℝ) (hc : L (basis a)=c • basis a) :
    dcoord (fun z => K k (L z-y) i j) x a=(c : ℂ)*dcoord (fun z => K k z i j) (L x-y) a := by
  have hd := (K_diff k (L x-y) i j).hasFDerivAt.comp x (L.hasFDerivAt.sub_const y)
  simp only [Function.comp_def] at hd
  rw [dcoord, hd.fderiv]
  simp [ContinuousLinearMap.comp_apply, hc, dcoord, smul_eq_mul]

private theorem K_affine_diff (k : ℝ) (x y : Space) (L : Space →L[ℝ] Space) (i j : Fin 3) :
    DifferentiableAt ℝ (fun z => K k (L z-y) i j) x := by
  have hd := (K_diff k (L x-y) i j).hasFDerivAt.comp x (L.hasFDerivAt.sub_const y)
  simpa only [Function.comp_def] using hd.differentiableAt

theorem magnetic_partial (electric : Bool) (k : ℝ) (x y : Space) (a i j : Fin 3) :
    dcoord (fun z => magneticReaction electric k z y i j) x a=(Complex.I/2)*
      (dcoord (fun z => K k z i j) (x-y) a-
        (if electric then -1 else 1 : ℂ)*(sign i : ℂ)*(sign a : ℂ)*
          dcoord (fun z => K k z i j) (reflect x-y) a) := by
  have hi := K_affine_diff k x y (ContinuousLinearMap.id ℝ Space) i j
  have hr := K_affine_diff k x y reflection i j
  simp only [ContinuousLinearMap.id_apply] at hi
  simp only [reflection_apply] at hr
  unfold magneticReaction
  rw [partial_const_mul (hi.sub (hr.const_mul _)), partial_sub hi (hr.const_mul _), partial_const_mul hr]
  have hd := affine_partial k x y (ContinuousLinearMap.id ℝ Space) a i j 1 (by simp)
  simp only [ContinuousLinearMap.id_apply, Complex.ofReal_one, one_mul] at hd
  have he := affine_partial k x y reflection a i j (sign a) (reflection_basis a)
  simp only [reflection_apply] at he
  rw [hd, he]
  ring

theorem curl_magnetic (electric : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) :
    curl (fun z a => magneticReaction electric k z y a j) x i =
      -(Complex.I*(k : ℂ))*reaction electric k x y i j := by
  have hsign : (sign (previous i) : ℂ)*(sign (next i) : ℂ)=-(sign i : ℂ) := by
    fin_cases i <;> norm_num [sign, next, previous, Fin.ext_iff]
  have he : curl (fun z a => magneticReaction electric k z y a j) x i =
      dcoord (fun z => magneticReaction electric k z y (previous i) j) x (next i)-
        dcoord (fun z => magneticReaction electric k z y (next i) j) x (previous i) := by fin_cases i <;> rfl
  rw [he, magnetic_partial, magnetic_partial]
  have hbase (z : Space) :
      dcoord (fun t => K k t (previous i) j) z (next i)-
        dcoord (fun t => K k t (next i) j) z (previous i)=-(Complex.I*(k : ℂ))*J k z i j := by
    convert SphereMaxwell.curl_K k z i j using 1
    fin_cases i <;> rfl
  unfold reaction
  calc
    _ = (Complex.I/2)*
      ((dcoord (fun t => K k t (previous i) j) (x-y) (next i)-
        dcoord (fun t => K k t (next i) j) (x-y) (previous i))+
       (if electric then -1 else 1 : ℂ)*(sign i : ℂ)*
       (dcoord (fun t => K k t (previous i) j) (reflect x-y) (next i)-
        dcoord (fun t => K k t (next i) j) (reflect x-y) (previous i))) := by
      linear_combination -(Complex.I/2)*(if electric then -1 else 1 : ℂ)*
        dcoord (fun t => K k t (previous i) j) (reflect x-y) (next i)*hsign+
        (Complex.I/2)*(if electric then -1 else 1 : ℂ)*
        dcoord (fun t => K k t (next i) j) (reflect x-y) (previous i)*hsign
    _ = _ := by rw [hbase, hbase]; ring

theorem maxwell (electric : Bool) (k : ℝ) (y : Space) (j : Fin 3) (x : Space) :
    MaxwellAt k 1 1 (fun z i => reaction electric k z y i j)
      (fun z i => magneticReaction electric k z y i j) x := by
  constructor
  · funext i
    simpa only [Complex.ofReal_one, mul_one] using curl_reaction electric k x y i j
  · funext i
    simpa only [Complex.ofReal_one, mul_one, neg_mul] using curl_magnetic electric k x y i j

theorem magnetic_differentiable (electric : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) :
    DifferentiableAt ℝ (fun z => magneticReaction electric k z y i j) x := by
  have hi := K_affine_diff k x y (ContinuousLinearMap.id ℝ Space) i j
  have hr := K_affine_diff k x y reflection i j
  simp only [ContinuousLinearMap.id_apply] at hi
  simp only [reflection_apply] at hr
  exact (hi.sub (hr.const_mul _)).const_mul _

theorem electric_differentiable (electric : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) :
    DifferentiableAt ℝ (fun z => reaction electric k z y i j) x := by
  have ha : Continuous (fun θ : Sphere => amplitude θ i j) :=
    continuous_const.sub ((coordinate_continuous i).mul (coordinate_continuous j))
  have hd (z : Space) : DifferentiableAt ℝ (fun t => J k t i j) z :=
    ((moment_hasFDerivAt _ ha 2 (fun θ => amplitude_bound θ i j) k z).const_mul _).differentiableAt
  have ht (L : Space →L[ℝ] Space) : DifferentiableAt ℝ (fun z => J k (L z-y) i j) x := by
    have hh := (hd (L x-y)).hasFDerivAt.comp x (L.hasFDerivAt.sub_const y)
    simpa only [Function.comp_def] using hh.differentiableAt
  have hi := ht (ContinuousLinearMap.id ℝ Space)
  have hr := ht reflection
  simp only [ContinuousLinearMap.id_apply] at hi
  simp only [reflection_apply] at hr
  exact (hi.add (hr.const_mul _)).const_mul _
end OQ14.SphereParityMaxwell
#print axioms OQ14.SphereParityMaxwell.magnetic_partial
#print axioms OQ14.SphereParityMaxwell.curl_magnetic
#print axioms OQ14.SphereParityMaxwell.maxwell

#print axioms OQ14.SphereParityMaxwell.magnetic_differentiable
#print axioms OQ14.SphereParityMaxwell.electric_differentiable
