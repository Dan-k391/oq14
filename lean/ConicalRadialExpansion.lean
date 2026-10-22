import ConicalRadialParticular
import RadialRellich

/-! Genuine two-power classification of the forced Euler cone system. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.ConicalRadialExpansion
open Set OQ14.ConicalRadialParticular
open scoped Topology

theorem homogeneous_expansion (ν : ℝ) (hν : 0 < ν) (U F : ℝ → ℂ)
    (hU : ∀ r, 0 < r → HasDerivAt U (F r/(r : ℂ)^2) r)
    (hF : ∀ r, 0 < r → HasDerivAt F (((ν*(ν+1) : ℝ) : ℂ)*U r) r) :
    ∃ c b : ℂ, ∀ r, 0 < r → U r=c*power ν r+b*power (-ν-1) r := by
  let f : ℝ → ℂ := fun r => (r : ℂ)*U r
  let df : ℝ → ℂ := fun r => U r+F r/(r : ℂ)
  let u : ℝ → ℂ := power (ν+1)
  let du : ℝ → ℂ := fun r => ((ν+1 : ℝ) : ℂ)*power ν r
  let v : ℝ → ℂ := power (-ν)
  let dv : ℝ → ℂ := fun r => -(ν : ℂ)*power (-ν-1) r
  let q : ℝ → ℂ := fun r => ((ν*(ν+1) : ℝ) : ℂ)/(r : ℂ)^2
  have hc (r : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 r := by
    simpa using (Complex.ofRealCLM.hasFDerivAt (x := r)).hasDerivAt
  have hf (r : ℝ) (hr : 0 < r) : HasDerivAt f (df r) r := by
    convert (hc r).mul (hU r hr) using 1
    dsimp only [df]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
    ring
  have hdf (r : ℝ) (hr : 0 < r) : HasDerivAt df (q r*f r) r := by
    convert (hU r hr).add ((hF r hr).div (hc r) (Complex.ofReal_ne_zero.mpr hr.ne')) using 1
    dsimp only [q,f]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
    ring
  have hu (r : ℝ) (hr : 0 < r) : HasDerivAt u (du r) r := by
    simpa only [u,du,show ν+1-1=ν by ring] using power_hasDerivAt (ν+1) r hr
  have hdu (r : ℝ) (hr : 0 < r) : HasDerivAt du (q r*u r) r := by
    have hp : power (ν+1) r=(r : ℂ)^2*power (ν-1) r := by
      rw [show (r : ℂ)^2=power 2 r by simp [power],power_mul _ _ _ hr]
      congr 1
      ring
    convert (power_hasDerivAt ν r hr).const_mul (((ν+1 : ℝ) : ℂ)) using 1
    dsimp only [q,u]
    rw [hp]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
    ring
  have hv (r : ℝ) (hr : 0 < r) : HasDerivAt v (dv r) r := by
    simpa only [v,dv,Complex.ofReal_neg] using power_hasDerivAt (-ν) r hr
  have hdv (r : ℝ) (hr : 0 < r) : HasDerivAt dv (q r*v r) r := by
    have hp : power (-ν) r=(r : ℂ)^2*power (-ν-1-1) r := by
      rw [show (r : ℂ)^2=power 2 r by simp [power],power_mul _ _ _ hr]
      congr 1
      ring
    convert (power_hasDerivAt (-ν-1) r hr).const_mul (-(ν : ℂ)) using 1
    dsimp only [q,v]
    rw [hp]
    field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
    ring
  let W : ℂ := -((2*ν+1 : ℝ) : ℂ)
  have hW : W ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (by linarith : 2*ν+1 ≠ 0))
  have hwr (r : ℝ) (hr : 0 < r) : u r*dv r-v r*du r=W := by
    have hp1 : power (ν+1) r*power (-ν-1) r=1 := by
      rw [power_mul _ _ _ hr,show ν+1+(-ν-1)=0 by ring]; simp [power]
    have hp2 : power (-ν) r*power ν r=1 := by rw [power_mul _ _ _ hr]; simp [power]
    dsimp only [u,du,v,dv,W]
    calc
      _ = -(ν : ℂ)*(power (ν+1) r*power (-ν-1) r)-
          ((ν+1 : ℝ) : ℂ)*(power (-ν) r*power ν r) := by ring
      _ = _ := by rw [hp1,hp2]; push_cast; ring
  obtain ⟨c,b,hcb⟩ := RadialRellich.ode_two_solution_expansion 0 f df u du v dv q W hW hf hdf hu hdu hv hdv hwr
  refine ⟨c,b,fun r hr => ?_⟩
  have h := hcb r hr
  have hp1 : power (ν+1) r=(r : ℂ)*power ν r := by
    rw [show (r : ℂ)=power 1 r by simp [power],power_mul _ _ _ hr]
    congr 1
    ring
  have hp2 : power (-ν) r=(r : ℂ)*power (-ν-1) r := by
    rw [show (r : ℂ)=power 1 r by simp [power],power_mul _ _ _ hr]
    congr 1
    ring
  dsimp only [f,u,v] at h
  rw [hp1,hp2] at h
  apply (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'))
  linear_combination h

theorem forced_expansion (ν : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (A B U F : ℝ → ℂ)
    (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0))
    (hU : ∀ r, 0 < r → HasDerivAt U (F r/(r : ℂ)^2-A r) r)
    (hF : ∀ r, 0 < r → HasDerivAt F (((ν*(ν+1) : ℝ) : ℂ)*U r+(r : ℂ)*B r) r) :
    ∃ c b : ℂ, ∀ r, 0 < r → U r=c*power ν r+b*power (-ν-1) r+particular ν A B r := by
  let V : ℝ → ℂ := U-particular ν A B
  let G : ℝ → ℂ := F-flux ν A B
  have hV (r : ℝ) (hr : 0 < r) : HasDerivAt V (G r/(r : ℂ)^2) r := by
    convert (hU r hr).sub (particular_hasDerivAt ν hν A B hA hB r hr) using 1
    dsimp only [G,Pi.sub_apply]
    ring
  have hG (r : ℝ) (hr : 0 < r) : HasDerivAt G (((ν*(ν+1) : ℝ) : ℂ)*V r) r := by
    convert (hF r hr).sub (flux_hasDerivAt ν hν A B hA hB r hr) using 1
    dsimp only [V,Pi.sub_apply]
    ring
  obtain ⟨c,b,hcb⟩ := homogeneous_expansion ν hν.1 V G hV hG
  refine ⟨c,b,fun r hr => ?_⟩
  have h := hcb r hr
  dsimp only [V,Pi.sub_apply] at h
  linear_combination h

end OQ14.ConicalRadialExpansion

#print axioms OQ14.ConicalRadialExpansion.homogeneous_expansion
#print axioms OQ14.ConicalRadialExpansion.forced_expansion
