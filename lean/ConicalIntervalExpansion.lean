import ConicalRadialExpansion

/-! Genuine forced conical radial classification on a finite open radial interval. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalIntervalExpansion
open Set OQ14.ConicalRadialParticular
open scoped Topology

theorem two_solution_expansion_on (Ω : Set ℝ) (hΩ : IsOpen Ω) (hcΩ : IsPreconnected Ω) (f df u du v dv q : ℝ → ℂ) (W : ℂ)
    (hW : W ≠ 0)
    (hf : ∀ r, r ∈ Ω → HasDerivAt f (df r) r)
    (hdf : ∀ r, r ∈ Ω → HasDerivAt df (q r*f r) r)
    (hu : ∀ r, r ∈ Ω → HasDerivAt u (du r) r)
    (hdu : ∀ r, r ∈ Ω → HasDerivAt du (q r*u r) r)
    (hv : ∀ r, r ∈ Ω → HasDerivAt v (dv r) r)
    (hdv : ∀ r, r ∈ Ω → HasDerivAt dv (q r*v r) r)
    (hwr : ∀ r, r ∈ Ω → u r*dv r-v r*du r = W) :
    ∃ a b : ℂ, ∀ r, r ∈ Ω → f r = a*u r+b*v r := by
  let ac : ℝ → ℂ := fun r => (f r*dv r-v r*df r)/W
  let bc : ℝ → ℂ := fun r => (u r*df r-f r*du r)/W
  have ha (r : ℝ) (hr : r ∈ Ω) : HasDerivAt ac 0 r := by
    simpa only [zero_div] using
      (RadialRellich.ode_wronskian_hasDerivAt f df v dv q r (hf r hr) (hdf r hr) (hv r hr) (hdv r hr)).div_const W
  have hb (r : ℝ) (hr : r ∈ Ω) : HasDerivAt bc 0 r := by
    simpa only [zero_div] using
      (RadialRellich.ode_wronskian_hasDerivAt u du f df q r (hu r hr) (hdu r hr) (hf r hr) (hdf r hr)).div_const W
  obtain ⟨a,hae⟩ := hΩ.exists_is_const_of_deriv_eq_zero hcΩ
    (fun r hr => (ha r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (ha r hr).deriv)
  obtain ⟨b,hbe⟩ := hΩ.exists_is_const_of_deriv_eq_zero hcΩ
    (fun r hr => (hb r hr).differentiableAt.differentiableWithinAt)
    (fun r hr => (hb r hr).deriv)
  refine ⟨a,b,?_⟩
  intro r hr
  rw [← hae r hr, ← hbe r hr]
  dsimp only [ac,bc]
  field_simp [hW]
  linear_combination -f r*(hwr r hr)

theorem homogeneous_expansion_on (ν L : ℝ) (hν : 0 < ν) (U F : ℝ → ℂ)
    (hU : ∀ r ∈ Ioo (0 : ℝ) L, HasDerivAt U (F r/(r : ℂ)^2) r)
    (hF : ∀ r ∈ Ioo (0 : ℝ) L, HasDerivAt F (((ν*(ν+1) : ℝ) : ℂ)*U r) r) :
    ∃ c b : ℂ, ∀ r ∈ Ioo (0 : ℝ) L, U r=c*power ν r+b*power (-ν-1) r := by
  let f : ℝ → ℂ := fun r => (r : ℂ)*U r
  let df : ℝ → ℂ := fun r => U r+F r/(r : ℂ)
  let u : ℝ → ℂ := power (ν+1)
  let du : ℝ → ℂ := fun r => ((ν+1 : ℝ) : ℂ)*power ν r
  let v : ℝ → ℂ := power (-ν)
  let dv : ℝ → ℂ := fun r => -(ν : ℂ)*power (-ν-1) r
  let q : ℝ → ℂ := fun r => ((ν*(ν+1) : ℝ) : ℂ)/(r : ℂ)^2
  have hc (r : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 r := by
    simpa using (Complex.ofRealCLM.hasFDerivAt (x := r)).hasDerivAt
  have hf (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) L) : HasDerivAt f (df r) r := by
    convert (hc r).mul (hU r hr) using 1
    dsimp only [df]
    field_simp [Complex.ofReal_ne_zero.mpr hr.1.ne']
    ring
  have hdf (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) L) : HasDerivAt df (q r*f r) r := by
    convert (hU r hr).add ((hF r hr).div (hc r) (Complex.ofReal_ne_zero.mpr hr.1.ne')) using 1
    dsimp only [q,f]
    field_simp [Complex.ofReal_ne_zero.mpr hr.1.ne']
    ring
  have hu (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) L) : HasDerivAt u (du r) r := by
    simpa only [u,du,show ν+1-1=ν by ring] using power_hasDerivAt (ν+1) r hr.1
  have hdu (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) L) : HasDerivAt du (q r*u r) r := by
    have hp : power (ν+1) r=(r : ℂ)^2*power (ν-1) r := by
      rw [show (r : ℂ)^2=power 2 r by simp [power],power_mul _ _ _ hr.1]
      congr 1
      ring
    convert (power_hasDerivAt ν r hr.1).const_mul (((ν+1 : ℝ) : ℂ)) using 1
    dsimp only [q,u]
    rw [hp]
    field_simp [Complex.ofReal_ne_zero.mpr hr.1.ne']
    ring
  have hv (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) L) : HasDerivAt v (dv r) r := by
    simpa only [v,dv,Complex.ofReal_neg] using power_hasDerivAt (-ν) r hr.1
  have hdv (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) L) : HasDerivAt dv (q r*v r) r := by
    have hp : power (-ν) r=(r : ℂ)^2*power (-ν-1-1) r := by
      rw [show (r : ℂ)^2=power 2 r by simp [power],power_mul _ _ _ hr.1]
      congr 1
      ring
    convert (power_hasDerivAt (-ν-1) r hr.1).const_mul (-(ν : ℂ)) using 1
    dsimp only [q,v]
    rw [hp]
    field_simp [Complex.ofReal_ne_zero.mpr hr.1.ne']
    ring
  let W : ℂ := -((2*ν+1 : ℝ) : ℂ)
  have hW : W ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (by linarith : 2*ν+1 ≠ 0))
  have hwr (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) L) : u r*dv r-v r*du r=W := by
    have hp1 : power (ν+1) r*power (-ν-1) r=1 := by
      rw [power_mul _ _ _ hr.1,show ν+1+(-ν-1)=0 by ring]; simp [power]
    have hp2 : power (-ν) r*power ν r=1 := by rw [power_mul _ _ _ hr.1]; simp [power]
    dsimp only [u,du,v,dv,W]
    calc
      _ = -(ν : ℂ)*(power (ν+1) r*power (-ν-1) r)-
          ((ν+1 : ℝ) : ℂ)*(power (-ν) r*power ν r) := by ring
      _ = _ := by rw [hp1,hp2]; push_cast; ring
  obtain ⟨c,b,hcb⟩ := two_solution_expansion_on (Ioo (0 : ℝ) L) isOpen_Ioo (convex_Ioo (0 : ℝ) L).isPreconnected f df u du v dv q W hW hf hdf hu hdu hv hdv hwr
  refine ⟨c,b,fun r hr => ?_⟩
  have h := hcb r hr
  have hp1 : power (ν+1) r=(r : ℂ)*power ν r := by
    rw [show (r : ℂ)=power 1 r by simp [power],power_mul _ _ _ hr.1]
    congr 1
    ring
  have hp2 : power (-ν) r=(r : ℂ)*power (-ν-1) r := by
    rw [show (r : ℂ)=power 1 r by simp [power],power_mul _ _ _ hr.1]
    congr 1
    ring
  dsimp only [f,u,v] at h
  rw [hp1,hp2] at h
  apply (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.1.ne'))
  linear_combination h

theorem forced_expansion_on (ν L : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (A B U F : ℝ → ℂ)
    (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0))
    (hU : ∀ r ∈ Ioo (0 : ℝ) L, HasDerivAt U (F r/(r : ℂ)^2-A r) r)
    (hF : ∀ r ∈ Ioo (0 : ℝ) L, HasDerivAt F (((ν*(ν+1) : ℝ) : ℂ)*U r+(r : ℂ)*B r) r) :
    ∃ c b : ℂ, ∀ r ∈ Ioo (0 : ℝ) L, U r=c*power ν r+b*power (-ν-1) r+particular ν A B r := by
  let V : ℝ → ℂ := U-particular ν A B
  let G : ℝ → ℂ := F-flux ν A B
  have hV (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) L) : HasDerivAt V (G r/(r : ℂ)^2) r := by
    convert (hU r hr).sub (particular_hasDerivAt ν hν A B hA hB r hr.1) using 1
    dsimp only [G,Pi.sub_apply]
    ring
  have hG (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) L) : HasDerivAt G (((ν*(ν+1) : ℝ) : ℂ)*V r) r := by
    convert (hF r hr).sub (flux_hasDerivAt ν hν A B hA hB r hr.1) using 1
    dsimp only [V,Pi.sub_apply]
    ring
  obtain ⟨c,b,hcb⟩ := homogeneous_expansion_on ν L hν.1 V G hV hG
  refine ⟨c,b,fun r hr => ?_⟩
  have h := hcb r hr
  dsimp only [V,Pi.sub_apply] at h
  linear_combination h

end OQ14.ConicalIntervalExpansion

#print axioms OQ14.ConicalIntervalExpansion.two_solution_expansion_on
#print axioms OQ14.ConicalIntervalExpansion.homogeneous_expansion_on
#print axioms OQ14.ConicalIntervalExpansion.forced_expansion_on
