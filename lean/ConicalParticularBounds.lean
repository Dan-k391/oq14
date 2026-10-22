import ConicalRadialParticular

/-! Quantitative bounded-forcing estimates for the actual cone particular solution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ConicalParticularBounds
open MeasureTheory Set OQ14.ConicalRadialParticular OQ14.ConePowerPrimitive
open scoped Topology

def constant (ν : ℝ) : ℝ := (ν+2)/(1-ν)+3

private theorem norm_power (β r : ℝ) (hr : 0 ≤ r) : ‖power β r‖=r^β := by
  simp only [power,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hr β)]

private theorem norm_div_le (z : ℂ) (D : ℝ) (hD : 1 ≤ D) : ‖z/(D : ℂ)‖ ≤ ‖z‖ := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ D)]
  exact div_le_self (norm_nonneg z) hD

theorem primitive_bounds (ν : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (A B : ℝ → ℂ)
    (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0)) (r M : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M) (hb : ∀ s ∈ Ioo (0 : ℝ) r, ‖A s‖ ≤ M ∧ ‖B s‖ ≤ M) :
    ‖leftPrimitive ν A B r‖ ≤ ((ν+2)/(1-ν))*M*r^(1-ν) ∧
      ‖rightPrimitive ν A B r‖ ≤ M*r^(ν+2) := by
  have hL : ∀ s ∈ Ioo (0 : ℝ) r, ‖minusForcing ν A B s‖ ≤ (ν+2)*M := by
    intro s hs
    calc
      _ ≤ ‖B s‖+‖((ν+1 : ℝ) : ℂ)*A s‖ := norm_sub_le _ _
      _ = ‖B s‖+(ν+1)*‖A s‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith [hν.1] : 0 < ν+1)]
      _ ≤ M+(ν+1)*M := add_le_add (hb s hs).2
        (mul_le_mul_of_nonneg_left (hb s hs).1 (by linarith [hν.1]))
      _ = (ν+2)*M := by ring
  have hR : ∀ s ∈ Ioo (0 : ℝ) r, ‖plusForcing ν A B s‖ ≤ (ν+1)*M := by
    intro s hs
    calc
      _ ≤ ‖B s‖+‖(ν : ℂ)*A s‖ := norm_add_le _ _
      _ = ‖B s‖+ν*‖A s‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hν.1]
      _ ≤ M+ν*M := add_le_add (hb s hs).2 (mul_le_mul_of_nonneg_left (hb s hs).1 hν.1.le)
      _ = (ν+1)*M := by ring
  constructor
  · have hi := primitive_norm_le (-ν) (by linarith [hν.2]) (minusForcing ν A B)
      (hB.sub (continuousOn_const.mul hA)) r ((ν+2)*M) hr.le hL
    convert hi using 1
    rw [show -ν+1=1-ν by ring]
    ring
  · have hi := primitive_norm_le (ν+1) (by linarith [hν.1]) (plusForcing ν A B)
      (hB.add (continuousOn_const.mul hA)) r ((ν+1)*M) hr.le hR
    apply hi.trans
    rw [show ν+1+1=ν+2 by ring]
    apply (div_le_iff₀ (by linarith [hν.1] : 0 < ν+2)).mpr
    nlinarith [mul_nonneg hM (Real.rpow_nonneg hr.le (ν+2))]

theorem particular_norm_le (ν : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (A B : ℝ → ℂ)
    (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0)) (r M : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M) (hb : ∀ s ∈ Ioo (0 : ℝ) r, ‖A s‖ ≤ M ∧ ‖B s‖ ≤ M) :
    ‖particular ν A B r‖ ≤ constant ν*M*r := by
  obtain ⟨hL,hR⟩ := primitive_bounds ν hν A B hA hB r M hr hM hb
  have hp1 : r^ν*r^(1-ν)=r := by rw [← Real.rpow_add hr,show ν+(1-ν)=1 by ring,Real.rpow_one]
  have hp2 : r^(-ν-1)*r^(ν+2)=r := by
    rw [← Real.rpow_add hr,show -ν-1+(ν+2)=1 by ring,Real.rpow_one]
  calc
    _ ≤ ‖power ν r*leftPrimitive ν A B r-power (-ν-1) r*rightPrimitive ν A B r‖ :=
      norm_div_le _ _ (by linarith [hν.1])
    _ ≤ ‖power ν r*leftPrimitive ν A B r‖+‖power (-ν-1) r*rightPrimitive ν A B r‖ := norm_sub_le _ _
    _ = r^ν*‖leftPrimitive ν A B r‖+r^(-ν-1)*‖rightPrimitive ν A B r‖ := by
      rw [norm_mul,norm_mul,norm_power _ _ hr.le,norm_power _ _ hr.le]
    _ ≤ r^ν*(((ν+2)/(1-ν))*M*r^(1-ν))+r^(-ν-1)*(M*r^(ν+2)) :=
      add_le_add (mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hr.le _))
        (mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hr.le _))
    _ = (((ν+2)/(1-ν))+1)*M*r := by
      linear_combination (((ν+2)/(1-ν))*M)*hp1+M*hp2
    _ ≤ constant ν*M*r := by dsimp only [constant]; nlinarith [mul_nonneg hM hr.le]

theorem flux_norm_le (ν : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (A B : ℝ → ℂ)
    (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0)) (r M : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M) (hb : ∀ s ∈ Ioo (0 : ℝ) r, ‖A s‖ ≤ M ∧ ‖B s‖ ≤ M) :
    ‖flux ν A B r‖ ≤ (constant ν-1)*M*r^2 := by
  obtain ⟨hL,hR⟩ := primitive_bounds ν hν A B hA hB r M hr hM hb
  have hK : 0 ≤ (ν+2)/(1-ν) := div_nonneg (by linarith [hν.1]) (by linarith [hν.2])
  have hp1 : r^(ν+1)*r^(1-ν)=r^2 := by
    rw [← Real.rpow_add hr,show ν+1+(1-ν)=2 by ring,Real.rpow_two]
  have hp2 : r^(-ν)*r^(ν+2)=r^2 := by
    rw [← Real.rpow_add hr,show -ν+(ν+2)=2 by ring,Real.rpow_two]
  calc
    _ ≤ ‖(ν : ℂ)*(power (ν+1) r*leftPrimitive ν A B r)+
        ((ν+1 : ℝ) : ℂ)*(power (-ν) r*rightPrimitive ν A B r)‖ := norm_div_le _ _ (by linarith [hν.1])
    _ ≤ ‖(ν : ℂ)*(power (ν+1) r*leftPrimitive ν A B r)‖+
        ‖((ν+1 : ℝ) : ℂ)*(power (-ν) r*rightPrimitive ν A B r)‖ := norm_add_le _ _
    _ = ν*(r^(ν+1)*‖leftPrimitive ν A B r‖)+(ν+1)*(r^(-ν)*‖rightPrimitive ν A B r‖) := by
      simp only [norm_mul,norm_power _ _ hr.le,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos hν.1,abs_of_pos (by linarith [hν.1] : 0 < ν+1)]
    _ ≤ ν*(r^(ν+1)*(((ν+2)/(1-ν))*M*r^(1-ν)))+(ν+1)*(r^(-ν)*(M*r^(ν+2))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hr.le _)) hν.1.le)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hr.le _)) (by linarith [hν.1]))
    _ = (ν*((ν+2)/(1-ν))+(ν+1))*M*r^2 := by
      linear_combination (ν*((ν+2)/(1-ν))*M)*hp1+((ν+1)*M)*hp2
    _ ≤ (constant ν-1)*M*r^2 := by
      dsimp only [constant]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg r)
      apply mul_le_mul_of_nonneg_right _ hM
      nlinarith [hν.2,mul_nonneg (by linarith [hν.2] : 0 ≤ 1-ν) hK]

theorem particular_deriv_norm_le (ν : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (A B : ℝ → ℂ)
    (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0)) (r M : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M) (hb : ∀ s ∈ Ioc (0 : ℝ) r, ‖A s‖ ≤ M ∧ ‖B s‖ ≤ M) :
    ‖deriv (particular ν A B) r‖ ≤ constant ν*M := by
  rw [(particular_hasDerivAt ν hν A B hA hB r hr).deriv]
  have hf := flux_norm_le ν hν A B hA hB r M hr hM (fun s hs => hb s ⟨hs.1,hs.2.le⟩)
  calc
    _ ≤ ‖flux ν A B r/(r : ℂ)^2‖+‖A r‖ := norm_sub_le _ _
    _ = ‖flux ν A B r‖/r^2+‖A r‖ := by
      rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    _ ≤ (constant ν-1)*M+M := by
      exact add_le_add ((div_le_iff₀ (sq_pos_of_pos hr)).mpr hf) (hb r ⟨hr,le_rfl⟩).1
    _ = constant ν*M := by ring

end OQ14.ConicalParticularBounds

#print axioms OQ14.ConicalParticularBounds.primitive_bounds
#print axioms OQ14.ConicalParticularBounds.particular_norm_le
#print axioms OQ14.ConicalParticularBounds.flux_norm_le
#print axioms OQ14.ConicalParticularBounds.particular_deriv_norm_le
