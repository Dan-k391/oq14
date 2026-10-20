import RadialSource
import RiccatiBarrier

/-! Actual barrier source bounds for the explicit finite radial stack. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.RadialLoadBounds

open Complex Set OQ14.RadialGreen OQ14.RadialStack OQ14.RadialSource
  OQ14.HankelRealBasis OQ14.RiccatiBarrier

def load (l : ℕ) (gs : List Layer) (X : ℝ) : ℂ :=
  (traverse l gs (outgoing l X)).2/(traverse l gs (outgoing l X)).1

theorem load_coreWave (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (hX : 0 < X) :
    load l gs X = coreWaveD l gs R X hR R/coreWave l gs R X hR R := by
  rw [(coreWave_boundary l gs R X hR hX).1,(coreWave_boundary l gs R X hR hX).2]
  unfold load
  field_simp [coefficients_second_ne_zero l gs R X hR hX]

theorem coreWave_ne_zero (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (hX : 0 < X) :
    coreWave l gs R X hR R ≠ 0 := by
  rw [(coreWave_boundary l gs R X hR hX).1]
  exact div_ne_zero (outgoing_traverse_nonzero l gs X hX)
    (coefficients_second_ne_zero l gs R X hR hX)

theorem loadDenom_actual (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (hX : 0 < X) :
    loadDenom (regular l R) (regularD l R) (load l gs X) =
      1/coreWave l gs R X hR R := by
  rw [load_coreWave l gs R X hR hX]
  have hw := coreWave_wronskian l gs R X hR R hR.ne'
  unfold loadDenom
  field_simp [coreWave_ne_zero l gs R X hR hX]
  linear_combination hw

theorem gamma_loadGamma (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (hX : 0 < X) :
    gamma l gs R X hR = loadGamma (regular l R) (regularD l R)
      (irregular l R) (irregularD l R) (load l gs X) := by
  rw [loadGamma,loadDenom_actual l gs R X hR hX,load_coreWave l gs R X hR hX]
  have hw : (regular l R : ℂ)*irregularD l R-(irregular l R : ℂ)*regularD l R=1 := by
    exact_mod_cast real_wronskian l R hR.ne'
  have hc := coreWave_ne_zero l gs R X hR hX
  field_simp [hc]
  dsimp only [coreWave,coreWaveD]
  linear_combination -(gamma l gs R X hR)*hw

theorem loadDenom_norm_bounds (ψ ψD : ℝ) (h : ℂ)
    (hψ : 0 < ψ) (hψD : 0 < ψD) (hh : h.re ≤ 0) :
    ψD ≤ ‖loadDenom ψ ψD h‖ ∧ ‖h‖*ψ ≤ ‖loadDenom ψ ψD h‖ := by
  have hb := loadDenom_normSq_lower ψ ψD h hψ.le hψD.le hh
  simp only [Complex.normSq_eq_norm_sq] at hb
  constructor
  · nlinarith [sq_nonneg ‖h‖,sq_nonneg ψ,norm_nonneg (loadDenom ψ ψD h),
      mul_nonneg (sq_nonneg ‖h‖) (sq_nonneg ψ)]
  · have hp : 0 ≤ ‖h‖*ψ := mul_nonneg (norm_nonneg _) hψ.le
    nlinarith [sq_nonneg ψD,norm_nonneg (loadDenom ψ ψD h)]

theorem loadGamma_bound (ψ ψD χ χD : ℝ) (h : ℂ)
    (hψ : 0 < ψ) (hψD : 0 < ψD) (hh : h.re ≤ 0) :
    ‖loadGamma ψ ψD χ χD h‖ ≤ |χD|/ψD+|χ|/ψ := by
  obtain ⟨hd,hhb⟩ := loadDenom_norm_bounds ψ ψD h hψ hψD hh
  have hdp : 0 < ‖loadDenom ψ ψD h‖ := hψD.trans_le hd
  have hnum : ‖(χD : ℂ)-h*χ‖ ≤ |χD|+‖h‖*|χ| := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using norm_sub_le (χD : ℂ) (h*χ)
  rw [loadGamma,norm_div]
  apply (div_le_div_of_nonneg_right hnum hdp.le).trans
  rw [add_div]
  apply add_le_add
  · exact div_le_div_of_nonneg_left (abs_nonneg χD) hψD hd
  · apply (div_le_div_iff₀ hdp hψ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhb (abs_nonneg χ)]

theorem actual_gamma_barrier_bound (l : ℕ) (gs : List Layer) (R X : ℝ)
    (hR : 0 < R) (hX : 0 < X) (hcore : R^2 < ν l)
    (hstack : ∀ g ∈ gs, g.q^2*g.b^2 ≤ OQ14.HankelEnergy.angular l) :
    ‖gamma l gs R X hR‖ ≤ |irregularD l R|/regularD l R+|irregular l R|/regular l R := by
  obtain ⟨hp,hpD⟩ := barrier_positive l R hR hcore R ⟨hR,le_rfl⟩
  rw [gamma_loadGamma l gs R X hR hX]
  exact loadGamma_bound _ _ _ _ _ hp hpD (outgoing_traverse_logDerivative l gs X hX hstack)

theorem actual_core_source_bounds (l : ℕ) (gs : List Layer) (R X : ℝ)
    (hR : 0 < R) (hX : 0 < X) (hcore : R^2 < ν l)
    (hstack : ∀ g ∈ gs, g.q^2*g.b^2 ≤ OQ14.HankelEnergy.angular l) :
    ‖coreWave l gs R X hR R‖ ≤ 1/regularD l R ∧
      ‖coreWaveD l gs R X hR R‖ ≤ 1/regular l R := by
  obtain ⟨hp,hpD⟩ := barrier_positive l R hR hcore R ⟨hR,le_rfl⟩
  have hl := outgoing_traverse_logDerivative l gs X hX hstack
  have hd := loadDenom_ne_zero _ _ _ hp hpD hl
  have hw : vacuumWronskian (regular l R) (regularD l R) (irregular l R) (irregularD l R)=1 := by
    simpa [vacuumWronskian,mul_comm] using real_wronskian l R hR.ne'
  have hv := source_value_cancellation _ _ _ _ (load l gs X) hw hd
  have hD := source_derivative_cancellation _ _ _ _ (load l gs X) hw hd
  rw [←gamma_loadGamma l gs R X hR hX] at hv hD
  change coreWave l gs R X hR R = _ at hv
  change coreWaveD l gs R X hR R = _ at hD
  obtain ⟨hb,hbh⟩ := loadDenom_norm_bounds _ _ _ hp hpD hl
  have hdn : 0 < ‖loadDenom (regular l R) (regularD l R) (load l gs X)‖ := hpD.trans_le hb
  rw [hv,hD,norm_div,norm_one,norm_div]
  constructor
  · exact div_le_div_of_nonneg_left zero_le_one hpD hb
  · apply (div_le_div_iff₀ hdn hp).mpr
    simpa only [one_mul] using hbh

end OQ14.RadialLoadBounds

#print axioms OQ14.RadialLoadBounds.load_coreWave
#print axioms OQ14.RadialLoadBounds.coreWave_ne_zero
#print axioms OQ14.RadialLoadBounds.loadDenom_actual
#print axioms OQ14.RadialLoadBounds.gamma_loadGamma
#print axioms OQ14.RadialLoadBounds.loadDenom_norm_bounds
#print axioms OQ14.RadialLoadBounds.loadGamma_bound
#print axioms OQ14.RadialLoadBounds.actual_gamma_barrier_bound
#print axioms OQ14.RadialLoadBounds.actual_core_source_bounds
