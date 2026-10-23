import DebyeReactionExpansion

/-! Actual regular solid waves and their spatial Debye fields are real at real frequency. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SolidWaveReality
open OQ14.Maxwell OQ14.HarmonicPolynomial

theorem F_conj (l : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (SolidRadialSeries.F l (t : ℂ))=SolidRadialSeries.F l (t : ℂ) := by
  unfold SolidRadialSeries.F EntireFactorialSeries.sum
  change Complex.conjCLE (∑' m,EntireFactorialSeries.term (SolidRadialSeries.coefficient l) m (t : ℂ))=_
  rw [Complex.conjCLE.map_tsum]
  congr 1
  funext m
  simp [EntireFactorialSeries.term,SolidRadialSeries.coefficient,Complex.conjCLE_apply]

theorem wave_conj (l : ℕ) (k : ℝ) (p : Poly) (x : Space) :
    (starRingEnd ℂ) (SolidScalarHelmholtz.wave l k p x)=SolidScalarHelmholtz.wave l k p x := by
  unfold SolidScalarHelmholtz.wave SolidScalarHelmholtz.radial
  rw [map_mul]
  have he : (k : ℂ)^2*((‖x‖^2 : ℝ) : ℂ)=((k^2*‖x‖^2 : ℝ) : ℂ) := by push_cast;ring
  rw [he,F_conj]
  simp only [complexEvaluate,Complex.conj_ofReal]

theorem wave_neg (l : ℕ) (k : ℝ) (p : Poly) :
    SolidScalarHelmholtz.wave l (-k) p=SolidScalarHelmholtz.wave l k p := by
  funext x
  simp only [SolidScalarHelmholtz.wave,SolidScalarHelmholtz.radial,Complex.ofReal_neg,neg_sq]

theorem partial_conj (f : Space → ℂ) (hf : Differentiable ℝ f)
    (hr : ∀ x,(starRingEnd ℂ) (f x)=f x) (x : Space) (i : Fin 3) :
    (starRingEnd ℂ) (dcoord f x i)=dcoord f x i := by
  have he : (fun y => Complex.conjCLE (f y))=f := funext hr
  have hd := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => Complex.conjCLE (f y)) x=_ at hd
  rw [he] at hd
  exact (congrArg (fun L : Space →L[ℝ] ℂ => L (Maxwell.basis i)) hd).symm

theorem curl_conj (F : Field) (hf : ∀ j,Differentiable ℝ (fun x => F x j))
    (hr : ∀ x j,(starRingEnd ℂ) (F x j)=F x j) (x : Space) (i : Fin 3) :
    (starRingEnd ℂ) (Maxwell.curl F x i)=Maxwell.curl F x i := by
  have hp (a b : Fin 3) := partial_conj (fun y => F y b) (hf b) (fun y => hr y b) x a
  fin_cases i <;> simp [Maxwell.curl,Maxwell.pd,hp]

theorem toroidal_conj (l : ℕ) (k : ℝ) (p : Poly) (x : Space) (i : Fin 3) :
    (starRingEnd ℂ) (DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l k p) x i)=
      DebyeCalculus.toroidal (SolidScalarHelmholtz.wave l k p) x i := by
  apply curl_conj
  · intro j
    intro y
    exact (DebyeCalculus.radialVector_smooth _ y (SolidScalarHelmholtz.wave_contDiff l k p).contDiffAt j).differentiableAt (by simp)
  · intro y j
    simp only [DebyeCalculus.radialVector,map_mul,Complex.conj_ofReal,wave_conj]

theorem electric_conj (l : ℕ) (k : ℝ) (p : Poly) (x : Space) (i : Fin 3) :
    (starRingEnd ℂ) (DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave l k p) x i)=
      DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave l k p) x i := by
  apply curl_conj
  · intro j
    intro y
    exact (DebyeCalculus.toroidal_smooth _ y (SolidScalarHelmholtz.wave_contDiff l k p).contDiffAt j).differentiableAt (by simp)
  · exact toroidal_conj l k p

end OQ14.SolidWaveReality

#print axioms OQ14.SolidWaveReality.F_conj
#print axioms OQ14.SolidWaveReality.wave_conj
#print axioms OQ14.SolidWaveReality.wave_neg
#print axioms OQ14.SolidWaveReality.partial_conj
#print axioms OQ14.SolidWaveReality.curl_conj
#print axioms OQ14.SolidWaveReality.toroidal_conj
#print axioms OQ14.SolidWaveReality.electric_conj
