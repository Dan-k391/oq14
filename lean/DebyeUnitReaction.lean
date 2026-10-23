import SolidWaveReality

/-! Exact unit-frequency standard regular-vector normalization of the physical reaction tensor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.DebyeUnitReaction
open OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open OQ14.PlaneDebyeCoefficients OQ14.DebyeReactionExpansion

def electric (a : PositiveIndex) (x : Space) (i : Fin 3) : ℂ :=
  DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave (a.1+1) 1 (representative (a.1+1) a.2)) x i
def toroidal (a : PositiveIndex) (x : Space) (i : Fin 3) : ℂ :=
  DebyeCalculus.toroidal (SolidScalarHelmholtz.wave (a.1+1) 1 (representative (a.1+1) a.2)) x i

theorem phase_product (l : ℕ) :
    (starRingEnd ℂ) (phaseCoefficient l 1)*phaseCoefficient l 1=(16*Real.pi^2 : ℂ) := by
  unfold phaseCoefficient
  simp only [map_mul,map_pow,Complex.conj_I,Complex.conj_ofReal,map_neg,map_one,map_ofNat,Complex.ofReal_one]
  have hi : (-Complex.I)^l*Complex.I^l=1 := by rw [← mul_pow];simp [Complex.I_sq]
  calc
    _ = (4*Real.pi : ℂ)^2*((-Complex.I)^l*Complex.I^l)*((-1 : ℂ)^(2*l)) := by ring
    _ = _ := by rw [hi,pow_mul];norm_num;ring

theorem term_poloidal (a : PositiveIndex) (x y : Space) (i j : Fin 3) :
    (((1^3/(16*Real.pi^2) : ℝ) : ℂ)*
      ((starRingEnd ℂ) (coefficient 1 x i (Sum.inl a))*coefficient 1 y j (Sum.inl a)))=
      (normalizer a.1 : ℂ)^2*electric a x i*electric a y j := by
  have hw := SolidWaveReality.wave_neg (a.1+1) 1 (representative (a.1+1) a.2)
  change SolidScalarHelmholtz.wave (a.1+1) (-1) (representative (a.1+1) a.2)=_ at hw
  simp only [coefficient,Sum.elim_inl,Complex.ofReal_one,hw,mul_neg,mul_one]
  change (((1^3/(16*Real.pi^2) : ℝ) : ℂ)*
    ((starRingEnd ℂ) ((normalizer a.1 : ℂ)*(phaseCoefficient (a.1+1) 1/(-Complex.I))*electric a x i)*
      ((normalizer a.1 : ℂ)*(phaseCoefficient (a.1+1) 1/(-Complex.I))*electric a y j)))=_
  have he : (starRingEnd ℂ) (electric a x i)=electric a x i := SolidWaveReality.electric_conj _ 1 _ x i
  simp only [map_mul,map_div₀,Complex.conj_ofReal,map_neg,Complex.conj_I,he]
  have hp := phase_product (a.1+1)
  have hpi : (Real.pi : ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp [hpi,Complex.I_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  linear_combination ((normalizer a.1 : ℂ)^2*electric a x i*electric a y j)*(phase_product (1+a.1))

theorem term_toroidal (a : PositiveIndex) (x y : Space) (i j : Fin 3) :
    (((1^3/(16*Real.pi^2) : ℝ) : ℂ)*
      ((starRingEnd ℂ) (coefficient 1 x i (Sum.inr a))*coefficient 1 y j (Sum.inr a)))=
      (normalizer a.1 : ℂ)^2*toroidal a x i*toroidal a y j := by
  have hw := SolidWaveReality.wave_neg (a.1+1) 1 (representative (a.1+1) a.2)
  change SolidScalarHelmholtz.wave (a.1+1) (-1) (representative (a.1+1) a.2)=_ at hw
  simp only [coefficient,Sum.elim_inr,Complex.ofReal_one,hw]
  change (((1^3/(16*Real.pi^2) : ℝ) : ℂ)*
    ((starRingEnd ℂ) ((normalizer a.1 : ℂ)*phaseCoefficient (a.1+1) 1*toroidal a x i)*
      ((normalizer a.1 : ℂ)*phaseCoefficient (a.1+1) 1*toroidal a y j)))=_
  have he : (starRingEnd ℂ) (toroidal a x i)=toroidal a x i := SolidWaveReality.toroidal_conj _ 1 _ x i
  simp only [map_mul,Complex.conj_ofReal,he]
  have hp := phase_product (a.1+1)
  have hpi : (Real.pi : ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp [hpi]
  linear_combination ((normalizer a.1 : ℂ)^2*toroidal a x i*toroidal a y j)*hp

theorem normalizer_sq (n : ℕ) :
    (normalizer n : ℂ)^2=(((n : ℂ)+1)*((n : ℂ)+2))⁻¹ := by
  have hn : ((n : ℂ)+1)*((n : ℂ)+2)≠0 := by
    exact_mod_cast (show ((n : ℝ)+1)*((n : ℝ)+2)≠0 by positivity)
  rw [inv_eq_one_div]
  apply (eq_div_iff hn).mpr
  have h := normalizer_identity n
  exact_mod_cast (show (normalizer n)^2*(((n : ℝ)+1)*((n : ℝ)+2))=1 by nlinarith [h])

def weight (a : PositiveIndex) : ℂ := (((a.1 : ℂ)+1)*((a.1 : ℂ)+2))⁻¹

theorem J_unit_expansion (x y : Space) (i j : Fin 3) :
    HasSum (Sum.elim
      (fun a : PositiveIndex => weight a*electric a x i*electric a y j)
      (fun a : PositiveIndex => weight a*toroidal a x i*toroidal a y j))
      (SphereReactionKernel.J 1 (x-y) i j) := by
  convert J_expansion 1 (by norm_num) x y i j using 1
  funext a
  cases a with
  | inl a => simpa only [Sum.elim_inl,normalizer_sq,weight] using (term_poloidal a x y i j).symm
  | inr a => simpa only [Sum.elim_inr,normalizer_sq,weight] using (term_toroidal a x y i j).symm

theorem J_unit_paired_expansion (x y : Space) (i j : Fin 3) :
    HasSum (fun a : PositiveIndex => weight a*
      (electric a x i*electric a y j+toroidal a x i*toroidal a y j))
      (SphereReactionKernel.J 1 (x-y) i j) := by
  let f := fun a : PositiveIndex => weight a*electric a x i*electric a y j
  let g := fun a : PositiveIndex => weight a*toroidal a x i*toroidal a y j
  have h : HasSum (Sum.elim f g) (SphereReactionKernel.J 1 (x-y) i j) := J_unit_expansion x y i j
  have hf : Summable f := by
    simpa only [Function.comp_def,Sum.elim_inl] using h.summable.comp_injective Sum.inl_injective
  have hg : Summable g := by
    simpa only [Function.comp_def,Sum.elim_inr] using h.summable.comp_injective Sum.inr_injective
  have hs : HasSum (Sum.elim f g) ((∑' a,f a)+(∑' a,g a)) := hf.hasSum.sum hg.hasSum
  have he := hs.unique h
  convert hf.hasSum.add hg.hasSum using 1
  · funext a
    dsimp [f,g]
    ring
  · exact he.symm

end OQ14.DebyeUnitReaction

#print axioms OQ14.DebyeUnitReaction.phase_product
#print axioms OQ14.DebyeUnitReaction.term_poloidal
#print axioms OQ14.DebyeUnitReaction.term_toroidal
#print axioms OQ14.DebyeUnitReaction.normalizer_sq
#print axioms OQ14.DebyeUnitReaction.J_unit_expansion
#print axioms OQ14.DebyeUnitReaction.J_unit_paired_expansion
