import BarrierDegreeDecomp
import SourceRemotePlaneSeries

/-! All-degree paired-shell series: with the per-degree constants of `BarrierDegreeDecomp` the absolute
plane flux outside the core of the series over all degrees and all real modes (coefficients bounded by
a common constant) tends to zero with the shell index.  The real modes of all degrees are encoded by
the natural numbers through `Encodable (Σ l, Index l)` and extension by zero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.BarrierDegreeSeriesFlux
open MeasureTheory Set Metric Filter Complex OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.SourceRemotePlaneBand OQ14.PlaneInverseCube OQ14.SphereHarmonicBasis OQ14.AngularExteriorBounds
  OQ14.BarrierDegreeFluxConstants OQ14.BarrierDegreeDecomp OQ14.HankelRealBasis
  OQ14.SourceRemotePlaneSeries
open scoped Topology ComplexConjugate

/-- A real mode of the all-degree series: a degree and an element of its orthonormal real basis. -/
abbrev Mode := Σ l : ℕ, Index l

/-! ### Encoding of the modes by the natural numbers (extension by zero) -/

/-- Degree of the `i`-th encoded mode (`0` off the range of the encoding). -/
def encl : ℕ → ℕ := Function.extend (Encodable.encode : Mode → ℕ) (fun p => p.1) 0

/-- Polynomial of the `i`-th encoded mode (`representative`; the zero polynomial off the range). -/
def encP : ℕ → Poly := Function.extend (Encodable.encode : Mode → ℕ)
  (fun p => (representative p.1 p.2 : Poly)) 0

/-- Coefficient of the `i`-th encoded mode: `a p * regular p.1 s0` (`0` off the range). -/
def encc (a : Mode → ℂ) (s0 : ℝ) : ℕ → ℂ := Function.extend (Encodable.encode : Mode → ℕ)
  (fun p => a p*((regular p.1 s0 : ℝ) : ℂ)) 0

/-- Extension by zero of a family indexed by the modes. -/
def encK (f : Mode → ℝ) : ℕ → ℝ := Function.extend (Encodable.encode : Mode → ℕ) f 0

theorem encl_encode (p : Mode) : encl (Encodable.encode p)=p.1 :=
  Encodable.encode_injective.extend_apply _ _ _

theorem encP_encode (p : Mode) : encP (Encodable.encode p)=(representative p.1 p.2 : Poly) :=
  Encodable.encode_injective.extend_apply _ _ _

theorem encc_encode (a : Mode → ℂ) (s0 : ℝ) (p : Mode) :
    encc a s0 (Encodable.encode p)=a p*((regular p.1 s0 : ℝ) : ℂ) :=
  Encodable.encode_injective.extend_apply _ _ _

theorem encK_encode (f : Mode → ℝ) (p : Mode) : encK f (Encodable.encode p)=f p :=
  Encodable.encode_injective.extend_apply _ _ _

theorem encl_off (i : ℕ) (h : ¬∃ p : Mode, Encodable.encode p=i) : encl i=0 := by
  unfold encl
  rw [Function.extend_apply' _ _ _ h]
  rfl

theorem encP_off (i : ℕ) (h : ¬∃ p : Mode, Encodable.encode p=i) : encP i=0 := by
  unfold encP
  rw [Function.extend_apply' _ _ _ h]
  rfl

theorem encc_off (a : Mode → ℂ) (s0 : ℝ) (i : ℕ) (h : ¬∃ p : Mode, Encodable.encode p=i) :
    encc a s0 i=0 := by
  unfold encc
  rw [Function.extend_apply' _ _ _ h]
  rfl

theorem encK_off (f : Mode → ℝ) (i : ℕ) (h : ¬∃ p : Mode, Encodable.encode p=i) : encK f i=0 := by
  unfold encK
  rw [Function.extend_apply' _ _ _ h]
  rfl

theorem encP_homogeneous (i : ℕ) : (encP i).IsHomogeneous (encl i) := by
  by_cases h : ∃ p : Mode, Encodable.encode p=i
  · obtain ⟨p,rfl⟩ := h
    rw [encP_encode,encl_encode]
    exact representative_homogeneous p.1 p.2
  · rw [encP_off i h,encl_off i h]
    exact MvPolynomial.isHomogeneous_zero _ _ _

theorem summable_encK (f : Mode → ℝ) (hf : Summable f) : Summable (encK f) :=
  (summable_extend_zero Encodable.encode_injective).mpr hf

/-! ### Summability over the modes of a degree-dependent constant -/

/-- The number of modes of degree `l` is at most `(l+1)^3`, so a family `G l` with `(l+1)^3 G l`
summable is summable over the modes. -/
theorem summable_mode_sigma (G : ℕ → ℝ) (hG0 : ∀ l, 0 ≤ G l)
    (hG : Summable (fun l : ℕ => ((l : ℝ)+1)^3*G l)) (A : ℝ) (hA : 0 ≤ A) :
    Summable (fun p : Mode => A*G p.1) := by
  rw [summable_sigma_of_nonneg (fun p => mul_nonneg hA (hG0 _))]
  refine ⟨fun l => (hasSum_fintype _).summable,?_⟩
  refine Summable.of_nonneg_of_le (fun l => tsum_nonneg (fun m => mul_nonneg hA (hG0 _)))
    (fun l => ?_) (hG.mul_left A)
  show ∑' m : Index l,A*G l ≤ A*(((l : ℝ)+1)^3*G l)
  rw [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hc : (Module.finrank ℝ (harmonicSpace l) : ℝ) ≤ ((l : ℝ)+1)^3 := by
    exact_mod_cast OQ14.SphereHarmonicDimension.harmonicSpace_finrank_le l
  calc (Module.finrank ℝ (harmonicSpace l) : ℝ)*(A*G l) ≤ ((l : ℝ)+1)^3*(A*G l) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg hA (hG0 l))
    _ = A*(((l : ℝ)+1)^3*G l) := by ring

theorem cubic_Kone (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) :
    Summable (fun l : ℕ => ((l : ℝ)+1)^3*Kone q W s0 R1 l) := by
  refine (summable_Ub_weighted q W s0 R1 hq hs0 hR1 hρ 4).congr (fun l => ?_)
  unfold Kone
  ring

theorem cubic_Ktwo (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) :
    Summable (fun l : ℕ => ((l : ℝ)+1)^3*Ktwo q W s0 R1 l) := by
  refine summable_of_le_weighted q W s0 R1 hq hs0 hR1 hρ _ 1 5 (fun l => ?_) ?_
  · have := Ktwo_nonneg q W s0 R1 hq hs0.le hR1 l
    show 0 ≤ ((l : ℝ)+1)^3*Ktwo q W s0 R1 l
    positivity
  · intro l
    have hU := Ub_nonneg q W s0 R1 hq hs0.le hR1 l
    have he := envelope_nonnegative l
    unfold Ktwo
    have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have h : ((l : ℝ)+1)^3*((l : ℝ)*(l+1)) ≤ 1*((l : ℝ)+1)^5 := by
      have h4 : (0 : ℝ) ≤ ((l : ℝ)+1)^4 := by positivity
      nlinarith
    calc ((l : ℝ)+1)^3*(((l : ℝ)*(l+1))*envelope l*Ub q W s0 R1 l)
        = (((l : ℝ)+1)^3*((l : ℝ)*(l+1)))*envelope l*Ub q W s0 R1 l := by ring
      _ ≤ (1*((l : ℝ)+1)^5)*envelope l*Ub q W s0 R1 l :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h he) hU
      _ = 1*(((l : ℝ)+1)^5*envelope l*Ub q W s0 R1 l) := by ring

theorem cubic_Lone (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) :
    Summable (fun l : ℕ => ((l : ℝ)+1)^3*Lone q W s0 R1 l) := by
  refine ((summable_Ub_weighted q W s0 R1 hq hs0 hR1 hρ 3).mul_left 2).congr (fun l => ?_)
  unfold Lone
  ring

theorem mode_cubic (tm : Bool) (q W s0 R1 : ℝ) (hq : 1 ≤ q) (hs0 : 0<s0) (hR1 : 0<R1)
    (hρ : base*Real.exp (1/(4*q))*s0 < R1) :
    Summable (fun l : ℕ => ((l : ℝ)+1)^3*mK1 tm q W s0 R1 l) ∧
    Summable (fun l : ℕ => ((l : ℝ)+1)^3*mK2 tm q W s0 R1 l) ∧
    Summable (fun l : ℕ => ((l : ℝ)+1)^3*mL1 tm q W s0 R1 l) ∧
    Summable (fun l : ℕ => ((l : ℝ)+1)^3*mL2 tm q W s0 R1 l) := by
  have h1 := cubic_Kone q W s0 R1 hq hs0 hR1 hρ
  have h2 := cubic_Ktwo q W s0 R1 hq hs0 hR1 hρ
  have h3 := cubic_Lone q W s0 R1 hq hs0 hR1 hρ
  have z : Summable (fun l : ℕ => ((l : ℝ)+1)^3*(0 : ℝ)) := by simpa using summable_zero
  cases tm
  · simp only [mK1_false,mK2_false,mL1_false,mL2_false]
    exact ⟨h3,z,h1,h2⟩
  · simp only [mK1_true,mK2_true,mL1_true,mL2_true]
    exact ⟨h1,h2,h3,z⟩

/-! ### The all-degree series -/

/-- **All-degree paired-shell series, absolute plane flux outside the core.**  For `tmE tmH : Bool`,
`q ≥ 1`, `n`, an inner scale `s0 > 0` and coefficient families on all real modes of all degrees bounded
by `A`, the series with the `ℕ`-indexed data obtained by encoding the modes (`encl`, `encP`, `encc`)
has absolute plane flux over `{radius s < ‖u‖}` tending to zero with the shell index `s`. -/
theorem paired_series_outside_core_flux_tendsto (tmE tmH : Bool) (q : ℝ) (hq : 0<q) (hq1 : 1 ≤ q)
    (n : ℕ) (s0 : ℝ) (hs0 : 0<s0) (aE aH : Mode → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hAE : ∀ p, ‖aE p‖ ≤ A) (hAH : ∀ p, ‖aH p‖ ≤ A) :
    Tendsto (fun s : ℕ => ∫ u : Plane in {u : Plane | (SourcePairedGeometry.physicalData q hq n s).R<‖u‖},
      ‖seriesFlux q hq n (fun _ => tmE) encl encP (encc aE s0) (fun _ => tmH) encl encP (encc aH s0) s u‖)
      atTop (𝓝 0) := by
  have hR1 := R1pair_pos q hq n s0
  have hρ := R1pair_rate q hq n s0 hs0
  obtain ⟨c1,c2,-,-⟩ := mode_cubic tmE q (Wpair q hq n) s0 (R1pair q hq n s0) hq1 hs0 hR1 hρ
  obtain ⟨-,-,d3,d4⟩ := mode_cubic tmH q (Wpair q hq n) s0 (R1pair q hq n s0) hq1 hs0 hR1 hρ
  have hnE := fun l => mode_constants_nonneg tmE q (Wpair q hq n) s0 (R1pair q hq n s0) hq1 hs0.le hR1 l
  have hnH := fun l => mode_constants_nonneg tmH q (Wpair q hq n) s0 (R1pair q hq n s0) hq1 hs0.le hR1 l
  refine series_outside_core_flux_tendsto q hq n (fun _ => tmE) encl encP encP_homogeneous (encc aE s0)
    (fun _ => tmH) encl encP encP_homogeneous (encc aH s0)
    (encK fun p => A*mK1 tmE q (Wpair q hq n) s0 (R1pair q hq n s0) p.1)
    (encK fun p => A*mK2 tmE q (Wpair q hq n) s0 (R1pair q hq n s0) p.1)
    (encK fun p => A*mL1 tmH q (Wpair q hq n) s0 (R1pair q hq n s0) p.1)
    (encK fun p => A*mL2 tmH q (Wpair q hq n) s0 (R1pair q hq n s0) p.1)
    (summable_encK _ (summable_mode_sigma _ (fun l => (hnE l).1) c1 A hA))
    (summable_encK _ (summable_mode_sigma _ (fun l => (hnE l).2.1) c2 A hA))
    (summable_encK _ (summable_mode_sigma _ (fun l => (hnH l).2.2.1) d3 A hA))
    (summable_encK _ (summable_mode_sigma _ (fun l => (hnH l).2.2.2) d4 A hA))
    (s1pair q hq n s0) ?_ ?_
  · intro i s x hs hx
    by_cases h : ∃ p : Mode, Encodable.encode p=i
    · obtain ⟨p,rfl⟩ := h
      simp only [encK_encode,encl_encode,encP_encode,encc_encode]
      have hd := (paired_mode_decomp tmE q hq hq1 n s0 hs0 p.1 p.2 s x hs hx).1
      have hx0 : x≠0 := norm_pos_iff.mp ((SourcePairedGeometry.physicalData q hq n s).hR.trans hx)
      have h2 := decomp_smul (aE p) hd
      rw [smul_smul] at h2
      exact decomp_mono hx0 h2 (mul_le_mul_of_nonneg_right (hAE p) (hnE p.1).1)
        (mul_le_mul_of_nonneg_right (hAE p) (hnE p.1).2.1)
    · rw [encK_off _ i h,encK_off _ i h,encc_off _ _ i h,zero_smul]
      exact decomp_zero x
  · intro i s x hs hx
    by_cases h : ∃ p : Mode, Encodable.encode p=i
    · obtain ⟨p,rfl⟩ := h
      simp only [encK_encode,encl_encode,encP_encode,encc_encode]
      have hd := (paired_mode_decomp tmH q hq hq1 n s0 hs0 p.1 p.2 s x hs hx).2
      have hx0 : x≠0 := norm_pos_iff.mp ((SourcePairedGeometry.physicalData q hq n s).hR.trans hx)
      have h2 := decomp_smul (aH p) hd
      rw [smul_smul] at h2
      exact decomp_mono hx0 h2 (mul_le_mul_of_nonneg_right (hAH p) (hnH p.1).2.2.1)
        (mul_le_mul_of_nonneg_right (hAH p) (hnH p.1).2.2.2)
    · rw [encK_off _ i h,encK_off _ i h,encc_off _ _ i h,zero_smul]
      exact decomp_zero x

/-! ### The series over the sigma type directly -/

/-- Electric field of the all-degree series, summed over the real modes of all degrees. -/
def sigmaElectric (tm : Bool) (q : ℝ) (hq : 0<q) (n : ℕ) (s0 : ℝ) (a : Mode → ℂ) (s : ℕ)
    (x : Space) : Vector :=
  ∑' p : Mode, a p • (((regular p.1 s0 : ℝ) : ℂ) • modeElectric tm
    { SourcePairedGeometry.physicalData q hq n s with l := p.1 } (representative p.1 p.2 : Poly) x)

/-- Magnetic field of the all-degree series, summed over the real modes of all degrees. -/
def sigmaMagnetic (tm : Bool) (q : ℝ) (hq : 0<q) (n : ℕ) (s0 : ℝ) (a : Mode → ℂ) (s : ℕ)
    (x : Space) : Vector :=
  ∑' p : Mode, a p • (((regular p.1 s0 : ℝ) : ℂ) • modeMagnetic tm
    { SourcePairedGeometry.physicalData q hq n s with l := p.1 } (representative p.1 p.2 : Poly) x)

/-- Plane flux density of the all-degree series over the sigma type. -/
def sigmaFlux (tmE tmH : Bool) (q : ℝ) (hq : 0<q) (n : ℕ) (s0 : ℝ) (aE aH : Mode → ℂ) (s : ℕ)
    (u : Plane) : ℂ :=
  crossProduct (sigmaElectric tmE q hq n s0 aE s (MaxwellPlaneTail.planePoint u))
    (conjugate (sigmaMagnetic tmH q hq n s0 aH s (MaxwellPlaneTail.planePoint u))) 2

theorem seriesElectric_eq (tm : Bool) (q : ℝ) (hq : 0<q) (n : ℕ) (s0 : ℝ) (a : Mode → ℂ) (s : ℕ)
    (x : Space) :
    seriesElectric q hq n (fun _ => tm) encl encP (encc a s0) s x=sigmaElectric tm q hq n s0 a s x := by
  unfold seriesElectric sigmaElectric
  have h : ∀ i : ℕ, encc a s0 i • modeElectric tm
      { SourcePairedGeometry.physicalData q hq n s with l := encl i } (encP i) x =
      Function.extend (Encodable.encode : Mode → ℕ) (fun p : Mode => a p • (((regular p.1 s0 : ℝ) : ℂ) •
        modeElectric tm { SourcePairedGeometry.physicalData q hq n s with l := p.1 }
          (representative p.1 p.2 : Poly) x)) 0 i := by
    intro i
    by_cases hi : ∃ p : Mode, Encodable.encode p=i
    · obtain ⟨p,rfl⟩ := hi
      rw [Encodable.encode_injective.extend_apply]
      simp only [encc_encode,encl_encode,encP_encode,smul_smul]
    · rw [Function.extend_apply' _ _ _ hi,encc_off a s0 i hi]
      simp
  exact (tsum_congr h).trans (tsum_extend_zero Encodable.encode_injective _)

theorem seriesMagnetic_eq (tm : Bool) (q : ℝ) (hq : 0<q) (n : ℕ) (s0 : ℝ) (a : Mode → ℂ) (s : ℕ)
    (x : Space) :
    seriesMagnetic q hq n (fun _ => tm) encl encP (encc a s0) s x=sigmaMagnetic tm q hq n s0 a s x := by
  unfold seriesMagnetic sigmaMagnetic
  have h : ∀ i : ℕ, encc a s0 i • modeMagnetic tm
      { SourcePairedGeometry.physicalData q hq n s with l := encl i } (encP i) x =
      Function.extend (Encodable.encode : Mode → ℕ) (fun p : Mode => a p • (((regular p.1 s0 : ℝ) : ℂ) •
        modeMagnetic tm { SourcePairedGeometry.physicalData q hq n s with l := p.1 }
          (representative p.1 p.2 : Poly) x)) 0 i := by
    intro i
    by_cases hi : ∃ p : Mode, Encodable.encode p=i
    · obtain ⟨p,rfl⟩ := hi
      rw [Encodable.encode_injective.extend_apply]
      simp only [encc_encode,encl_encode,encP_encode,smul_smul]
    · rw [Function.extend_apply' _ _ _ hi,encc_off a s0 i hi]
      simp
  exact (tsum_congr h).trans (tsum_extend_zero Encodable.encode_injective _)

theorem seriesFlux_eq_sigmaFlux (tmE tmH : Bool) (q : ℝ) (hq : 0<q) (n : ℕ) (s0 : ℝ)
    (aE aH : Mode → ℂ) (s : ℕ) (u : Plane) :
    seriesFlux q hq n (fun _ => tmE) encl encP (encc aE s0) (fun _ => tmH) encl encP (encc aH s0) s u=
      sigmaFlux tmE tmH q hq n s0 aE aH s u := by
  unfold seriesFlux sigmaFlux
  rw [seriesElectric_eq,seriesMagnetic_eq]

/-- **Same statement phrased for the sum over the sigma type directly.** -/
theorem paired_series_outside_core_flux_tendsto' (tmE tmH : Bool) (q : ℝ) (hq : 0<q) (hq1 : 1 ≤ q)
    (n : ℕ) (s0 : ℝ) (hs0 : 0<s0) (aE aH : Mode → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hAE : ∀ p, ‖aE p‖ ≤ A) (hAH : ∀ p, ‖aH p‖ ≤ A) :
    Tendsto (fun s : ℕ => ∫ u : Plane in {u : Plane | (SourcePairedGeometry.physicalData q hq n s).R<‖u‖},
      ‖sigmaFlux tmE tmH q hq n s0 aE aH s u‖) atTop (𝓝 0) := by
  have h := paired_series_outside_core_flux_tendsto tmE tmH q hq hq1 n s0 hs0 aE aH A hA hAE hAH
  simp only [seriesFlux_eq_sigmaFlux] at h
  exact h

end OQ14.BarrierDegreeSeriesFlux
#print axioms OQ14.BarrierDegreeSeriesFlux.encl_encode
#print axioms OQ14.BarrierDegreeSeriesFlux.encP_encode
#print axioms OQ14.BarrierDegreeSeriesFlux.encc_encode
#print axioms OQ14.BarrierDegreeSeriesFlux.encK_encode
#print axioms OQ14.BarrierDegreeSeriesFlux.encl_off
#print axioms OQ14.BarrierDegreeSeriesFlux.encP_off
#print axioms OQ14.BarrierDegreeSeriesFlux.encc_off
#print axioms OQ14.BarrierDegreeSeriesFlux.encK_off
#print axioms OQ14.BarrierDegreeSeriesFlux.encP_homogeneous
#print axioms OQ14.BarrierDegreeSeriesFlux.summable_encK
#print axioms OQ14.BarrierDegreeSeriesFlux.summable_mode_sigma
#print axioms OQ14.BarrierDegreeSeriesFlux.cubic_Kone
#print axioms OQ14.BarrierDegreeSeriesFlux.cubic_Ktwo
#print axioms OQ14.BarrierDegreeSeriesFlux.cubic_Lone
#print axioms OQ14.BarrierDegreeSeriesFlux.mode_cubic
#print axioms OQ14.BarrierDegreeSeriesFlux.paired_series_outside_core_flux_tendsto
#print axioms OQ14.BarrierDegreeSeriesFlux.seriesElectric_eq
#print axioms OQ14.BarrierDegreeSeriesFlux.seriesMagnetic_eq
#print axioms OQ14.BarrierDegreeSeriesFlux.seriesFlux_eq_sigmaFlux
#print axioms OQ14.BarrierDegreeSeriesFlux.paired_series_outside_core_flux_tendsto'
