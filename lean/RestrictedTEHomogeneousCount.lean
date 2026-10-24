import RestrictedTEPlaneJets

/-! The explicit parity-device counting inequalities extend from unit physical power to every
positive power by quadratic homogeneity of the actual plane flux. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEHomogeneousCount
open Complex MeasureTheory Metric Set Filter Maxwell RestrictedTEPlaneLocal SymmetricHarmonicJets
open OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEPlaneJets
open OQ14.RestrictedTETotalLinear OQ14.RestrictedTEPassageTransfer
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space
abbrev Plane := PlaneInverseCube.Plane

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem physicalPower_smul (z : ℂ) (A : Index →₀ ℂ) :
    RestrictedTEIncoming.physicalPower (z • A)=‖z‖^2*RestrictedTEIncoming.physicalPower A := by
  rw [← RestrictedTEInput.input_norm_sq,← RestrictedTEInput.input_norm_sq,map_smul,norm_smul,mul_pow]

theorem passage_const_mul {P : Type*} [MeasurableSpace P] (μ : Measure P) (D : Set P) (c : ℝ)
    (F : P → ℂ) : passage μ D (fun q => (c : ℂ)*F q)=c*passage μ D F := by
  unfold passage
  rw [integral_const_mul,Complex.re_ofReal_mul]

theorem bypass_const_mul {P : Type*} [MeasurableSpace P] (μ : Measure P) (D : Set P) (c : ℝ) (hc : 0 ≤ c)
    (F : P → ℂ) : bypass μ D (fun q => (c : ℂ)*F q)=c*bypass μ D F := by
  unfold bypass
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with q
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]

/-- Quadratic homogeneity of the actual plane flux in the coefficient vector. -/
theorem Fflux_smul (p : ℝ → ι → Space) (ρ χ R b γ : ℝ) (hρ : 0<ρ) (hχ : 0≤χ) (hγ : 0<γ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh' : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|) (a : ℝ) (ha : 0<a) (ha1 : a≤1)
    (z : ℂ) (A' : Index →₀ ℂ) (q : Plane) :
    Fflux p ρ χ R b hρ hχ hi a (z • A') q=(‖z‖^2 : ℝ)*Fflux p ρ χ R b hρ hχ hi a A' q := by
  have hsesq := fluxForm_sesq p ρ χ R b (γ*a) a hρ hχ hi (mul_pos hγ ha) ha ha1
    (fun l => by have := hh' a ha ha1 l; linarith) q
  unfold Fflux
  rw [totalFlux_eq_diagonal,totalFlux_eq_diagonal,hsesq.smul_left,hsesq.smul_right]
  simp only [smul_eq_mul]
  rw [← mul_assoc,Complex.mul_conj,Complex.normSq_eq_norm_sq]

/-- Counting inequalities for every element of the span with positive physical power. -/
theorem explicit_parity_device_counting_homogeneous (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0) (hγ : 0<γ)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh' : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|)
    (c : ι → Plane) (h : ι → ℝ) (hhpos : ∀ l, 0<h l) (hp : ∀ a l, p a l=abovePoint (c l) (h l*a))
    (hcd : ∀ l k, l≠k → c l≠c k) (n : ι → Plane) (hn : ∀ l, ‖n l‖=1) (D : Set Plane)
    (hD : ∀ l, ∃ s0 : ℝ, 0<s0 ∧ ∀ s : ℝ, 0<s → s≤s0 →
      D ∩ Metric.closedBall (c l) s=(fun q => q-c l) ⁻¹' (U (n l) ∩ Metric.closedBall 0 s))
    (A : κ → Index →₀ ℂ) (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)))
    (HT : ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 → ∀ l,
      magnetic A' (MaxwellPlaneTail.planePoint (c l)) 0=-(mj A' c n l)*((n l 1 : ℝ) : ℂ) ∧
        magnetic A' (MaxwellPlaneTail.planePoint (c l)) 1=mj A' c n l*((n l 0 : ℝ) : ℂ))
    (HK : ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 → ∀ l,
      0≤(kap ρ χ A' c n l).re ∧ (kap ρ χ A' c n l).im=0)
    (p0 ηt δt : ℝ)
    (HB : ∀ A'∈Submodule.span ℂ (Set.range A), RestrictedTEIncoming.physicalPower A'=1 →
      ∑ l, (kap ρ χ A' c n l).re*halfPlane (n l) (h l)=p0)
    (hη : ηt<p0) (hδt : p0<δt) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ A'∈Submodule.span ℂ (Set.range A), 0<RestrictedTEIncoming.physicalPower A' →
      ηt*RestrictedTEIncoming.physicalPower A'≤passage volume D (Fflux p ρ χ R b hρ hχ hi a A') ∧
      bypass volume D (Fflux p ρ χ R b hρ hχ hi a A')≤δt*RestrictedTEIncoming.physicalPower A' := by
  have hunit := explicit_parity_device_counting p ρ χ δ R b γ hρ hχ hδ hR hb hγ hsep hi hh' c h hhpos hp hcd n hn D hD
    A horth HT HK p0 ηt δt HB hη hδt
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, 0<a ∧ a≤1 := by
    filter_upwards [self_mem_nhdsWithin,Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with a ha ha1
    exact ⟨ha,ha1.2.le⟩
  filter_upwards [hunit,hsmall] with a hA ha
  intro A' hA' hP
  set P := RestrictedTEIncoming.physicalPower A' with hPdef
  let z : ℂ := ((Real.sqrt P)⁻¹ : ℝ)
  have hz : ‖z‖^2=P⁻¹ := by
    simp only [z,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg P))]
    rw [inv_pow,Real.sq_sqrt hP.le]
  have hmem : z • A'∈Submodule.span ℂ (Set.range A) := Submodule.smul_mem _ z hA'
  have hpow : RestrictedTEIncoming.physicalPower (z • A')=1 := by
    rw [physicalPower_smul,hz,← hPdef,inv_mul_cancel₀ hP.ne']
  obtain ⟨hpass,hbyp⟩ := hA (z • A') hmem hpow
  have hF : Fflux p ρ χ R b hρ hχ hi a (z • A')=fun q => ((P⁻¹ : ℝ) : ℂ)*Fflux p ρ χ R b hρ hχ hi a A' q := by
    funext q
    rw [Fflux_smul p ρ χ R b γ hρ hχ hγ hi hh' a ha.1 ha.2 z A' q,hz]
  rw [hF,passage_const_mul] at hpass
  rw [hF,bypass_const_mul _ _ _ (inv_nonneg.mpr hP.le)] at hbyp
  constructor
  · have := mul_le_mul_of_nonneg_left hpass hP.le
    rw [← mul_assoc,mul_inv_cancel₀ hP.ne',one_mul] at this
    rw [mul_comm ηt P]
    exact this
  · have := mul_le_mul_of_nonneg_left hbyp hP.le
    rw [← mul_assoc,mul_inv_cancel₀ hP.ne',one_mul] at this
    rw [mul_comm δt P]
    exact this

end OQ14.RestrictedTEHomogeneousCount
#print axioms OQ14.RestrictedTEHomogeneousCount.physicalPower_smul
#print axioms OQ14.RestrictedTEHomogeneousCount.passage_const_mul
#print axioms OQ14.RestrictedTEHomogeneousCount.bypass_const_mul
#print axioms OQ14.RestrictedTEHomogeneousCount.Fflux_smul
#print axioms OQ14.RestrictedTEHomogeneousCount.explicit_parity_device_counting_homogeneous
