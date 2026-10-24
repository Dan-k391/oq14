import RestrictedTETotalLinear
import RestrictedTEInput

/-! Uniform whole-plane convergence over the unit sphere (power ball) of a constructed finite physical input space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEUnitSphere
open Complex MeasureTheory Metric Set Filter Maxwell PlaneSourceKernel MaxwellRadiation
open SymmetricHarmonicJets RestrictedTEPlaneLocal OQ14.RestrictedTETotalLinear
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- Quadratic homogeneity of the difference form. -/
theorem diffForm_scale (p : ℝ → ι → Space) (ρ χ R b d a : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (hd : 0<d) (ha : 0<a) (ha1 : a≤1)
    (hh : ∀ l, d+ρ*a≤|p a l 2|) (q : Plane) (z : ℂ) (A : Index →₀ ℂ) :
    diffForm p ρ χ R b a hρ hχ hi q (z • A) (z • A)=
      z*(conj z*diffForm p ρ χ R b a hρ hχ hi q A A) := by
  have h := diffForm_sesq p ρ χ R b d a hρ hχ hi hd ha ha1 hh q
  rw [h.smul_left,h.smul_right]
  rfl

theorem unit_sphere_form (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0) (hγ : 0<γ)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|) (A : κ → Index →₀ ℂ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ c : κ → ℂ, (∑ j, ‖c j‖^2)≤1 →
      Integrable (fun q : Plane => diffForm p ρ χ R b a hρ hχ hi q (∑ j, c j • A j) (∑ j, c j • A j)) ∧
        (∫ q : Plane, ‖diffForm p ρ χ R b a hρ hχ hi q (∑ j, c j • A j) (∑ j, c j • A j)‖)≤ε := by
  classical
  let s : Finset Index := Finset.univ.biUnion (fun j => (A j).support)
  let K : ℝ := 1+∑ j, ∑ i ∈ s, ‖A j i‖
  have hK0 : 0≤∑ j, ∑ i ∈ s, ‖A j i‖ :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => norm_nonneg _))
  have hK : 1≤K := by
    dsimp only [K]
    linarith
  have hKpos : 0<K := lt_of_lt_of_le one_pos hK
  have hu := uniform_form p ρ χ δ R b γ hρ hχ hδ hR hb hγ hsep hi hh s (ε/K^2) (by positivity)
  have hlt1 : ∀ᶠ a : ℝ in 𝓝[>] 0, a<1 := nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)
  filter_upwards [hu,self_mem_nhdsWithin,hlt1] with a hu ha ha1
  change 0<a at ha
  intro c hc
  have hc1 (j : κ) : ‖c j‖≤1 := by
    have h1 : ‖c j‖^2≤∑ j, ‖c j‖^2 :=
      Finset.single_le_sum (f := fun j => ‖c j‖^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    by_contra hne
    push_neg at hne
    nlinarith [norm_nonneg (c j)]
  let Ac : Index →₀ ℂ := ∑ j, c j • A j
  let B : Index →₀ ℂ := ((K : ℝ) : ℂ)⁻¹ • Ac
  have hAc_apply (i : Index) : Ac i=∑ j, c j*A j i := by
    simp only [Ac,Finsupp.coe_finset_sum,Finset.sum_apply,Finsupp.smul_apply,smul_eq_mul]
  have hB_supp : ∀ i, i∉s → B i=0 := by
    intro i hi'
    have h0 : ∀ j, A j i=0 := fun j => by
      by_contra hne
      exact hi' (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,Finsupp.mem_support_iff.mpr hne⟩)
    simp only [B,Finsupp.smul_apply,smul_eq_mul,hAc_apply,h0,mul_zero,Finset.sum_const_zero]
  have hB_bound : ∀ i, ‖B i‖≤1 := by
    intro i
    by_cases his : i∈s
    · have h1 : ‖Ac i‖≤∑ j, ‖A j i‖ := by
        rw [hAc_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hc1 j)
      have h2 : (∑ j, ‖A j i‖)≤∑ j, ∑ i ∈ s, ‖A j i‖ := by
        calc (∑ j, ‖A j i‖)≤∑ i' ∈ s, ∑ j, ‖A j i'‖ :=
              Finset.single_le_sum (f := fun i' => ∑ j, ‖A j i'‖)
                (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) his
          _ = ∑ j, ∑ i ∈ s, ‖A j i‖ := Finset.sum_comm
      have h3 : ‖Ac i‖≤K-1 := by
        have : K-1=∑ j, ∑ i ∈ s, ‖A j i‖ := by dsimp only [K]; ring
        linarith
      simp only [B,Finsupp.smul_apply,smul_eq_mul,norm_mul,norm_inv,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos hKpos]
      rw [inv_mul_le_iff₀ hKpos]
      linarith
    · rw [hB_supp i his]
      simp
  have hAcB : Ac=((K : ℝ) : ℂ) • B := by
    simp only [B,smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hKpos.ne'),one_smul]
  obtain ⟨hI,hM⟩ := hu B hB_supp hB_bound
  have hq (q : Plane) : diffForm p ρ χ R b a hρ hχ hi q Ac Ac=
      ((K^2 : ℝ) : ℂ)*diffForm p ρ χ R b a hρ hχ hi q B B := by
    rw [hAcB,diffForm_scale p ρ χ R b (γ*a) a hρ hχ hi (mul_pos hγ ha) ha ha1.le
      (fun l => by simpa only [add_mul] using hh a ha ha1.le l) q,Complex.conj_ofReal]
    push_cast
    ring
  have hfun : (fun q : Plane => diffForm p ρ χ R b a hρ hχ hi q Ac Ac)=
      fun q => ((K^2 : ℝ) : ℂ)*diffForm p ρ χ R b a hρ hχ hi q B B := funext hq
  change Integrable (fun q : Plane => diffForm p ρ χ R b a hρ hχ hi q Ac Ac) ∧
    (∫ q : Plane, ‖diffForm p ρ χ R b a hρ hχ hi q Ac Ac‖)≤ε
  simp only [hq]
  refine ⟨hI.const_mul _,?_⟩
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg K)]
  rw [integral_const_mul]
  calc K^2*(∫ q : Plane, ‖diffForm p ρ χ R b a hρ hχ hi q B B‖)≤K^2*(ε/K^2) :=
        mul_le_mul_of_nonneg_left hM (sq_nonneg K)
    _ = ε := by field_simp

/-- Uniform finite-input convergence of the actual complete parity flux to the exact finite-dipole flux on the
Euclidean unit ball of the coefficient space of any finite family of fixed harmonic TE coefficient vectors. -/
theorem uniform_unit_sphere (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0) (hγ : 0<γ)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|) (A : κ → Index →₀ ℂ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ c : κ → ℂ, (∑ j, ‖c j‖^2)≤1 →
      Integrable (fun q : Plane =>
        RestrictedTETotalFlux.totalFlux (b/a)
            (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi (∑ j, c j • A j) a)
            ((a : ℂ)⁻¹ • (∑ j, c j • A j)) q-
          RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
            (fun l => StaticSpherePolarization.polarization χ
              (electric ((a : ℂ)⁻¹ • (∑ j, c j • A j)) (p a l)))
            ((a : ℂ)⁻¹ • (∑ j, c j • A j)) q) ∧
      (∫ q : Plane, ‖RestrictedTETotalFlux.totalFlux (b/a)
            (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi (∑ j, c j • A j) a)
            ((a : ℂ)⁻¹ • (∑ j, c j • A j)) q-
          RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
            (fun l => StaticSpherePolarization.polarization χ
              (electric ((a : ℂ)⁻¹ • (∑ j, c j • A j)) (p a l)))
            ((a : ℂ)⁻¹ • (∑ j, c j • A j)) q‖)≤ε :=
  (unit_sphere_form p ρ χ δ R b γ hρ hχ hδ hR hb hγ hsep hi hh A ε hε).mono
    (fun _ h c hc => h c hc)

/-- The same convergence uniformly over the physical-power unit ball of the complex span of finitely many
coefficient vectors whose actual physical incoming data are orthonormal. -/
theorem uniform_physical_unit_ball (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0) (hγ : 0<γ)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|) (A : κ → Index →₀ ℂ)
    (horth : Orthonormal ℂ (fun j => RestrictedTEInput.input (A j))) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ A' : Index →₀ ℂ, A'∈Submodule.span ℂ (Set.range A) →
      RestrictedTEIncoming.physicalPower A'≤1 →
      Integrable (fun q : Plane =>
        RestrictedTETotalFlux.totalFlux (b/a)
            (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A' a) ((a : ℂ)⁻¹ • A') q-
          RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
            (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A') (p a l)))
            ((a : ℂ)⁻¹ • A') q) ∧
      (∫ q : Plane, ‖RestrictedTETotalFlux.totalFlux (b/a)
            (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A' a) ((a : ℂ)⁻¹ • A') q-
          RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
            (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A') (p a l)))
            ((a : ℂ)⁻¹ • A') q‖)≤ε := by
  filter_upwards [uniform_unit_sphere p ρ χ δ R b γ hρ hχ hδ hR hb hγ hsep hi hh A ε hε] with a h A' hA' hP
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hA'
  have hpow : (∑ j, ‖c j‖^2)=RestrictedTEIncoming.physicalPower A' := by
    rw [← RestrictedTEInput.input_norm_sq,← hc]
    have hin : RestrictedTEInput.input (∑ j, c j • A j)=∑ j, c j • RestrictedTEInput.input (A j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => map_smul _ _ _)
    rw [hin]
    generalize hv : ∑ j, c j • RestrictedTEInput.input (A j)=v
    have this : @inner ℂ _ _ v v=∑ j, (starRingEnd ℂ) (c j)*c j := by
      rw [← hv]
      exact horth.inner_sum c c Finset.univ
    rw [inner_self_eq_norm_sq_to_K] at this
    simp only [Complex.conj_mul'] at this
    have h3 : ((∑ j, ‖c j‖^2 : ℝ) : ℂ)=((‖v‖^2 : ℝ) : ℂ) := by
      push_cast
      exact this.symm
    exact Complex.ofReal_injective h3
  rw [← hc]
  exact h c (hpow.trans_le hP)

end OQ14.RestrictedTEUnitSphere
#print axioms OQ14.RestrictedTEUnitSphere.diffForm_scale
#print axioms OQ14.RestrictedTEUnitSphere.unit_sphere_form
#print axioms OQ14.RestrictedTEUnitSphere.uniform_unit_sphere
#print axioms OQ14.RestrictedTEUnitSphere.uniform_physical_unit_ball
