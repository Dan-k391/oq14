import ConicalCommonErrorNorm

/-! Fixed witness-source gauge for actual finite angular illumination of the common material. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ConicalCommonFixedGauge
open MeasureTheory Set Metric Filter OQ14.NewtonL2
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

def totalSource (i : ι) (R k : ℝ) (d : Input) :=
  ConicalCommonEntire.polarization p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) -
    ConicalCommonBaseline.forcing p a center i

def source (i : ι) (R k : ℝ) (d : Input) (j : Fin 3) (x : Space) :=
  ConicalCommonEntire.source p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) j x -
    ConicalCommonMaterial.source p a center i j x

omit [DecidableEq ι] in
theorem source_ae (i : ι) (R k : ℝ) (d : Input) (j : Fin 3) :
    physicalCoordinate (totalSource p a center B hB hcontrast ha hsep i R k d) j =ᵐ[volume]
      source p a center B hB hcontrast ha hsep i R k d j :=
  ConicalResponseLinear.source_sub_ae _ _ _ _ (ConicalCommonEntire.source_ae p a center B hB hcontrast ha hsep R k _)
    (ConicalCommonBaseline.source_ae p a center i) j

omit [DecidableEq ι] in
theorem source_zero_outer (i : ι) (R T k : ℝ) (hRT : R ≤ T)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (d : Input) (j : Fin 3) (x : Space) (hx : x ∉ closedBall (0 : Space) T) :
    source p a center B hB hcontrast ha hsep i R k d j x = 0 := by
  have hxR : x ∉ closedBall (0 : Space) R := fun hxR => hx (closedBall_subset_closedBall hRT hxR)
  have hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T :=
    (hR i).trans (closedBall_subset_closedBall hRT)
  rw [source, ConicalCommonEntire.source_zero p a center B hB hcontrast ha hsep R k _ hR j x hxR,
    ConicalCommonMaterial.source_zero_global_outer p a center i j T hT x hx (ha i), sub_self]

def potential (i : ι) (R T k : ℝ) (hRT : R ≤ T)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R) (d : Input) :=
  ConicalTranslatedPotential.translated (center i)
    (ConicalCompactPotential.potentialData k T (totalSource p a center B hB hcontrast ha hsep i R k d)
      (source p a center B hB hcontrast ha hsep i R k d)
      (source_zero_outer p a center B hB hcontrast ha hsep i R T k hRT hR d)
      (source_ae p a center B hB hcontrast ha hsep i R k d))

def correction (i : ι) (R k : ℝ) (d : Input) (J : Maxwell.Field) (x : Space) (j : Fin 3) : ℂ :=
  J x j + ElectricPotentialDecomposition.correction k (source p a center B hB hcontrast ha hsep i R k d) (x+center i) j

omit [DecidableEq ι] in
theorem correction_continuous (i : ι) (R T k : ℝ) (hRT : R ≤ T)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R) (d : Input)
    (J : Maxwell.Field) (hJ : ∀ j, Continuous (fun x => J x j)) (j : Fin 3) :
    Continuous (fun x => correction p a center B hB hcontrast ha hsep i R k d J x j) :=
  (hJ j).add ((ElectricPotentialDecomposition.correction_continuous k T _ _
    (source_zero_outer p a center B hB hcontrast ha hsep i R T k hRT hR d)
    (source_ae p a center B hB hcontrast ha hsep i R k d) j).comp (continuous_id.add continuous_const))

omit [Fintype ι] [DecidableEq ι] in
theorem exists_extension (i : ι) (a' b k : ℝ) (hai : a' < (p i).cutoff.rIn) (hba : b < a') (d : Input) :
    ∃ J : Maxwell.Field, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x j)) ∧
      ∀ j x, x ∈ closedBall (0 : Space) b → J x j = ConicalCommonIncidentError.error (p i) a' k (center i) d j x := by
  have hex (j : Fin 3) := ExteriorGreen.smooth_localization isOpen_ball
    (isCompact_closedBall (0 : Space) b) (closedBall_subset_ball hba)
    (ConicalCommonIncidentError.error (p i) a' k (center i) d j)
    (ConicalCommonIncidentError.error_smooth (p i) a' k hai (center i) d j)
  choose J hJ hc he using hex
  exact ⟨fun x j => J j x, hJ, fun j x hx => (he j x hx).eq_of_nhds⟩

theorem fixed_electric_ae (i : ι) (R T k b : ℝ) (hRT : R ≤ T) (hb : b < a i)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (d : Input) (J : Maxwell.Field)
    (hJ : ∀ j x, x ∈ closedBall (0 : Space) b → J x j = ConicalCommonIncidentError.error (p i) (a i) k (center i) d j x)
    (j : Fin 3) : ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      FieldResponse.electric k (totalSource p a center B hB hcontrast ha hsep i R k d)
        (source p a center B hB hcontrast ha hsep i R k d) (x+center i) j + J x j =
      ConicalCommonEntire.electric p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) (x+center i) j := by
  have hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T :=
    (hR i).trans (closedBall_subset_closedBall hRT)
  have hsource : ∀ j y, y ∈ ball (center i) (a i) → ConicalCommonMaterial.source p a center i j y = 0 := by
    intro j y hy
    exact ConicalCommonMaterial.source_zero_material p a center ha hsep hai i i j y (ball_subset_closedBall hy)
  have hρzero : ∀ j y, y ∉ closedBall (0 : Space) T →
      ConicalCommonEntire.source p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) j y = 0 := by
    intro j y hy
    exact ConicalCommonEntire.source_zero p a center B hB hcontrast ha hsep R k _ hR j y
      (fun h => hy (closedBall_subset_closedBall hRT h))
  have hσzero : ∀ j y, y ∉ closedBall (0 : Space) T → ConicalCommonMaterial.source p a center i j y = 0 :=
    fun j y hy => ConicalCommonMaterial.source_zero_global_outer p a center i j T hT y hy (ha i)
  have he := (ae_restrict_iff' measurableSet_closedBall).mp
    (ConicalResponseLinear.electric_sub_ae k R T _ _ _ _
      (ConicalCommonEntire.source_ae p a center B hB hcontrast ha hsep R k _)
      (ConicalCommonBaseline.source_ae p a center i) hρzero hσzero j)
  have hs := SourceFreeOpenResponse.electric_ae k (ConicalCommonBaseline.forcing p a center i)
    (ConicalCommonMaterial.source p a center i)
    (fun j => ConicalCommonBaseline.source_integrable p a center i j T hT (ha i))
    (ConicalCommonBaseline.source_ae p a center i) T hσzero (ball (center i) (a i)) isOpen_ball hsource
  have ht := (measurePreserving_add_right (volume : Measure Space) (center i)).quasiMeasurePreserving.ae (he.and hs)
  filter_upwards [ht] with x ht hx
  have hm : x+center i ∈ ball (center i) (a i) := by
    have hx' : x ∈ ball (0 : Space) (a i) := ball_subset_ball hb.le hx
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx'
  have hmem := hR i (ConicalCommonMaterial.material_subset_outer p a center ha i (ball_subset_closedBall hm))
  have hf := ht.1 hmem
  have hg := congrFun (ht.2 hm) j
  rw [hJ j x (ball_subset_closedBall hx)]
  change FieldResponse.electric k (_-_) (fun j y => _-_ ) (x+center i) j + _ = _
  rw [hf, hg]
  change _ - ExteriorContinuity.electric k (fun j y => ConicalSeparatedSource.physicalSource (p i) (a i) j (y-center i)) (x+center i) j + _ = _
  rw [ConicalCommonExteriorTranslation.electric_translate]
  dsimp [ConicalCommonIncidentError.error, ConicalCommonEntire.electric, MaterialField.total,
    MaterialField.scattered, ConicalCommonEntire.polarization, ConicalCommonEntire.source]
  rw [add_comm x (center i)]
  ring

theorem potential_gauss (i : ι) (R T k b : ℝ) (hR0 : 0 ≤ R) (hRT : R ≤ T)
    (hk : k ≠ 0) (hb : b < a i)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (d : Input) (J : Maxwell.Field)
    (hJ : ∀ j x, x ∈ closedBall (0 : Space) b → J x j = ConicalCommonIncidentError.error (p i) (a i) k (center i) d j x)
    (f : 𝓢(Space, ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ ball (0 : Space) b) :
    (∑ j : Fin 3, ∫ x, (ConicalLocalGauss.epsilon (p i) x : ℂ) *
      ((potential p a center B hB hcontrast ha hsep i R T k hRT hR d).derivative j x +
        correction p a center B hB hcontrast ha hsep i R k d J x j) * Maxwell.dcoord f x j) = 0 := by
  have h := ConicalCommonLocal.local_gauss p a center B hB hcontrast ha hsep i b k hb.le (hai i) hk _ _
    (ConicalCommonEntire.maxwell p a center B hB hcontrast ha hsep R k hR0 hfreq hR (FiniteAngularHerglotz.incident k d)) f hf
  have he (j : Fin 3) : (∫ x, (ConicalLocalGauss.epsilon (p i) x : ℂ) *
      ((potential p a center B hB hcontrast ha hsep i R T k hRT hR d).derivative j x +
        correction p a center B hB hcontrast ha hsep i R k d J x j) * Maxwell.dcoord f x j) =
      ∫ x, (ConicalLocalGauss.epsilon (p i) x : ℂ) *
        ConicalCommonEntire.electric p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) (center i+x) j * Maxwell.dcoord f x j := by
    apply integral_congr_ae
    filter_upwards [fixed_electric_ae p a center B hB hcontrast ha hsep i R T k b hRT hb hR hai d J hJ j] with x hx
    by_cases hb' : x ∈ ball (0 : Space) b
    · have ht := hx hb'
      dsimp [potential, ConicalTranslatedPotential.translated, ConicalCompactPotential.potentialData, correction]
      rw [← add_comm x (center i), ← ht]
      ring
    · have hn : x ∉ tsupport (f : Space → ℂ) := fun ht => hb' (hf ht)
      simp [Maxwell.dcoord, fderiv_of_not_mem_tsupport ℝ hn]
  simpa only [he] using h

def system (i : ι) (R T k b : ℝ) (hR0 : 0 ≤ R) (hRT : R ≤ T)
    (hk : k ≠ 0) (hb : b < a i)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (d : Input) (J : Maxwell.Field)
    (hJ : ∀ j, Continuous (fun x => J x j))
    (heJ : ∀ j x, x ∈ closedBall (0 : Space) b → J x j = ConicalCommonIncidentError.error (p i) (a i) k (center i) d j x) :
    ConicalProjectionData.System (p i) b :=
  ConicalProjectionLocalization.ofPotential (p i) b (hb.trans (hai i))
    (potential p a center B hB hcontrast ha hsep i R T k hRT hR d)
    (correction p a center B hB hcontrast ha hsep i R k d J)
    (correction_continuous p a center B hB hcontrast ha hsep i R T k hRT hR d J hJ)
    (potential_gauss p a center B hB hcontrast ha hsep i R T k b hR0 hRT hk hb hfreq hR hai d J heJ)

theorem system_actual (i : ι) (R T k b : ℝ) (hR0 : 0 ≤ R) (hRT : R ≤ T)
    (hk : k ≠ 0) (hb : b < a i)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (d : Input) (J : Maxwell.Field)
    (hJ : ∀ j, Continuous (fun x => J x j))
    (heJ : ∀ j x, x ∈ closedBall (0 : Space) b → J x j = ConicalCommonIncidentError.error (p i) (a i) k (center i) d j x) (j : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      ConicalProjectionData.totalCoordinate (system p a center B hB hcontrast ha hsep i R T k b hR0 hRT hk hb hfreq hR hai d J hJ heJ) j x =
        ConicalCommonEntire.electric p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) (x+center i) j := by
  have ht := ConicalProjectionLocalization.total_inner (p i) b (hb.trans (hai i))
    (potential p a center B hB hcontrast ha hsep i R T k hRT hR d)
    (correction p a center B hB hcontrast ha hsep i R k d J)
    (correction_continuous p a center B hB hcontrast ha hsep i R T k hRT hR d J hJ)
    (potential_gauss p a center B hB hcontrast ha hsep i R T k b hR0 hRT hk hb hfreq hR hai d J heJ) j
  filter_upwards [ht, fixed_electric_ae p a center B hB hcontrast ha hsep i R T k b hRT hb hR hai d J heJ j] with x ht he hx
  dsimp only [system]
  rw [ht hx]
  dsimp [potential, ConicalTranslatedPotential.translated, ConicalCompactPotential.potentialData, correction]
  linear_combination he hx

end OQ14.ConicalCommonFixedGauge
#print axioms OQ14.ConicalCommonFixedGauge.source_ae
#print axioms OQ14.ConicalCommonFixedGauge.source_zero_outer
#print axioms OQ14.ConicalCommonFixedGauge.correction_continuous
#print axioms OQ14.ConicalCommonFixedGauge.exists_extension
#print axioms OQ14.ConicalCommonFixedGauge.fixed_electric_ae
#print axioms OQ14.ConicalCommonFixedGauge.potential_gauss
#print axioms OQ14.ConicalCommonFixedGauge.system
#print axioms OQ14.ConicalCommonFixedGauge.system_actual
