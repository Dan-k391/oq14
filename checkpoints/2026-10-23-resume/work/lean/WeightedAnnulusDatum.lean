import IncidentLocalization
import OutgoingFreeDyadic

/-! Weighted-only material data from actual continuous fields on a compact annulus. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.WeightedAnnulusDatum
open MeasureTheory Set Metric Filter OQ14.Maxwell
attribute [local instance] Classical.propDecidable
open scoped Topology

abbrev Coefficient := StaticCoefficient.Coefficient

def annulus (R X : ℝ) : Set Space := closedBall 0 X \ ball 0 R

theorem annulus_compact (R X : ℝ) : IsCompact (annulus R X) :=
  (isCompact_closedBall 0 X).diff isOpen_ball

instance (R X : ℝ) : CompactSpace (annulus R X) := isCompact_iff_compactSpace.mp (annulus_compact R X)

def extension (R X : ℝ) (f : C(annulus R X,ℂ)) (x : Space) : ℂ :=
  if hx : x∈annulus R X then f ⟨x,hx⟩ else 0

theorem extension_measurable (R X : ℝ) (f : C(annulus R X,ℂ)) : Measurable (extension R X f) :=
  f.continuous.measurable.dite measurable_const (annulus_compact R X).measurableSet

def weighted (c : Coefficient) (R X : ℝ) (f : C(annulus R X,ℂ)) (x : Space) : ℂ :=
  (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*extension R X f x

theorem weighted_measurable (c : Coefficient) (R X : ℝ) (f : C(annulus R X,ℂ)) :
    Measurable (weighted c R X f) :=
  (Complex.continuous_ofReal.measurable.comp (Real.continuous_sqrt.measurable.comp
    (c.measurable.comp VectorFourier.coordinateMap_preserving.measurable))).mul (extension_measurable R X f)

theorem weighted_bound (c : Coefficient) (R X : ℝ) (f : C(annulus R X,ℂ)) (x : Space) :
    ‖weighted c R X f x‖≤Real.sqrt c.bound*‖f‖ := by
  by_cases hx : x∈annulus R X
  · simp only [weighted,extension,dif_pos hx,norm_mul]
    exact mul_le_mul (StaticCoefficient.sqrt_value_bound c _) (f.norm_coe_le_norm ⟨x,hx⟩)
      (norm_nonneg _) (Real.sqrt_nonneg _)
  · simp only [weighted,extension,dif_neg hx,mul_zero,norm_zero]
    positivity

theorem weighted_memLp (c : Coefficient) (R X : ℝ) (f : C(annulus R X,ℂ)) :
    MemLp (weighted c R X f) 2 volume := by
  have hs : HasCompactSupport (weighted c R X f) := by
    apply HasCompactSupport.intro' (annulus_compact R X) (annulus_compact R X).isClosed
    intro x hx
    simp only [weighted,extension,dif_neg hx,mul_zero]
  exact hs.memLp_of_bound (weighted_measurable c R X f).aestronglyMeasurable _
    (Eventually.of_forall (weighted_bound c R X f))

def scalar (c : Coefficient) (R X : ℝ) (f : C(annulus R X,ℂ)) : FourierL2.ScalarL2 :=
  (weighted_memLp c R X f).toLp (weighted c R X f)

theorem scalar_ae (c : Coefficient) (R X : ℝ) (f : C(annulus R X,ℂ)) :
    (scalar c R X f : Space → ℂ)=ᵐ[volume] weighted c R X f :=
  (weighted_memLp c R X f).coeFn_toLp

def reference (R X : ℝ) : FourierL2.ScalarL2 :=
  indicatorConstLp 2 (annulus_compact R X).measurableSet (annulus_compact R X).measure_lt_top.ne (1 : ℂ)

theorem scalar_norm (c : Coefficient) (R X : ℝ) (f : C(annulus R X,ℂ)) :
    ‖scalar c R X f‖≤(Real.sqrt c.bound*‖reference R X‖)*‖f‖ := by
  have h : ‖scalar c R X f‖≤(Real.sqrt c.bound*‖f‖)*‖reference R X‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [scalar_ae c R X f,
      (indicatorConstLp_coeFn (p := 2) (hs := (annulus_compact R X).measurableSet)
        (hμs := (annulus_compact R X).measure_lt_top.ne) (c := (1 : ℂ)))] with x hx href
    change reference R X x=(annulus R X).indicator (fun _ => (1 : ℂ)) x at href
    rw [hx,href]
    by_cases ha : x∈annulus R X
    · simp only [Set.indicator_of_mem ha,norm_one,mul_one]
      exact weighted_bound c R X f x
    · simp only [Set.indicator_of_not_mem ha,norm_zero,mul_zero,weighted,extension,dif_neg ha,le_refl]
  exact h.trans_eq (by ring)

def scalarLinear (c : Coefficient) (R X : ℝ) : C(annulus R X,ℂ) →ₗ[ℂ] FourierL2.ScalarL2 where
  toFun := scalar c R X
  map_add' f g := by
    apply Lp.ext
    filter_upwards [scalar_ae c R X (f+g),scalar_ae c R X f,scalar_ae c R X g,
      Lp.coeFn_add (scalar c R X f) (scalar c R X g)] with x hfg hf hg ha
    rw [hfg,ha]
    simp only [Pi.add_apply]
    rw [hf,hg]
    dsimp [weighted,extension]
    split_ifs <;> simp [mul_add]
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [scalar_ae c R X (z • f),scalar_ae c R X f,
      Lp.coeFn_smul z (scalar c R X f)] with x hzf hf hz
    change scalar c R X (z • f) x=(z • scalar c R X f) x
    rw [hzf,hz]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hf]
    dsimp [weighted,extension]
    split_ifs <;> simp [mul_left_comm]

def scalarMap (c : Coefficient) (R X : ℝ) : C(annulus R X,ℂ) →L[ℂ] FourierL2.ScalarL2 :=
  (scalarLinear c R X).mkContinuous (Real.sqrt c.bound*‖reference R X‖) (scalar_norm c R X)

theorem scalarMap_actual (c : Coefficient) (R X : ℝ) (f : C(annulus R X,ℂ))
    (incident : Space → ℂ) (hi : ∀ x : annulus R X,f x=incident x)
    (hc : ∀ x : Space,x∉annulus R X → c.value (VectorFourier.coordinateMap x)=0) :
    (scalarMap c R X f : Space → ℂ)=ᵐ[volume]
      (fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*incident x) := by
  filter_upwards [scalar_ae c R X f] with x hx
  rw [show scalarMap c R X f x=scalar c R X f x from rfl,hx]
  by_cases ha : x∈annulus R X
  · simp only [weighted,extension,dif_pos ha,hi ⟨x,ha⟩]
  · simp only [weighted,extension,dif_neg ha,hc x ha,Real.sqrt_zero,Complex.ofReal_zero,mul_zero,zero_mul]

end OQ14.WeightedAnnulusDatum


#print axioms OQ14.WeightedAnnulusDatum.annulus_compact
#print axioms OQ14.WeightedAnnulusDatum.extension_measurable
#print axioms OQ14.WeightedAnnulusDatum.weighted_measurable
#print axioms OQ14.WeightedAnnulusDatum.weighted_bound
#print axioms OQ14.WeightedAnnulusDatum.weighted_memLp
#print axioms OQ14.WeightedAnnulusDatum.scalar_ae
#print axioms OQ14.WeightedAnnulusDatum.scalar_norm
#print axioms OQ14.WeightedAnnulusDatum.scalarMap_actual
