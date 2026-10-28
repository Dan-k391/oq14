import UnionFiniteAngularRunge
import ConicalMaterialRunge
import CompactCommonMaterial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.UnionMaterialTransfer
open MeasureTheory Set Metric OQ14.Maxwell OQ14.UnionFreeRunge
open scoped Topology
abbrev Space := Maxwell.Space
abbrev VectorL2 := VectorFourier.VectorL2

theorem scalar_memLp (K : Set Space) (hK : MeasurableSet K) (f : Scalar K) :
    MemLp (K.indicator (f : Space → ℂ)) 2 volume :=
  (memLp_indicator_iff_restrict hK).mpr (Lp.memLp f)

def scalarExtension (K : Set Space) (hK : MeasurableSet K) (f : Scalar K) : FourierL2.ScalarL2 :=
  (scalar_memLp K hK f).toLp (K.indicator (f : Space → ℂ))

theorem scalarExtension_ae (K : Set Space) (hK : MeasurableSet K) (f : Scalar K) :
    scalarExtension K hK f =ᵐ[volume] K.indicator (f : Space → ℂ) :=
  (scalar_memLp K hK f).coeFn_toLp

theorem scalarExtension_add (K : Set Space) (hK : MeasurableSet K) (f g : Scalar K) :
    scalarExtension K hK (f+g)=scalarExtension K hK f+scalarExtension K hK g := by
  apply Lp.ext
  have hf := (ae_restrict_iff' hK).mp (Lp.coeFn_add f g)
  filter_upwards [scalarExtension_ae K hK (f+g),scalarExtension_ae K hK f,scalarExtension_ae K hK g,
    Lp.coeFn_add (scalarExtension K hK f) (scalarExtension K hK g),hf] with x hfg he hf hadd hlocal
  rw [hfg,hadd]
  simp only [Pi.add_apply,he,hf]
  by_cases hx : x ∈ K
  · simp only [indicator_of_mem hx]
    exact hlocal hx
  · simp only [indicator_of_not_mem hx,add_zero]

theorem scalarExtension_smul (K : Set Space) (hK : MeasurableSet K) (z : ℂ) (f : Scalar K) :
    scalarExtension K hK (z • f)=z • scalarExtension K hK f := by
  apply Lp.ext
  have hf := (ae_restrict_iff' hK).mp (Lp.coeFn_smul z f)
  filter_upwards [scalarExtension_ae K hK (z • f),scalarExtension_ae K hK f,
    Lp.coeFn_smul z (scalarExtension K hK f),hf] with x hz he hs hlocal
  rw [hz,hs]
  simp only [Pi.smul_apply,smul_eq_mul,he]
  by_cases hx : x ∈ K
  · simp only [indicator_of_mem hx]
    exact hlocal hx
  · simp only [indicator_of_not_mem hx,mul_zero]

theorem scalarExtension_norm (K : Set Space) (hK : MeasurableSet K) (f : Scalar K) :
    ‖scalarExtension K hK f‖=‖f‖ := by
  simp only [Lp.norm_def]
  rw [eLpNorm_congr_ae (scalarExtension_ae K hK f),eLpNorm_indicator_eq_eLpNorm_restrict hK]

def scalar (K : Set Space) (hK : MeasurableSet K) : Scalar K →L[ℂ] FourierL2.ScalarL2 :=
  ({toFun := scalarExtension K hK,map_add' := scalarExtension_add K hK,map_smul' := scalarExtension_smul K hK} :
    Scalar K →ₗ[ℂ] FourierL2.ScalarL2).mkContinuous 1 (fun f => by
      change ‖scalarExtension K hK f‖ ≤ 1*‖f‖
      rw [scalarExtension_norm,one_mul])

def vector (K : Set Space) (hK : MeasurableSet K) : Vector K →L[ℂ] VectorL2 :=
  ∑ j : Fin 3, (DynamicConvolution.insert j).comp
    ((scalar K hK).comp (PiLp.proj 2 (fun _ : Fin 3 => Scalar K) j))

theorem vector_coordinate (K : Set Space) (hK : MeasurableSet K) (g : Vector K) (j : Fin 3) :
    NewtonL2.physicalCoordinate (vector K hK g) j=scalarExtension K hK (g j) := by
  change DynamicConvolution.component j (vector K hK g)=_
  simp only [vector,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum,
    DynamicConvolution.component_insert]
  simp
  rfl

theorem vector_ae (K : Set Space) (hK : MeasurableSet K) (g : Vector K) (j : Fin 3) :
    NewtonL2.physicalCoordinate (vector K hK g) j =ᵐ[volume] K.indicator (fun x => g j x) := by
  rw [vector_coordinate]
  exact scalarExtension_ae K hK (g j)

def weighted (c : StaticCoefficient.Coefficient) (K : Set Space) (hK : MeasurableSet K) : Vector K →L[ℂ] VectorL2 :=
  (StaticCoefficient.sqrtMultiplier c).comp (vector K hK)

theorem weighted_actual (c : StaticCoefficient.Coefficient) (K : Set Space) (hK : MeasurableSet K)
    (g : Vector K) (I : Field)
    (hc : ∀ x : Space, x ∉ K → c.value (VectorFourier.coordinateMap x)=0)
    (hg : ∀ j, (g j : Space → ℂ) =ᵐ[volume.restrict K] fun x => I x j) (j : Fin 3) :
    (fun x => weighted c K hK g (VectorFourier.coordinateMap x) j) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*I x j := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c (vector K hK g))
  have hl := (ae_restrict_iff' hK).mp (hg j)
  filter_upwards [hs,NewtonL2.physicalCoordinate_ae (vector K hK g) j,
    vector_ae K hK g j,hl] with x hs hp he hl
  change StaticCoefficient.sqrtMultiplier c (vector K hK g) (VectorFourier.coordinateMap x) j=_
  rw [hs]
  change (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*
    vector K hK g (VectorFourier.coordinateMap x) j=_
  rw [← hp,he]
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx,hl hx]
  · rw [hc x hx]
    simp

def solutionOperator (c : StaticCoefficient.Coefficient) (k R : ℝ) (K : Set Space) (hK : MeasurableSet K) :
    Vector K →L[ℂ] VectorL2 :=
  (Ring.inverse (DynamicVolume.volumeBlock c k R)).comp (weighted c K hK)

theorem solution_equation (c : StaticCoefficient.Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius c R) (K : Set Space) (hK : MeasurableSet K) (g : Vector K) :
    DynamicVolume.volumeBlock c k R (solutionOperator c k R K hK g)=weighted c K hK g :=
  MaterialField.solution_equation c k R hR (by
    have he := DynamicStaticLimit.error_small c k R hk
    linarith) _

theorem solution_lipschitz (c : StaticCoefficient.Coefficient) (k R : ℝ) (K : Set Space) (hK : MeasurableSet K)
    (g h : Vector K) : ‖solutionOperator c k R K hK g-solutionOperator c k R K hK h‖ ≤
      ‖solutionOperator c k R K hK‖ * ‖g-h‖ := by
  rw [← map_sub]
  exact (solutionOperator c k R K hK).le_opNorm (g-h)

theorem finite_angular_solution_approximation {ι : Type*} [Fintype ι]
    (center : ι → Space) (radius : ι → ℝ) (hr : ∀ i, 0 ≤ radius i)
    (hsep : ∀ i j, i ≠ j → radius i + radius j < dist (center i) (center j))
    (c : StaticCoefficient.Coefficient) (k : ℝ) (hk : 0 < k) (R T : ℝ)
    (hR : 0 ≤ R) (hRT : R ≤ T)
    (hKR : balls center radius ⊆ closedBall (0 : Space) R)
    (G : VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hiσ : ∀ j x, x ∈ balls center radius → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ComplexTransverseExpansion.ModeIndex →₀ ℂ,
      ‖solutionOperator c k R (balls center radius) (balls_compact center radius).measurableSet
        (UnionFiniteAngularRunge.incident k R (balls center radius) hKR d) -
       solutionOperator c k R (balls center radius) (balls_compact center radius).measurableSet
        (target k R T (balls center radius) hKR G σ hcσ hG)‖ < ε := by
  let A := solutionOperator c k R (balls center radius) (balls_compact center radius).measurableSet
  let δ := ε / (‖A‖+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨d,hd⟩ := UnionFiniteAngularRunge.approximation center radius hr hsep k hk R T hR hRT hKR G σ hcσ hiσ hG δ hδ
  refine ⟨d,?_⟩
  have hbound := solution_lipschitz c k R (balls center radius) (balls_compact center radius).measurableSet
    (UnionFiniteAngularRunge.incident k R (balls center radius) hKR d)
    (target k R T (balls center radius) hKR G σ hcσ hG)
  change ‖A _ - A _‖ ≤ ‖A‖ * ‖_ - _‖ at hbound
  apply hbound.trans_lt
  have hn : 0 ≤ ‖A‖ := norm_nonneg _
  have hmul : ‖A‖ * ‖UnionFiniteAngularRunge.incident k R (balls center radius) hKR d -
      target k R T (balls center radius) hKR G σ hcσ hG‖ ≤ ‖A‖*δ := mul_le_mul_of_nonneg_left hd.le hn
  have hkey : (‖A‖+1)*δ=ε := by dsimp [δ]; field_simp
  nlinarith
theorem common_support_union {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ConicalStaticVolume.Data) (a : ι → ℝ) (center : ι → Space)
    (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
    (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
      (ConicalCommonMaterial.outer p center j)) (x : Space) (hx : x ∉ balls center a) :
    (ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep).value
      (VectorFourier.coordinateMap x) = 0 := by
  rw [ConicalCommonMaterial.coefficient_spatial]
  apply Finset.sum_eq_zero
  intro i _
  apply ConicalCommonMaterial.localValue_zero
  intro hi
  exact hx (mem_iUnion.mpr ⟨i,hi⟩)
theorem weighted_eq_global (c : StaticCoefficient.Coefficient) (K : Set Space) (hK : MeasurableSet K)
    (g : Vector K) (F : VectorL2)
    (hc : ∀ x : Space, x ∉ K → c.value (VectorFourier.coordinateMap x)=0)
    (hg : ∀ j, (g j : Space → ℂ) =ᵐ[volume.restrict K]
      (NewtonL2.physicalCoordinate F j : Space → ℂ)) :
    weighted c K hK g = StaticCoefficient.sqrtMultiplier c F := by
  apply StaticSphereMaterial.vector_ext_physical
  intro j
  have h := weighted_actual c K hK g (fun x j => NewtonL2.physicalCoordinate F j x) hc hg j
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (StaticCoefficient.sqrtMultiplier_ae c F)
  filter_upwards [h,hs,NewtonL2.physicalCoordinate_ae F j] with x h hs hp
  rw [h,hs]
  simpa only [PiLp.smul_apply, smul_eq_mul] using congrArg (fun z : ℂ => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*z) hp
end OQ14.UnionMaterialTransfer
#print axioms OQ14.UnionMaterialTransfer.scalarExtension_norm
#print axioms OQ14.UnionMaterialTransfer.vector_ae
#print axioms OQ14.UnionMaterialTransfer.weighted_actual
#print axioms OQ14.UnionMaterialTransfer.solution_equation
#print axioms OQ14.UnionMaterialTransfer.solution_lipschitz

#print axioms OQ14.UnionMaterialTransfer.finite_angular_solution_approximation


#print axioms OQ14.UnionMaterialTransfer.common_support_union


#print axioms OQ14.UnionMaterialTransfer.weighted_eq_global


#print axioms OQ14.UnionMaterialTransfer.scalar_memLp
#print axioms OQ14.UnionMaterialTransfer.scalarExtension_ae
#print axioms OQ14.UnionMaterialTransfer.scalarExtension_add
#print axioms OQ14.UnionMaterialTransfer.scalarExtension_smul
#print axioms OQ14.UnionMaterialTransfer.vector_coordinate
