import SourceFreeOpenHelmholtz
import ConicalRungeClosure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.UnionFreeRunge
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalRungeAnnihilator
open scoped InnerProductSpace ComplexConjugate Topology
abbrev Space := Maxwell.Space
abbrev Scalar (K : Set Space) := Lp ℂ 2 (volume.restrict K)
abbrev Vector (K : Set Space) := PiLp 2 (fun _ : Fin 3 => Scalar K)
abbrev WaveIndex := AngularPower.Sphere × Fin 3

def density (K : Set Space) (g : Vector K) (j : Fin 3) : Space → ℂ := K.indicator (fun x => conj (g j x))
theorem density_memLp (K : Set Space) (hK : MeasurableSet K) (g : Vector K) (j : Fin 3) : MemLp (density K g j) 2 volume :=
  (memLp_indicator_iff_restrict hK).mpr (Complex.conjCLE.toContinuousLinearMap.comp_memLp (g j))
def scalarExtension (K : Set Space) (hK : MeasurableSet K) (g : Vector K) (j : Fin 3) : FourierL2.ScalarL2 :=
  (density_memLp K hK g j).toLp (density K g j)
def extension (K : Set Space) (hK : MeasurableSet K) (g : Vector K) : VectorFourier.VectorL2 :=
  ∑ j : Fin 3, DynamicConvolution.insert j (scalarExtension K hK g j)
theorem extension_ae (K : Set Space) (hK : MeasurableSet K) (g : Vector K) (j : Fin 3) :
    NewtonL2.physicalCoordinate (extension K hK g) j =ᵐ[volume] density K g j := by
  have he : NewtonL2.physicalCoordinate (extension K hK g) j = scalarExtension K hK g j := by
    change DynamicConvolution.component j (∑ i : Fin 3, DynamicConvolution.insert i (scalarExtension K hK g i))=_
    simp only [map_sum,DynamicConvolution.component_insert]
    simp
  rw [he]
  exact (density_memLp K hK g j).coeFn_toLp

theorem density_integral (K : Set Space) (hK : MeasurableSet K) (g : Vector K) (j : Fin 3) (f : Space → ℂ) :
    (∫ x, f x*density K g j x)=∫ x in K, f x*conj (g j x) := by
  rw [← integral_indicator hK]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ K <;> simp [density,hx]

theorem wave_memLp (k : ℝ) (K : Set Space) [IsFiniteMeasure (volume.restrict K)] (w : WaveIndex) (j : Fin 3) :
    MemLp (ConicalRungeBall.waveValue k (w.1 : Space) w.2 j) 2 (volume.restrict K) := by
  have hc : Continuous (ConicalRungeBall.waveValue k (w.1 : Space) w.2 j) := by
    unfold ConicalRungeBall.waveValue ConicalRungeAnnihilator.phase
    fun_prop
  apply MemLp.of_bound hc.aestronglyMeasurable 2
  filter_upwards with x
  simp only [ConicalRungeBall.waveValue,norm_mul,ConicalRungeBall.phase_norm,one_mul]
  exact DyadicRadiation.transverse_norm_bound (w.1 : Space) w.2 j

def wave (k : ℝ) (K : Set Space) [IsFiniteMeasure (volume.restrict K)] (w : WaveIndex) : Vector K :=
  (WithLp.equiv 2 (Fin 3 → Scalar K)).symm (fun j =>
    (wave_memLp k K w j).toLp (ConicalRungeBall.waveValue k (w.1 : Space) w.2 j))
def waveSpan (k : ℝ) (K : Set Space) [IsFiniteMeasure (volume.restrict K)] : Submodule ℂ (Vector K) :=
  Submodule.span ℂ (range (wave k K))

theorem inner_wave (k : ℝ) (K : Set Space) (hK : MeasurableSet K)
    [IsFiniteMeasure (volume.restrict K)] (w : WaveIndex) (g : Vector K) :
    ⟪g,wave k K w⟫_ℂ = planePair k (density K g) (w.1 : Space) w.2 := by
  rw [PiLp.inner_apply]
  unfold planePair
  apply Finset.sum_congr rfl
  intro j _
  rw [density_integral K hK,← integral_const_mul,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(wave_memLp k K w j).coeFn_toLp] with x hx
  change @inner ℂ ℂ _ (g j x) (((wave_memLp k K w j).toLp (ConicalRungeBall.waveValue k (w.1 : Space) w.2 j)) x) = _
  rw [hx]
  simp only [RCLike.inner_apply,ConicalRungeBall.waveValue]
  ring
theorem target_memLp (k R T : ℝ) (K : Set Space) (hKR : K ⊆ closedBall (0 : Space) R)
    (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j) (j : Fin 3) :
    MemLp (fun x => FieldResponse.electric k G σ x j) 2 (volume.restrict K) :=
  (LocalVolumeResponse.electric_memLp_ball k R T G σ
    (NewtonReciprocity.compact_source_integrable T G σ hcσ hG) hcσ hG j).mono_measure
    (Measure.restrict_mono_set volume hKR)

def target (k R T : ℝ) (K : Set Space) (hKR : K ⊆ closedBall (0 : Space) R)
    (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j) : Vector K :=
  (WithLp.equiv 2 (Fin 3 → Scalar K)).symm (fun j =>
    (target_memLp k R T K hKR G σ hcσ hG j).toLp (fun x => FieldResponse.electric k G σ x j))

theorem inner_target (k R T : ℝ) (K : Set Space) (hK : MeasurableSet K)
    (hKR : K ⊆ closedBall (0 : Space) R) (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j) (g : Vector K) :
    ⟪g,target k R T K hKR G σ hcσ hG⟫_ℂ =
      ∑ j : Fin 3, ∫ x, FieldResponse.electric k G σ x j*density K g j x := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [density_integral K hK,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(target_memLp k R T K hKR G σ hcσ hG j).coeFn_toLp] with x hx
  change @inner ℂ ℂ _ (g j x) (((target_memLp k R T K hKR G σ hcσ hG j).toLp
    (fun x => FieldResponse.electric k G σ x j)) x) = _
  rw [hx]
  simp only [RCLike.inner_apply]

theorem target_closedSpan {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (hsep : ∀ i j, i ≠ j → radius i + radius j < dist (center i) (center j))
    (k : ℝ) (hk : 0 < k) (K : Set Space) (hK : MeasurableSet K)
    (hKeq : K = (DisjointBallGeometry.exterior center radius)ᶜ)
    [IsFiniteMeasure (volume.restrict K)] (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hKR : K ⊆ closedBall (0 : Space) R) (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hiσ : ∀ j x, x ∉ DisjointBallGeometry.exterior center radius → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j) :
    target k R T K hKR G σ hcσ hG ∈ (waveSpan k K).topologicalClosure := by
  haveI : CompleteSpace (Vector K) := by
    change CompleteSpace (Fin 3 → Scalar K)
    infer_instance
  rw [← (waveSpan k K).orthogonal_orthogonal_eq_closure]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro g hg
  have hplane (n : Space) (hn : ‖n‖=1) (i : Fin 3) : planePair k (density K g) n i=0 := by
    let w : WaveIndex := (⟨n, by simpa only [mem_sphere,dist_zero_right] using hn⟩,i)
    rw [← inner_wave k K hK w g]
    apply (Submodule.mem_orthogonal' _ _).mp hg
    exact Submodule.subset_span ⟨w,rfl⟩
  rw [inner_target k R T K hK hKR]
  apply SourceFreeOpenHelmholtz.reciprocal_pair_zero center radius hr hsep k hk R T hR hRT
    (extension K hK g) G (density K g) σ
  · intro j x hx
    exact indicator_of_not_mem (fun hxK => hx (hKR hxK)) _
  · exact hcσ
  · intro j x hx
    apply indicator_of_not_mem
    rw [hKeq]
    exact not_not.mpr hx
  · exact hiσ
  · exact extension_ae K hK g
  · exact hG
  · exact hplane

theorem finite_approximation {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (hsep : ∀ i j, i ≠ j → radius i + radius j < dist (center i) (center j))
    (k : ℝ) (hk : 0 < k) (K : Set Space) (hK : MeasurableSet K)
    (hKeq : K = (DisjointBallGeometry.exterior center radius)ᶜ)
    [IsFiniteMeasure (volume.restrict K)] (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hKR : K ⊆ closedBall (0 : Space) R) (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hiσ : ∀ j x, x ∉ DisjointBallGeometry.exterior center radius → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : WaveIndex →₀ ℂ, ‖(c.sum fun w b => b • wave k K w)-target k R T K hKR G σ hcσ hG‖ < ε := by
  have ht := target_closedSpan center radius hr hsep k hk K hK hKeq R T hR hRT hKR G σ hcσ hiσ hG
  change target k R T K hKR G σ hcσ hG ∈ closure (waveSpan k K : Set (Vector K)) at ht
  obtain ⟨v,hv,hd⟩ := Metric.mem_closure_iff.mp ht ε hε
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  refine ⟨c,?_⟩
  rw [hc]
  simpa only [dist_eq_norm,norm_sub_rev] using hd
def balls {ι : Type*} (center : ι → Space) (radius : ι → ℝ) : Set Space :=
  ⋃ i, closedBall (center i) (radius i)

theorem balls_eq {ι : Type*} (center : ι → Space) (radius : ι → ℝ) :
    balls center radius = (DisjointBallGeometry.exterior center radius)ᶜ := by
  ext x
  simp [balls, DisjointBallGeometry.exterior, mem_closedBall, not_lt]

theorem balls_compact {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ) :
    IsCompact (balls center radius) := isCompact_iUnion (fun i => isCompact_closedBall (center i) (radius i))

instance balls_finite {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ) :
    IsFiniteMeasure (volume.restrict (balls center radius)) :=
  isFiniteMeasure_restrict.mpr (balls_compact center radius).measure_ne_top

theorem finite_union_approximation {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (hsep : ∀ i j, i ≠ j → radius i + radius j < dist (center i) (center j))
    (k : ℝ) (hk : 0 < k) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hKR : balls center radius ⊆ closedBall (0 : Space) R)
    (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hiσ : ∀ j x, x ∈ balls center radius → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : WaveIndex →₀ ℂ, ‖(c.sum fun w b => b • wave k (balls center radius) w)-
      target k R T (balls center radius) hKR G σ hcσ hG‖ < ε := by
  apply finite_approximation center radius hr hsep k hk (balls center radius)
    (balls_compact center radius).measurableSet (balls_eq center radius) R T hR hRT hKR G σ hcσ
  · intro j x hx
    apply hiσ j x
    rw [balls_eq]
    exact hx
  · exact hε

end OQ14.UnionFreeRunge




#print axioms OQ14.UnionFreeRunge.finite_union_approximation


#print axioms OQ14.UnionFreeRunge.density_memLp
#print axioms OQ14.UnionFreeRunge.extension_ae
#print axioms OQ14.UnionFreeRunge.density_integral
#print axioms OQ14.UnionFreeRunge.wave_memLp
#print axioms OQ14.UnionFreeRunge.inner_wave
#print axioms OQ14.UnionFreeRunge.target_memLp
#print axioms OQ14.UnionFreeRunge.inner_target
#print axioms OQ14.UnionFreeRunge.target_closedSpan
#print axioms OQ14.UnionFreeRunge.finite_approximation
#print axioms OQ14.UnionFreeRunge.balls_eq
#print axioms OQ14.UnionFreeRunge.balls_compact
