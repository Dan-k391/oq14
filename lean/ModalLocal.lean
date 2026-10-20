import ModalWeak

/-! # Actual local square integrability of the spherical Maxwell fields

The exterior profiles are clipped only to construct continuous majorants and
measurable representatives. The electric and magnetic fields themselves are
the unchanged regular-interior/outgoing-exterior fields.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.ModalLocal

open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ModalWeak
  OQ14.ModalProfiles OQ14.ModalOrigin OQ14.ModalInterface OQ14.ModalDipole
  OQ14.ModalMatching OQ14.ModalAlgebra OQ14.ModalWronskian OQ14.RadialInterface
open scoped Topology Classical

theorem continuous_memLp_compact (f : Space → ℂ) (hf : Continuous f)
    (K : Set Space) (hK : IsCompact K) (p : ENNReal) :
    MemLp f p (volume.restrict K) := by
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC x hx

theorem piecewise_memLp_compact (f g : Space → ℂ) (hf : Continuous f) (hg : Continuous g)
    (s K : Set Space) (hs : MeasurableSet s) (hK : IsCompact K) (p : ENNReal) :
    MemLp (s.piecewise f g) p (volume.restrict K) := by
  have he : s.piecewise f g = s.indicator f + sᶜ.indicator g := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx, Set.piecewise]
  rw [he]
  exact ((continuous_memLp_compact f hf K hK p).indicator hs).add
    ((continuous_memLp_compact g hg K hK p).indicator hs.compl)

theorem radial_mul_memLp_compact (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ioi 0))
    (h : Space → ℂ) (hh : Continuous h) (K : Set Space) (hK : IsCompact K) (p : ENNReal) :
    MemLp (fun x => radial f g x * h x) p (volume.restrict K) := by
  have he : (fun x => radial f g x * h x) =
      {x : Space | ‖x‖ ≤ 1}.piecewise
        (fun x => f ‖x‖ * h x) (fun x => g (max ‖x‖ (1/2)) * h x) := by
    funext x
    by_cases hx : ‖x‖ ≤ 1
    · simp [radial, Set.piecewise, hx]
    · have hr : (1/2 : ℝ) ≤ ‖x‖ := by linarith
      simp only [radial, Set.piecewise, Set.mem_setOf_eq, if_neg hx]
      rw [max_eq_left hr]
  rw [he]
  exact piecewise_memLp_compact _ _ ((radial_profile_continuous f hf).mul hh)
    ((clipped_profile_continuous g hg).mul hh) _ K
    (isClosed_le continuous_norm continuous_const).measurableSet hK p

theorem radial_memLp_compact (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ioi 0))
    (K : Set Space) (hK : IsCompact K) (p : ENNReal) :
    MemLp (radial f g) p (volume.restrict K) := by
  simpa only [mul_one] using
    radial_mul_memLp_compact f g hf hg (fun _ => 1) continuous_const K hK p

theorem outerB_differentiableAt (k b z : ℂ) (hk : k ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ (outerB k b) z := by
  have hx := (xi_hasDerivAt 1 (k*z) (mul_ne_zero hk hz)).differentiableAt.comp z
    (differentiableAt_id.const_mul k)
  have hd := (xiD_hasDerivAt 1 (k*z) (mul_ne_zero hk hz)).differentiableAt.comp z
    (differentiableAt_id.const_mul k)
  exact (((hx.const_mul 2).div (differentiableAt_id.pow 4) (pow_ne_zero _ hz)).sub
    ((hd.const_mul k).div (differentiableAt_id.pow 3) (pow_ne_zero _ hz))).const_mul b

theorem electric_memLp_compact (n k a b : ℂ) (hk : k ≠ 0)
    (K : Set Space) (hK : IsCompact K) (p : ENNReal) (i : Fin 3) :
    MemLp (fun x => electric n k a b x i) p (volume.restrict K) := by
  have hA := radial_memLp_compact _ _ (entire_real_profile _ (innerA_differentiable n k a)).1
    (punctured_real_profile _ (fun z hz => outerA_differentiableAt k b z hk hz)).1 K hK p
  have hB (j : Fin 3) := radial_mul_memLp_compact _ _
    (entire_real_profile _ (innerB_differentiable n k a)).1
    (punctured_real_profile _ (fun z hz => outerB_differentiableAt k b z hk hz)).1
    (fun x => (x 2 : ℂ) * (x j : ℂ))
    ((coordinate 2).continuous.mul (coordinate j).continuous) K hK p
  rw [funext (electric_profiles n k a b)]
  fin_cases i <;> dsimp
  · simpa only [mul_assoc] using hB 0
  · simpa only [mul_assoc] using hB 1
  · simpa only [mul_assoc] using hA.add (hB 2)

theorem magnetic_memLp_compact (n k a b : ℂ) (hk : k ≠ 0)
    (K : Set Space) (hK : IsCompact K) (p : ENNReal) (i : Fin 3) :
    MemLp (fun x => magnetic n k a b x i) p (volume.restrict K) := by
  have hC (j : Fin 3) := radial_mul_memLp_compact _ _
    (entire_real_profile _ (innerC_differentiable n k a)).1
    (punctured_real_profile _ (fun z hz => outerC_differentiableAt k b z hk hz)).1
    (fun x => (x j : ℂ)) (coordinate j).continuous K hK p
  rw [funext (magnetic_profiles n k a b hk)]
  fin_cases i <;> dsimp
  · exact hC 1
  · simpa only [neg_mul] using (hC 0).neg
  · exact MemLp.zero'

theorem displacement_memLp_compact (n k a b : ℂ) (hk : k ≠ 0)
    (K : Set Space) (hK : IsCompact K) (p : ENNReal) (i : Fin 3) :
    MemLp (fun x => coefficient n x * electric n k a b x i) p (volume.restrict K) := by
  let s : Set Space := {x | ‖x‖ ≤ 1}
  have hs : MeasurableSet s := measurableSet_le continuous_norm.measurable measurable_const
  have he : (fun x => coefficient n x * electric n k a b x i) =
      (fun x => n^2 * s.indicator (fun y => electric n k a b y i) x) +
        sᶜ.indicator (fun x => electric n k a b x i) := by
    funext x
    by_cases hx : ‖x‖ ≤ 1 <;> simp [coefficient, s, hx]
  rw [he]
  have hE := electric_memLp_compact n k a b hk K hK p i
  exact ((hE.indicator hs).const_mul (n^2)).add (hE.indicator hs.compl)

theorem memLp_bounded_of_compact (f : Space → ℂ) (p : ENNReal)
    (hf : ∀ K : Set Space, IsCompact K → MemLp f p (volume.restrict K))
    (Ω : Set Space) (hΩ : Bornology.IsBounded Ω) :
    MemLp f p (volume.restrict Ω) := by
  obtain ⟨R, hR⟩ := hΩ.subset_closedBall (0 : Space)
  exact (hf (closedBall 0 R) (isCompact_closedBall 0 R)).mono_measure
    (Measure.restrict_mono hR le_rfl)

theorem electric_memLp_bounded (n k a b : ℂ) (hk : k ≠ 0)
    (Ω : Set Space) (hΩ : Bornology.IsBounded Ω) (p : ENNReal) (i : Fin 3) :
    MemLp (fun x => electric n k a b x i) p (volume.restrict Ω) :=
  memLp_bounded_of_compact _ p (fun K hK => electric_memLp_compact n k a b hk K hK p i) Ω hΩ

theorem magnetic_memLp_bounded (n k a b : ℂ) (hk : k ≠ 0)
    (Ω : Set Space) (hΩ : Bornology.IsBounded Ω) (p : ENNReal) (i : Fin 3) :
    MemLp (fun x => magnetic n k a b x i) p (volume.restrict Ω) :=
  memLp_bounded_of_compact _ p (fun K hK => magnetic_memLp_compact n k a b hk K hK p i) Ω hΩ

theorem displacement_memLp_bounded (n k a b : ℂ) (hk : k ≠ 0)
    (Ω : Set Space) (hΩ : Bornology.IsBounded Ω) (p : ENNReal) (i : Fin 3) :
    MemLp (fun x => coefficient n x * electric n k a b x i) p (volume.restrict Ω) :=
  memLp_bounded_of_compact _ p (fun K hK => displacement_memLp_compact n k a b hk K hK p i) Ω hΩ

end OQ14.ModalLocal

#print axioms OQ14.ModalLocal.continuous_memLp_compact
#print axioms OQ14.ModalLocal.piecewise_memLp_compact
#print axioms OQ14.ModalLocal.radial_mul_memLp_compact
#print axioms OQ14.ModalLocal.radial_memLp_compact
#print axioms OQ14.ModalLocal.outerB_differentiableAt
#print axioms OQ14.ModalLocal.electric_memLp_compact
#print axioms OQ14.ModalLocal.magnetic_memLp_compact
#print axioms OQ14.ModalLocal.displacement_memLp_compact
#print axioms OQ14.ModalLocal.memLp_bounded_of_compact
#print axioms OQ14.ModalLocal.electric_memLp_bounded
#print axioms OQ14.ModalLocal.magnetic_memLp_bounded
#print axioms OQ14.ModalLocal.displacement_memLp_bounded
