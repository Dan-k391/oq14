import FinitePlaneDipole

/-! Actual inverse static plane fields compared with exact finite dipole profiles. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.StaticPlaneDipoleError

open MeasureTheory Metric StaticPlaneKernel NewtonSeparatedResponse
open scoped Topology BigOperators

abbrev Vector := StaticBallNewton.Vector
abbrev VectorL2 := VectorFourier.VectorL2

theorem field_congr_ae (f g : Space → ℂ) (hfg : f =ᵐ[volume] g) (i j : Fin 3) :
    StaticPlaneSource.field f i j=StaticPlaneSource.field g i j := by
  funext q
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trial_profile (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (d : ℝ)
    (hr : ∀ l, 0 < r l) (hd : 0 < d) (hh : ∀ l, d+r l ≤ |p l 2|)
    (q : PlaneInverseCube.Plane) (i : Fin 3) :
    (∑ j, StaticPlaneSource.field
      (fun y => FiniteSphereStatic.sumSource p r P (VectorFourier.coordinateMap y) j) i j q)=
      FinitePlaneDipole.dipoles p r P (MaxwellPlaneTail.planePoint q) i := by
  calc
    _ = ∑ j, StaticPlaneSource.field (FinitePlaneDipole.source p r P j) i j q := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrFun (field_congr_ae _ _ (FinitePlaneDipole.source_ae p r P j).symm i j) q
    _ = _ := by
      rw [← response_plane]
      exact FinitePlaneDipole.plane_response_eq_dipoles p r P d hr hd hh q i

omit [Fintype ι] [DecidableEq ι] in
theorem material_representative (p : ι → Space) (r : ι → ℝ) (χ gap : ℝ)
    (hχ : 0 ≤ χ) (hgap : 0 < gap) (hh : ∀ l, gap+r l ≤ |p l 2|)
    (s : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p r χ hχ))
    (u : VectorL2) (i : Fin 3) :
    ContinuousOn (fun x => response
      (DynamicVolume.source (FiniteSphereStatic.coefficient p r χ hχ) u) x i) (strip gap) ∧
    (∀ᵐ x : Space, x ∈ strip gap →
      NewtonL2.physicalCoordinate (StaticNewton.response (FiniteSphereStatic.coefficient p r χ hχ) u) i x=
        response (DynamicVolume.source (FiniteSphereStatic.coefficient p r χ hχ) u) x i) := by
  let c := FiniteSphereStatic.coefficient p r χ hχ
  have hρ : ∀ j, Integrable (DynamicVolume.source c u j) :=
    fun j => DynamicVolume.source_integrable c u s.radius s.ballZero j
  have hh' := StaticPlaneInclusions.material_gap p r χ gap hχ hh u
  refine ⟨response_continuousOn _ hρ gap hgap hh' i, ?_⟩
  exact newton_ae_response (StaticCoefficient.sqrtMultiplier c u) _ hρ
    (StaticNewton.material_source_ae c u) gap s.radius hgap
    (fun j y hy => DynamicVolume.source_zero c u s.radius s.ballZero j y hy) hh' i

theorem inverse_from_estimates (p : ι → Space) (ρ a χ δ R k b A M γ : ℝ)
    (hρ : 0 < ρ) (ha : 0 < a) (hχ : 0 ≤ χ) (hγ : 0 < γ)
    (hh : ∀ l, (γ+ρ)*a ≤ |p l 2|)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
    (f : VectorL2) (E : ι → Vector)
    (he : FiniteSphereAsymptotics.Estimates p ρ a χ δ R k b A M hχ d f E)
    (i : Fin 3) :
    Integrable (fun q : PlaneInverseCube.Plane =>
      response (DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
        (ParityMaterialField.solution d k (b/a) f)) (MaxwellPlaneTail.planePoint q) i-
      FinitePlaneDipole.dipoles p (fun _ => ρ*a)
        (fun l => StaticSpherePolarization.polarization χ (E l)) (MaxwellPlaneTail.planePoint q) i) ∧
    (∫ q : PlaneInverseCube.Plane, ‖response
      (DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
        (ParityMaterialField.solution d k (b/a) f)) (MaxwellPlaneTail.planePoint q) i-
      FinitePlaneDipole.dipoles p (fun _ => ρ*a)
        (fun l => StaticSpherePolarization.polarization χ (E l)) (MaxwellPlaneTail.planePoint q) i‖) ≤
      (3*StaticPlaneInclusions.errorConstant (ι := ι) χ ρ δ k R b A M γ)*a^2 := by
  let c := FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ
  let u := ParityMaterialField.solution d k (b/a) f
  let P := fun l => StaticSpherePolarization.polarization χ (E l)
  let g := fun j y => FiniteSphereStatic.sumSource p (fun _ => ρ*a) P (VectorFourier.coordinateMap y) j
  let D := fun j q => StaticPlaneSource.field (DynamicVolume.source c u j) i j q-
    StaticPlaneSource.field (g j) i j q
  have hh' : ∀ l, γ*a+ρ*a ≤ |p l 2| := by intro l; simpa only [add_mul] using hh l
  have hi (j : Fin 3) : Integrable (D j) :=
    StaticPlaneError.difference_integrable (γ*a) (mul_pos hγ ha) _ _
      (DynamicVolume.source_integrable c u d.radius d.ballZero j)
      (FiniteSphereReaction.source_integrable p (fun _ => ρ*a) P j)
      (Filter.Eventually.of_forall (StaticPlaneInclusions.material_gap p (fun _ => ρ*a) χ (γ*a) hχ hh' u j))
      (StaticPlaneInclusions.trial_gap p (fun _ => ρ*a) P (γ*a) hh' j) i j
  have hq (q : PlaneInverseCube.Plane) :
      response (DynamicVolume.source c u) (MaxwellPlaneTail.planePoint q) i-
        FinitePlaneDipole.dipoles p (fun _ => ρ*a) P (MaxwellPlaneTail.planePoint q) i=
          ∑ j : Fin 3, D j q := by
    rw [response_plane, ← trial_profile p (fun _ => ρ*a) P (γ*a)
      (fun _ => mul_pos hρ ha) (mul_pos hγ ha) hh' q i]
    exact (Finset.sum_sub_distrib).symm
  have heq : (fun q : PlaneInverseCube.Plane =>
      response (DynamicVolume.source c u) (MaxwellPlaneTail.planePoint q) i-
        FinitePlaneDipole.dipoles p (fun _ => ρ*a) P (MaxwellPlaneTail.planePoint q) i)=
          fun q => ∑ j : Fin 3, D j q := funext hq
  change Integrable (fun q => response (DynamicVolume.source c u) (MaxwellPlaneTail.planePoint q) i-
      FinitePlaneDipole.dipoles p (fun _ => ρ*a) P (MaxwellPlaneTail.planePoint q) i) ∧ _
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact integrable_finset_sum _ (fun j _ => hi j)
  calc
    _ = ∫ q : PlaneInverseCube.Plane, ‖∑ j : Fin 3, D j q‖ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun q => congrArg norm (hq q)))
    _ ≤ ∫ q : PlaneInverseCube.Plane, ∑ j : Fin 3, ‖D j q‖ :=
      integral_mono_ae (integrable_finset_sum _ (fun j _ => hi j)).norm
        (integrable_finset_sum _ (fun j _ => (hi j).norm))
        (Filter.Eventually.of_forall (fun q => norm_sum_le _ _))
    _ = ∑ j : Fin 3, ∫ q : PlaneInverseCube.Plane, ‖D j q‖ :=
      integral_finset_sum _ (fun j _ => (hi j).norm)
    _ ≤ ∑ _j : Fin 3, StaticPlaneInclusions.errorConstant (ι := ι) χ ρ δ k R b A M γ*a^2 :=
      Finset.sum_le_sum (fun j _ => StaticPlaneInclusions.inverse_from_estimates p ρ a χ δ R k b A M γ
        ha hχ hγ hh d f E he i j)
    _ = _ := by simp only [Fin.sum_univ_three]; ring

def PlaneEstimates (p : ι → Space) (ρ a χ δ R k b A M γ : ℝ) (hχ : 0 ≤ χ)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
    (f : VectorL2) (E : ι → Vector) : Prop :=
  ∀ i : Fin 3,
    (ContinuousOn (fun x => response
      (DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
        (ParityMaterialField.solution d k (b/a) f)) x i) (strip (γ*a)) ∧
    (∀ᵐ x : Space, x ∈ strip (γ*a) →
      NewtonL2.physicalCoordinate (StaticNewton.response
        (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
          (ParityMaterialField.solution d k (b/a) f)) i x=
        response (DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
          (ParityMaterialField.solution d k (b/a) f)) x i)) ∧
    Integrable (fun q : PlaneInverseCube.Plane =>
      response (DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
        (ParityMaterialField.solution d k (b/a) f)) (MaxwellPlaneTail.planePoint q) i-
      FinitePlaneDipole.dipoles p (fun _ => ρ*a)
        (fun l => StaticSpherePolarization.polarization χ (E l)) (MaxwellPlaneTail.planePoint q) i) ∧
    (∫ q : PlaneInverseCube.Plane, ‖response
      (DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
        (ParityMaterialField.solution d k (b/a) f)) (MaxwellPlaneTail.planePoint q) i-
      FinitePlaneDipole.dipoles p (fun _ => ρ*a)
        (fun l => StaticSpherePolarization.polarization χ (E l)) (MaxwellPlaneTail.planePoint q) i‖) ≤
      (3*StaticPlaneInclusions.errorConstant (ι := ι) χ ρ δ k R b A M γ)*a^2

theorem finite_sphere_family (p : ℝ → ι → Space) (ρ χ δ R k b A M γ : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hδ : 0 < δ) (hb : b ≠ 0) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hγ : 0 < γ)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ l n, l ≠ n → δ ≤ dist (p a l) (p a n))
    (hinside : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (hheight : ∀ a, 0 < a → a ≤ 1 → ∀ l, (γ+ρ)*a ≤ |p a l 2|)
    (f : ℝ → VectorL2) (incident : ℝ → Maxwell.Field) (E : ℝ → ι → Vector)
    (hE : ∀ a, 0 < a → a ≤ 1 → ∀ l j, E a l j = incident a (p a l) j)
    (hcenter : ∀ a, 0 < a → a ≤ 1 → ∀ l j, ‖E a l j‖ ≤ A/a)
    (hincident : ∀ a, 0 < a → a ≤ 1 → ∀ j : Fin 3,
      (fun x => f a (VectorFourier.coordinateMap x) j) =ᵐ[volume]
        fun x => (Real.sqrt ((FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ).value
          (VectorFourier.coordinateMap x)) : ℂ)*incident a x j)
    (hdiff : ∀ a, 0 < a → a ≤ 1 → ∀ l j, ∀ x ∈ ball (p a l) (ρ*a),
      DifferentiableAt ℝ (fun y => incident a y j) x)
    (hder : ∀ a, 0 < a → a ≤ 1 → ∀ l j, ∀ x ∈ ball (p a l) (ρ*a),
      ‖fderiv ℝ (fun y => incident a y j) x‖ ≤ M/a) :
    ∃ η > 0, ∀ a : ℝ, 0 < a → a < η →
      ∃ d : BoundedMaterialKernel.SupportData
          (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ),
        d.radius = R ∧ d.carrier = (⋃ l, ball (p a l) (ρ*a)) ∧
          FiniteSphereAsymptotics.Estimates (p a) ρ a χ δ R k b A M hχ d (f a) (E a) ∧
          PlaneEstimates (p a) ρ a χ δ R k b A M γ hχ d (f a) (E a) := by
  obtain ⟨η, hη, hh⟩ := FiniteSphereAsymptotics.finite_sphere_family p ρ χ δ R k b A M
    hρ hχ hδ hb hA hM hsep hinside f incident E hE hcenter hincident hdiff hder
  refine ⟨min η 1, lt_min hη zero_lt_one, ?_⟩
  intro a ha had
  have ha1 : a ≤ 1 := (had.trans_le (min_le_right _ _)).le
  obtain ⟨d, hdr, hdc, he⟩ := hh a ha (had.trans_le (min_le_left _ _))
  refine ⟨d, hdr, hdc, he, ?_⟩
  intro i
  refine ⟨?_, inverse_from_estimates (p a) ρ a χ δ R k b A M γ hρ ha hχ hγ
    (hheight a ha ha1) d (f a) (E a) he i⟩
  apply material_representative (p a) (fun _ => ρ*a) χ (γ*a) hχ (mul_pos hγ ha) _ d
    (ParityMaterialField.solution d k (b/a) (f a)) i
  intro l
  simpa only [add_mul] using hheight a ha ha1 l

end OQ14.StaticPlaneDipoleError

#print axioms OQ14.StaticPlaneDipoleError.field_congr_ae
#print axioms OQ14.StaticPlaneDipoleError.trial_profile
#print axioms OQ14.StaticPlaneDipoleError.material_representative
#print axioms OQ14.StaticPlaneDipoleError.inverse_from_estimates
#print axioms OQ14.StaticPlaneDipoleError.finite_sphere_family
