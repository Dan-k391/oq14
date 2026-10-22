import PlaneMaxwellSharp

/-! Actual finite-sum Maxwell field disk masses and source differences. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PlaneMaxwellFields
open MeasureTheory Metric Set StaticPlaneKernel PlaneSourceKernel MaxwellRadiation
open PlaneInverseCube (diskConstant)
open scoped Topology

private theorem geometry (R d : ℝ) (ρ : Source) (hρ : Admissible R d ρ) (j : Fin 3) :
    ∀ᵐ y, ρ j y ≠ 0 → ‖y‖ ≤ R ∧ d ≤ |y 2| := by
  filter_upwards with y hy
  have h := source_mem_region R d ρ hρ j y hy
  exact ⟨by simpa only [mem_closedBall, dist_zero_right] using h.1, h.2⟩

private theorem sum_mass (f : Fin 3 → Plane → ℂ) (T C : ℝ) (m : Fin 3 → ℝ)
    (hi : ∀ j, IntegrableOn (f j) (closedBall 0 T))
    (hb : ∀ j, (∫ q : Plane in closedBall 0 T, ‖f j q‖) ≤ C*m j) :
    IntegrableOn (fun q => ∑ j, f j q) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖∑ j, f j q‖) ≤ C*(∑ j, m j) := by
  refine ⟨integrable_finset_sum Finset.univ (fun j _ => hi j), ?_⟩
  calc
    _ ≤ ∫ q : Plane in closedBall 0 T, ∑ j, ‖f j q‖ :=
      integral_mono_ae (integrable_finset_sum Finset.univ (fun j _ => hi j)).norm
        (integrable_finset_sum Finset.univ (fun j _ => (hi j).norm))
        (Filter.Eventually.of_forall (fun q => norm_sum_le _ _))
    _ = ∑ j, ∫ q : Plane in closedBall 0 T, ‖f j q‖ :=
      integral_finset_sum _ (fun j _ => (hi j).norm)
    _ ≤ ∑ j, C*m j := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem electric_mass (k R T d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (i : Fin 3) :
    IntegrableOn (fun q : Plane => ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q) i)
      (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q) i‖) ≤
      (PlaneMaxwellLocal.electricCoefficient k R T*((Real.pi+diskConstant)/d))*sourceMass ρ := by
  exact sum_mass _ T _ _
    (fun j => (PlaneMaxwellLocal.electric_entry_mass k R T d hd (ρ j) (hρ.integrable j)
      (geometry R d ρ hρ j) i j).1)
    (fun j => (PlaneMaxwellLocal.electric_entry_mass k R T d hd (ρ j) (hρ.integrable j)
      (geometry R d ρ hρ j) i j).2)

theorem remainder_mass (k R T d : ℝ) (hd : 0 < d) (hdM : d ≤ T+R) (ρ : Source)
    (hρ : Admissible R d ρ) (i : Fin 3) :
    IntegrableOn (fun q : Plane => ∑ j, KernelConvolution.response
      (fun z => DyadicKernel.remainder k z i j) (ρ j) (MaxwellPlaneTail.planePoint q)) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖∑ j, KernelConvolution.response
      (fun z => DyadicKernel.remainder k z i j) (ρ j) (MaxwellPlaneTail.planePoint q)‖) ≤
      PlaneMaxwellSharp.remainderMass k R T*sourceMass ρ := by
  exact sum_mass _ T _ _
    (fun j => (PlaneMaxwellSharp.remainder_response_mass k R T d hd hdM (ρ j) (hρ.integrable j)
      (geometry R d ρ hρ j) i j).1)
    (fun j => (PlaneMaxwellSharp.remainder_response_mass k R T d hd hdM (ρ j) (hρ.integrable j)
      (geometry R d ρ hρ j) i j).2)

theorem magnetic_mass (k R T d : ℝ) (hd : 0 < d) (hdM : d ≤ T+R) (ρ : Source)
    (hρ : Admissible R d ρ) (i : Fin 3) :
    IntegrableOn (fun q : Plane => MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q) i)
      (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q) i‖) ≤
      (2 * |k| * PlaneMaxwellSharp.gradientMass k R T d)*sourceMass ρ := by
  have hg (a b : Fin 3) := PlaneMaxwellSharp.gradient_response_mass k R T d hd hdM
    (ρ b) (hρ.integrable b) (geometry R d ρ hρ b) a
  have hC : 0 ≤ PlaneMaxwellSharp.gradientMass k R T d := by
    have hl : 0 ≤ Real.log ((T+R)/d) := Real.log_nonneg ((one_le_div hd).mpr hdM)
    have hD : 0 ≤ diskConstant := by unfold diskConstant; positivity
    unfold PlaneMaxwellSharp.gradientMass
    have hM : 0 ≤ T+R := (hd.trans_le hdM).le
    positivity
  let f := fun q : Plane => KernelConvolution.response
    (fun z => GreenKernel.phiGradient k z (WeakCurl.next i)) (ρ (WeakCurl.previous i)) (MaxwellPlaneTail.planePoint q)
  let g := fun q : Plane => KernelConvolution.response
    (fun z => GreenKernel.phiGradient k z (WeakCurl.previous i)) (ρ (WeakCurl.next i)) (MaxwellPlaneTail.planePoint q)
  have hf : IntegrableOn f (closedBall 0 T) := (hg _ _).1
  have hh : IntegrableOn g (closedBall 0 T) := (hg _ _).1
  refine ⟨(hf.sub hh).const_mul _, ?_⟩
  calc
    _ = |k| * (∫ q : Plane in closedBall 0 T, ‖f q-g q‖) := by
      simp only [MagneticResponse.magnetic, norm_mul, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, integral_const_mul, f, g]
    _ ≤ |k| * ((∫ q : Plane in closedBall 0 T, ‖f q‖)+(∫ q : Plane in closedBall 0 T, ‖g q‖)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg k)
      rw [← integral_add hf.norm hh.norm]
      exact integral_mono_ae (hf.sub hh).norm (hf.norm.add hh.norm)
        (Filter.Eventually.of_forall (fun q => norm_sub_le _ _))
    _ ≤ |k| * (PlaneMaxwellSharp.gradientMass k R T d*sourceMass ρ+
        PlaneMaxwellSharp.gradientMass k R T d*sourceMass ρ) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg k)
      exact add_le_add ((hg _ _).2.trans (mul_le_mul_of_nonneg_left (component_mass_le ρ _) hC))
        ((hg _ _).2.trans (mul_le_mul_of_nonneg_left (component_mass_le ρ _) hC))
    _ = _ := by ring

theorem electric_sub_mass (k R T d : ℝ) (hd : 0 < d) (ρ σ : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) (i : Fin 3) :
    IntegrableOn (fun q : Plane => ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q) i-
      ExteriorContinuity.electric k σ (MaxwellPlaneTail.planePoint q) i) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q) i-
      ExteriorContinuity.electric k σ (MaxwellPlaneTail.planePoint q) i‖) ≤
      (PlaneMaxwellLocal.electricCoefficient k R T*((Real.pi+diskConstant)/d))*sourceMass (ρ-σ) := by
  have he : (fun q : Plane => ExteriorContinuity.electric k (ρ-σ) (MaxwellPlaneTail.planePoint q) i) =
      (fun q : Plane => ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q) i-
        ExteriorContinuity.electric k σ (MaxwellPlaneTail.planePoint q) i) := by
    funext q
    exact congrFun (electric_plane_sub k R d hd ρ σ hρ hσ q) i
  have he' (q : Plane) := congrFun he q
  simpa only [he, he'] using electric_mass k R T d hd (ρ-σ) (admissible_sub R d ρ σ hρ hσ) i

theorem magnetic_sub_mass (k R T d : ℝ) (hd : 0 < d) (hdM : d ≤ T+R) (ρ σ : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) (i : Fin 3) :
    IntegrableOn (fun q : Plane => MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q) i-
      MagneticResponse.magnetic k σ (MaxwellPlaneTail.planePoint q) i) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q) i-
      MagneticResponse.magnetic k σ (MaxwellPlaneTail.planePoint q) i‖) ≤
      (2 * |k| * PlaneMaxwellSharp.gradientMass k R T d)*sourceMass (ρ-σ) := by
  have he : (fun q : Plane => MagneticResponse.magnetic k (ρ-σ) (MaxwellPlaneTail.planePoint q) i) =
      (fun q : Plane => MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q) i-
        MagneticResponse.magnetic k σ (MaxwellPlaneTail.planePoint q) i) := by
    funext q
    exact congrFun (magnetic_plane_sub k R d hd ρ σ hρ hσ q) i
  have he' (q : Plane) := congrFun he q
  simpa only [he, he'] using magnetic_mass k R T d hd hdM (ρ-σ) (admissible_sub R d ρ σ hρ hσ) i
end OQ14.PlaneMaxwellFields
#print axioms OQ14.PlaneMaxwellFields.electric_mass
#print axioms OQ14.PlaneMaxwellFields.remainder_mass
#print axioms OQ14.PlaneMaxwellFields.magnetic_mass
#print axioms OQ14.PlaneMaxwellFields.electric_sub_mass
#print axioms OQ14.PlaneMaxwellFields.magnetic_sub_mass
