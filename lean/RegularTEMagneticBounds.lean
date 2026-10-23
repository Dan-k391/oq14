import RegularTEMagneticTrace
import RegularTEDecomposition
import MaxwellPlaneTail

/-! Derived uniform angular inverse-radius magnetic bounds for actual TE Hankel parts. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RegularTEMagneticBounds
open Complex Filter Set Metric Maxwell DebyeRadialTrace HarmonicPolynomial RegularTEIncoming
open RegularTEMagneticTrace
open scoped Topology
abbrev Space := FourierL2.Space
abbrev Sphere := SphereReactionKernel.Sphere

theorem ray_bounds (l : ℕ) (inward : Bool) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) : ∃ C : ℝ, 0≤C ∧ ∀ᶠ r : ℝ in atTop,
      ∀ n : Sphere, (∀ i : Fin 3, ‖magnetic l inward p (r • (n : Space)) i‖≤C/r) ∧
        ‖dot (position n) (magnetic l inward p (r • (n : Space)))‖≤C/r^2 := by
  have hT : Continuous (fun n : Sphere => angularToroidal p n) :=
    (HarmonicRadiationGeometry.angularToroidal_continuous p).comp continuous_subtype_val
  have hP : Continuous (fun n : Sphere => complexEvaluate p n) :=
    (complexEvaluate_regular p).continuous.comp continuous_subtype_val
  obtain ⟨T,hT⟩ := (isCompact_univ : IsCompact (univ : Set Sphere)).exists_bound_of_continuousOn hT.continuousOn
  obtain ⟨P,hP⟩ := (isCompact_univ : IsCompact (univ : Set Sphere)).exists_bound_of_continuousOn hP.continuousOn
  let M := max 0 (max T P)
  have hM : 0≤M := le_max_left _ _
  have hbT (n : Sphere) (i : Fin 3) : ‖angularToroidal p n i‖≤M :=
    (norm_le_pi_norm _ i).trans ((hT n (mem_univ n)).trans ((le_max_left T P).trans (le_max_right _ _)))
  have hbP (n : Sphere) : ‖complexEvaluate p n‖≤M :=
    (hP n (mem_univ n)).trans ((le_max_right T P).trans (le_max_right _ _))
  let D := (l : ℝ)*(l+1)*M
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨2*M+D,by positivity,?_⟩
  filter_upwards [radial_eventually_bounded l inward,radialD_eventually_bounded l inward,
    eventually_ge_atTop (1 : ℝ)] with r hrad hradD hr1
  intro n
  have hr : 0<r := by linarith
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have hcoord (i : Fin 3) : ‖position n i‖≤1 := SphereWaveCalculus.coordinate_bound i n
  let H := magnetic l inward p (r • (n : Space))
  have hcross (i : Fin 3) : ‖crossProduct (position n) H i‖≤M/r := by
    rw [show H=magnetic l inward p (r • (n : Space)) from rfl,magnetic_tangent_ray l inward p hp hh n r hr]
    simp only [Pi.smul_apply,smul_eq_mul]
    calc
      _ = (‖radialD l inward r‖/(2*r))*‖angularToroidal p n i‖ := by
        simp [norm_mul,norm_div,abs_of_pos hr]
      _ ≤ (2/(2*r))*M := mul_le_mul (div_le_div_of_nonneg_right hradD (by positivity))
        (hbT n i) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hdot : ‖dot (position n) H‖≤D/r^2 := by
    rw [show H=magnetic l inward p (r • (n : Space)) from rfl,magnetic_radial_ray l inward p hp hh n r hr]
    have hl : ‖(l : ℂ)+1‖=(l : ℝ)+1 := by
      rw [show (l : ℂ)+1=(((l : ℝ)+1 : ℝ) : ℂ) by push_cast; rfl]
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0≤(l : ℝ)+1 by positivity)]
    calc
      _ = ((l : ℝ)*(l+1)*‖radial l inward r‖/(2*r^2))*‖complexEvaluate p n‖ := by
        simp [norm_mul,norm_div,hl,norm_pow,abs_of_pos hr]
      _ ≤ ((l : ℝ)*(l+1)*2/(2*r^2))*M := mul_le_mul
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrad (by positivity)) (by positivity))
        (hbP n) (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [D]; ring
  have hdir : MaxwellRadiation.direction (n : Space)=position n := by
    ext i
    simp [MaxwellRadiation.direction,GreenKernel.unitCoordinate,hn,position]
  have hnn : dot (position n) (position n)=1 := by
    have h := MaxwellRadiation.direction_dot (n : Space) (norm_pos_iff.mp (by rw [hn]; norm_num))
    rwa [hdir] at h
  have hid (i : Fin 3) : H i=crossProduct (crossProduct (position n) H) (position n) i+
      dot (position n) H*position n i := by
    rw [MaxwellRadiation.cross_cross_same,hnn,one_mul]
    ring
  have hcross2 (i : Fin 3) : ‖crossProduct (crossProduct (position n) H) (position n) i‖≤2*(M/r) := by
    have h := MaxwellRadiation.cross_direction_bound (crossProduct (position n) H) (n : Space)
      (M/r) (by positivity) hcross i
    rwa [hdir] at h
  refine ⟨?_,hdot.trans (div_le_div_of_nonneg_right (by linarith [hM]) (sq_nonneg r))⟩
  intro i
  change ‖H i‖≤(2*M+D)/r
  calc
    _ ≤ 2*(M/r)+D/r^2 := by
      rw [hid]
      apply (norm_add_le _ _).trans
      apply add_le_add (hcross2 i)
      rw [norm_mul]
      exact (mul_le_mul hdot (hcoord i) (norm_nonneg _) (by positivity)).trans_eq (by ring)
    _ ≤ 2*(M/r)+D/r := add_le_add_left (div_le_div_of_nonneg_left hD hr (by nlinarith)) _
    _ = _ := by ring

theorem regular_ray_bounds (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) : ∃ C : ℝ, 0≤C ∧ ∀ᶠ r : ℝ in atTop,
      ∀ n : Sphere,
        (∀ i : Fin 3, ‖DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave l 1 p) (r • (n : Space)) i‖≤C/r) ∧
        ‖dot (position n) (DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave l 1 p) (r • (n : Space)))‖≤C/r^2 := by
  obtain ⟨C,hC,hb⟩ := ray_bounds l false p hp hh
  obtain ⟨D,hD,hd⟩ := ray_bounds l true p hp hh
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  filter_upwards [hb,hd,eventually_gt_atTop (0 : ℝ)] with r hb hd hr
  intro n
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have hx : r • (n : Space)≠0 := norm_pos_iff.mp (by simp [norm_smul,abs_of_pos hr,hn,hr])
  rw [RegularTEDecomposition.magnetic_split l p hp _ hx]
  refine ⟨?_,?_⟩
  · intro i
    exact (norm_add_le _ _).trans ((add_le_add ((hb n).1 i) ((hd n).1 i)).trans_eq (by ring))
  · have he : dot (position n) (magnetic l false p (r • (n : Space))+magnetic l true p (r • (n : Space)))=
        dot (position n) (magnetic l false p (r • (n : Space)))+
        dot (position n) (magnetic l true p (r • (n : Space))) := by
      simp [dot,Pi.add_apply]; ring
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add (hb n).2 (hd n).2).trans_eq (by ring))

end OQ14.RegularTEMagneticBounds
#print axioms OQ14.RegularTEMagneticBounds.ray_bounds
#print axioms OQ14.RegularTEMagneticBounds.regular_ray_bounds
