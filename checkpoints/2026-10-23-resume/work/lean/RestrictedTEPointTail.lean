import RestrictedTEMagneticTail
import TransversePlaneFlux
import PointMaxwellTail
import ParityPlaneColumns

/-! Actual point dyadic and parity-electric flux tails against finite harmonic TE magnetic fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEPointTail
open Complex Filter Set Metric MeasureTheory Maxwell PlaneSourceKernel MaxwellRadiation
open SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space

private theorem leading_zero (k : ℝ) (x y : Space) (j : Fin 3) (hx : x≠0)
    (hp : x 2=0) (H : Vector) :
    crossProduct (PointMaxwellTail.leadingE k x y j)
      (conjugate (TransversePlaneFlux.tangentPart x H)) 2=0 := by
  change PointMaxwellTail.leadingE k x y j 0*conj (TransversePlaneFlux.tangentPart x H 1)-
    PointMaxwellTail.leadingE k x y j 1*conj (TransversePlaneFlux.tangentPart x H 0)=0
  rw [← PointMaxwellTail.leading_identity k x y hx 0 j,← PointMaxwellTail.leading_identity k x y hx 1 j]
  simp [TransversePlaneFlux.tangentPart,cross_apply,direction,GreenKernel.unitCoordinate,hp]
  ring

theorem dyadic_tail (A : Index →₀ ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∃ T : ℝ, 2≤T ∧ 2*R≤T ∧ ∀ (k : ℝ) (x y : Space) (j : Fin 3),
      T<‖x‖ → x 2=0 → y∈closedBall 0 R →
      ‖crossProduct (fun i => DyadicKernel.dyadic k (x-y) i j) (conjugate (magnetic A x)) 2‖≤
        (2*C*(MaxwellPlaneTail.electricErrorConstant k R+MaxwellPlaneTail.leadingConstant k))/‖x‖^3 := by
  obtain ⟨C,hC,T,hT,hbound⟩ := RestrictedTEMagneticTail.field_bounds A
  refine ⟨C,hC,max T (2*R),hT.trans (le_max_left _ _),le_max_right _ _,?_⟩
  intro k x y j hx hp hy
  have hxT : T<‖x‖ := lt_of_le_of_lt (le_max_left _ _) hx
  have hxR : 2*R<‖x‖ := lt_of_le_of_lt (le_max_right _ _) hx
  have hx2 : 2≤‖x‖ := hT.trans hxT.le
  have hxpos : 0<‖x‖ := by linarith
  have hx0 : x≠0 := norm_pos_iff.mp hxpos
  have hE : 0≤MaxwellPlaneTail.electricErrorConstant k R := by unfold MaxwellPlaneTail.electricErrorConstant; positivity
  have hL : 0≤MaxwellPlaneTail.leadingConstant k := by unfold MaxwellPlaneTail.leadingConstant; positivity
  have hb := hbound x hxT
  have herr := TransversePlaneFlux.radial_error_bound x hx0 (magnetic A x) (C/‖x‖^2) (by positivity) hb.2
  have h := MaxwellPlaneTail.cross_perturbation_bound
    (fun i => DyadicKernel.dyadic k (x-y) i j) (magnetic A x)
    (PointMaxwellTail.leadingE k x y j) (TransversePlaneFlux.tangentPart x (magnetic A x))
    (MaxwellPlaneTail.leadingConstant k/‖x‖) (C/‖x‖)
    (MaxwellPlaneTail.electricErrorConstant k R/‖x‖^2) (C/‖x‖^2)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (fun i => PointMaxwellTail.leading_electric_bound k R hR x y hxR hy i j) hb.1
    (fun i => PointMaxwellTail.electric_error k R hR x y hxR hx2 hy i j) herr
    (leading_zero k x y j hx0 hp (magnetic A x))
  exact h.trans_eq (by field_simp; ring)

theorem J_tail (A : Index →₀ ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ K : ℝ, 0≤K ∧ ∃ T : ℝ, 2≤T ∧ 2*R≤T ∧ ∀ (x y : Space) (j : Fin 3),
      T<‖x‖ → x 2=0 → y∈closedBall 0 R →
      ‖crossProduct (fun i => SphereReactionKernel.J 1 (x-y) i j) (conjugate (magnetic A x)) 2‖≤K/‖x‖^3 := by
  obtain ⟨C,hC,T,hT,hTR,hb⟩ := dyadic_tail A R hR
  let K := 2*C*(MaxwellPlaneTail.electricErrorConstant 1 R+MaxwellPlaneTail.leadingConstant 1)
  have hK : 0≤K := by dsimp [K,MaxwellPlaneTail.electricErrorConstant,MaxwellPlaneTail.leadingConstant]; positivity
  refine ⟨K,hK,T,hT,hTR,?_⟩
  intro x y j hx hp hy
  have hxy : x-y≠0 := (ScalarRadiation.distance_lower_bound R hR x y (lt_of_le_of_lt hTR hx) hy).2.1
  let F := fun k : ℝ => crossProduct (fun i => DyadicKernel.dyadic k (x-y) i j) (conjugate (magnetic A x)) 2
  have hplus : ‖F 1‖≤K/‖x‖^3 := hb 1 x y j hx hp hy
  have hminus : ‖F (-1)‖≤K/‖x‖^3 := by
    simpa only [K,MaxwellPlaneTail.electricErrorConstant,MaxwellPlaneTail.leadingConstant,neg_sq,abs_neg] using
      hb (-1) x y j hx hp hy
  have he : crossProduct (fun i => SphereReactionKernel.J 1 (x-y) i j) (conjugate (magnetic A x)) 2=
      (-I/2)*(F 1-F (-1)) := by
    change SphereReactionKernel.J 1 (x-y) 0 j*conj (magnetic A x 1)-
      SphereReactionKernel.J 1 (x-y) 1 j*conj (magnetic A x 0)=_
    rw [SphereDyadicTransform.J_dyadic 1 (x-y) one_ne_zero hxy 0 j,
      SphereDyadicTransform.J_dyadic 1 (x-y) one_ne_zero hxy 1 j]
    simp [F,cross_apply,conjugate]
    field_simp
    ring_nf
    norm_num [I_sq]
    ring
  rw [he,norm_mul,show ‖(-I/2 : ℂ)‖=(1/2 : ℝ) by norm_num [norm_div]]
  exact (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hplus hminus)) (by norm_num)).trans_eq (by ring)

theorem reaction_tail (A : Index →₀ ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ K : ℝ, 0≤K ∧ ∃ T : ℝ, 2≤T ∧ 2*R≤T ∧ ∀ (e : Bool) (x y : Space) (j : Fin 3),
      T<‖x‖ → x 2=0 → y∈closedBall 0 R →
      ‖crossProduct (fun i => SphereReactionKernel.reaction e 1 x y i j) (conjugate (magnetic A x)) 2‖≤K/‖x‖^3 := by
  obtain ⟨K,hK,T,hT,hTR,hb⟩ := J_tail A R hR
  refine ⟨K,hK,T,hT,hTR,?_⟩
  intro e x y j hx hp hy
  have he : crossProduct (fun i => SphereReactionKernel.reaction e 1 x y i j) (conjugate (magnetic A x)) 2=
      (if e then 0 else I)*crossProduct (fun i => SphereReactionKernel.J 1 (x-y) i j) (conjugate (magnetic A x)) 2 := by
    change SphereReactionKernel.reaction e 1 x y 0 j*conj (magnetic A x 1)-
      SphereReactionKernel.reaction e 1 x y 1 j*conj (magnetic A x 0)=_
    rw [SphereMagneticParity.reaction_on_plane e 1 x y hp 0 j,
      SphereMagneticParity.reaction_on_plane e 1 x y hp 1 j]
    cases e <;> norm_num [SphereReactionKernel.sign,Fin.ext_iff,cross_apply,conjugate]
    all_goals simp
    all_goals ring
  rw [he]
  cases e
  · simpa only [Bool.false_eq_true,if_false,norm_mul,norm_I,one_mul] using hb x y j hx hp hy
  · simpa only [if_true,zero_mul,norm_zero] using div_nonneg hK (by positivity : 0≤‖x‖^3)

theorem global_envelope (A : Index →₀ ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ w : Plane → ℝ, Integrable w ∧ (∀ q, 0≤w q) ∧ ∀ (e : Bool) (y : Space), y∈closedBall 0 R →
      ∀ (j : Fin 3) (q : Plane),
        ‖crossProduct (fun i => SphereReactionKernel.reaction e 1 (MaxwellPlaneTail.planePoint q) y i j)
          (conjugate (magnetic A (MaxwellPlaneTail.planePoint q))) 2‖≤w q := by
  obtain ⟨K,hK,T,hT,hTR,hb⟩ := reaction_tail A R hR
  obtain ⟨B,hB,hH⟩ := RestrictedTEMagnetic.magnetic_bounded A
  let D := 2*SphereReactionKernel.entryBound 1*B
  have hD : 0≤D := mul_nonneg (mul_nonneg (by norm_num) (SphereReactionKernel.entryBound_nonnegative 1)) hB
  refine ⟨MaxwellPlaneL1.envelope T D K,MaxwellPlaneL1.envelope_integrable T D K (by linarith),
    MaxwellPlaneL1.envelope_nonnegative T D K hD hK,?_⟩
  intro e y hy j q
  by_cases hq : ‖q‖≤T
  · have he : MaxwellPlaneL1.envelope T D K q=D := by
      simp [MaxwellPlaneL1.envelope,PlaneInverseCube.profile,Set.indicator,mem_closedBall,dist_zero_right,hq,not_lt.mpr hq]
    rw [he]
    exact MaxwellPlaneTail.cross_norm_bound _ _ (SphereReactionKernel.entryBound 1) B
      (SphereReactionKernel.entryBound_nonnegative 1) hB
      (fun i => SphereReactionKernel.reaction_bound e 1 _ y i j) (hH _) 2
  · have ht : T<‖q‖ := lt_of_not_ge hq
    have he : MaxwellPlaneL1.envelope T D K q=K/‖q‖^3 := by
      simp [MaxwellPlaneL1.envelope,PlaneInverseCube.profile,Set.indicator,mem_closedBall,dist_zero_right,hq,ht,div_eq_mul_inv]
    rw [he]
    simpa only [MaxwellPlaneTail.planePoint_norm] using hb e (MaxwellPlaneTail.planePoint q) y j
      (by rwa [MaxwellPlaneTail.planePoint_norm]) (by rfl) hy

end OQ14.RestrictedTEPointTail
#print axioms OQ14.RestrictedTEPointTail.dyadic_tail
#print axioms OQ14.RestrictedTEPointTail.J_tail
#print axioms OQ14.RestrictedTEPointTail.reaction_tail
#print axioms OQ14.RestrictedTEPointTail.global_envelope
