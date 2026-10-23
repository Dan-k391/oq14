import StaticSourceTail

/-! A genuine dynamic-minus-static coherent flux bound uniform in the plane gap. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.StaticCoherentRemainder
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation
open SphereReactionKernel (entryBound entryBound_nonnegative)
open SourceHerglotzLocal (electricFlux)
open Maxwell (conjugate)
open scoped Topology
abbrev Space := FourierL2.Space

def staticFlux (k : ℝ) (S : Source) (z : Space) (m : Fin 3) (q : Plane) : ℂ :=
  crossProduct (NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q))
    (conjugate (fun i => SphereMagneticKernel.K k (MaxwellPlaneTail.planePoint q-z) i m)) 2

def flux (k : ℝ) (S : Source) (z : Space) (m : Fin 3) (q : Plane) : ℂ :=
  electricFlux k S z m q-staticFlux k S z m q

def tailCoefficient (k R : ℝ) : ℝ :=
  PointMaxwellTail.tailConstant k k R+16*entryBound k/Real.pi

def wholeCoefficient (k R T : ℝ) : ℝ :=
  2*entryBound k*PlaneMaxwellSharp.remainderMass k R T+
    tailCoefficient k R*PlaneInverseCube.diskConstant/T

theorem field_split (k R d : ℝ) (hd : 0 < d) (S : Source) (hS : Admissible R d S)
    (q : Plane) (i : Fin 3) :
    ExteriorContinuity.electric k S (MaxwellPlaneTail.planePoint q) i-
      NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q) i=
      ∑ j, KernelConvolution.response (fun z => DyadicKernel.remainder k z i j) (S j) (MaxwellPlaneTail.planePoint q) := by
  unfold ExteriorContinuity.electric NewtonSeparatedResponse.response
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hi := response_plane_integrable _ (dyadic_measurable k i j)
    (fun z hz => ExteriorContinuity.dyadic_continuousAt k i j z hz) R d hd S hS q j
  have hs := response_plane_integrable _ (StaticPlaneKernel.hessian_measurable i j)
    (fun z hz => NewtonExterior.hessian_continuousAt 0 i j z hz) R d hd S hS q j
  unfold KernelConvolution.response
  rw [← integral_sub hi hs]
  apply integral_congr_ae
  filter_upwards with y
  unfold DyadicKernel.remainder
  ring

theorem static_continuous (k R d : ℝ) (hd : 0 < d) (S : Source) (hS : Admissible R d S)
    (z : Space) (m : Fin 3) : Continuous (staticFlux k S z m) := by
  have hs (i : Fin 3) : Continuous (fun q : Plane => NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q) i) := by
    apply continuous_finset_sum
    intro j _
    exact response_plane_continuous _ (StaticPlaneKernel.hessian_measurable i j)
      (fun z hz => NewtonExterior.hessian_continuousAt 0 i j z hz) R d hd S hS j
  have hK (i : Fin 3) : Continuous (fun q : Plane => SphereMagneticKernel.K k (MaxwellPlaneTail.planePoint q-z) i m) :=
    (SphereMagneticKernel.K_continuous k i m).comp (MaxwellPlaneTail.planePoint_continuous.sub continuous_const)
  exact ((hs 0).mul (hK 1).star).sub ((hs 1).mul (hK 0).star)

theorem flux_remainder (k R d : ℝ) (hd : 0 < d) (S : Source) (hS : Admissible R d S)
    (z : Space) (m : Fin 3) (q : Plane) :
    flux k S z m q=crossProduct
      (fun i => ∑ j, KernelConvolution.response (fun w => DyadicKernel.remainder k w i j) (S j) (MaxwellPlaneTail.planePoint q))
      (conjugate (fun i => SphereMagneticKernel.K k (MaxwellPlaneTail.planePoint q-z) i m)) 2 := by
  simp only [← field_split k R d hd S hS]
  unfold flux staticFlux electricFlux
  simp [cross_apply,conjugate]
  ring

theorem local_mass (k R T d : ℝ) (hd : 0 < d) (hdM : d ≤ T+R) (S : Source) (hS : Admissible R d S)
    (z : Space) (m : Fin 3) :
    IntegrableOn (flux k S z m) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖flux k S z m q‖) ≤
      (2*entryBound k*PlaneMaxwellSharp.remainderMass k R T)*sourceMass S := by
  let F := fun q i => ∑ j, KernelConvolution.response (fun w => DyadicKernel.remainder k w i j) (S j) (MaxwellPlaneTail.planePoint q)
  have hf (i : Fin 3) := PlaneMaxwellFields.remainder_mass k R T d hd hdM S hS i
  have hb (q : Plane) : ‖flux k S z m q‖ ≤ entryBound k*(‖F q 0‖+‖F q 1‖) := by
    rw [flux_remainder k R d hd S hS]
    change ‖F q 0*star (SphereMagneticKernel.K k (MaxwellPlaneTail.planePoint q-z) 1 m)-
      F q 1*star (SphereMagneticKernel.K k (MaxwellPlaneTail.planePoint q-z) 0 m)‖ ≤ _
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_star]
    exact (add_le_add
      (mul_le_mul_of_nonneg_left (SphereMagneticKernel.K_bound k _ 1 m) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (SphereMagneticKernel.K_bound k _ 0 m) (norm_nonneg _))).trans_eq (by ring)
  have hg : IntegrableOn (fun q => entryBound k*(‖F q 0‖+‖F q 1‖)) (closedBall 0 T) :=
    ((hf 0).1.norm.add (hf 1).1.norm).const_mul _
  have hc := (SourceHerglotzLocal.electric_continuous k R d hd S hS z m).sub (static_continuous k R d hd S hS z m)
  have hi := hg.mono' hc.aestronglyMeasurable.restrict (Filter.Eventually.of_forall hb)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ q : Plane in closedBall 0 T, entryBound k*(‖F q 0‖+‖F q 1‖) :=
      integral_mono_ae hi.norm hg (Filter.Eventually.of_forall hb)
    _ = entryBound k*((∫ q : Plane in closedBall 0 T, ‖F q 0‖)+(∫ q : Plane in closedBall 0 T, ‖F q 1‖)) := by
      rw [integral_const_mul,integral_add (hf 0).1.norm (hf 1).1.norm]
    _ ≤ entryBound k*(PlaneMaxwellSharp.remainderMass k R T*sourceMass S+PlaneMaxwellSharp.remainderMass k R T*sourceMass S) :=
      mul_le_mul_of_nonneg_left (add_le_add (hf 0).2 (hf 1).2) (entryBound_nonnegative k)
    _ = _ := by ring

theorem tail_bound (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (S : Source) (hS : Admissible R d S) (z : Space) (hz : z ∈ closedBall 0 R)
    (m : Fin 3) (q : Plane) (hq : 2*R < ‖q‖) (hq2 : 2 ≤ ‖q‖) :
    ‖flux k S z m q‖ ≤ (tailCoefficient k R*sourceMass S)/‖q‖^3 := by
  have hs := StaticSourceTail.field_bound R d hR hd S hS q hq
  have hC : 0 ≤ ((8/Real.pi)/‖q‖^3)*sourceMass S := by
    have := sourceMass_nonnegative S
    positivity
  have hstatic := MaxwellPlaneTail.cross_norm_bound _ (fun i => SphereMagneticKernel.K k (MaxwellPlaneTail.planePoint q-z) i m) _ _ hC (entryBound_nonnegative k) hs
    (fun i => SphereMagneticKernel.K_bound k (MaxwellPlaneTail.planePoint q-z) i m) 2
  have he := SourceHerglotzTail.electric_tail k R d hR hd hk S hS z hz m q hq hq2
  exact ((norm_sub_le _ _).trans (add_le_add he hstatic)).trans_eq (by unfold tailCoefficient; ring)

theorem whole_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hdM : d ≤ T+R)
    (S : Source) (hS : Admissible R d S) (z : Space) (hz : z ∈ closedBall 0 R) (m : Fin 3) :
    Integrable (flux k S z m) ∧ (∫ q : Plane, ‖flux k S z m q‖) ≤ wholeCoefficient k R T*sourceMass S := by
  have hl := local_mass k R T d hd hdM S hS z m
  have hc := (SourceHerglotzLocal.electric_continuous k R d hd S hS z m).sub (static_continuous k R d hd S hS z m)
  have hb (q : Plane) (hq : T < ‖q‖) := tail_bound k R d hR hd hk S hS z hz m q (by linarith) (by linarith)
  have hi := PlaneInverseCube.tail_integrable T _ (by linarith) hc.aestronglyMeasurable.restrict hb
  have hu := PlaneInverseCube.tail_integral_bound T _ (by linarith) hc.aestronglyMeasurable.restrict hb
  have hs : {q : Plane | T < ‖q‖}=(closedBall (0 : Plane) T)ᶜ := by
    ext q; simp [mem_closedBall,dist_zero_right,not_le]
  rw [hs] at hi hu
  have hall : Integrable (flux k S z m) := by
    simpa only [union_compl_self,integrableOn_univ] using hl.1.union hi
  refine ⟨hall,?_⟩
  rw [← integral_add_compl isClosed_closedBall.measurableSet hall.norm]
  exact (add_le_add hl.2 hu).trans_eq (by unfold wholeCoefficient; ring)

end OQ14.StaticCoherentRemainder
#print axioms OQ14.StaticCoherentRemainder.field_split
#print axioms OQ14.StaticCoherentRemainder.static_continuous
#print axioms OQ14.StaticCoherentRemainder.flux_remainder
#print axioms OQ14.StaticCoherentRemainder.local_mass
#print axioms OQ14.StaticCoherentRemainder.tail_bound
#print axioms OQ14.StaticCoherentRemainder.whole_mass
