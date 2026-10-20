import SphereReactionKernel
import BoundedMaterialKernel

/-! # Actual support-volume parity reaction operators and self-consistent inverse

The explicit spherical-integral kernels are integrated against the actual
material source. Their norms are proportional to material volume. The
combined inverse below concerns this explicit kernel only.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ParityReactionVolume

open MeasureTheory Metric DynamicConvolution
open scoped BigOperators

abbrev Coefficient := StaticCoefficient.Coefficient
abbrev SupportData := BoundedMaterialKernel.SupportData

def entries (electric : Bool) (k : ℝ) (i j : Fin 3) : BoundedMaterialKernel.Kernel where
  value x y := SphereReactionKernel.reaction electric k x y i j
  continuous := SphereReactionKernel.reaction_continuous electric k i j
  bound := SphereReactionKernel.entryBound k
  nonnegative := SphereReactionKernel.entryBound_nonnegative k
  bounded x y := SphereReactionKernel.reaction_bound electric k x y i j

def operator {c : Coefficient} (d : SupportData c) (electric : Bool) (k : ℝ) :
    VectorL2 →L[ℂ] VectorL2 := BoundedMaterialKernel.operator d (entries electric k)

def reactionBound {c : Coefficient} (d : SupportData c) (k : ℝ) : ℝ :=
  9 * c.bound * volume.real d.carrier * SphereReactionKernel.entryBound k

theorem reactionBound_nonnegative {c : Coefficient} (d : SupportData c) (k : ℝ) :
    0 ≤ reactionBound d k := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (StaticCoefficient.bound_nonnegative c)) measureReal_nonneg)
      (SphereReactionKernel.entryBound_nonnegative k)

theorem operator_norm {c : Coefficient} (d : SupportData c) (electric : Bool) (k : ℝ) :
    ‖operator d electric k‖ ≤ reactionBound d k := by
  apply (BoundedMaterialKernel.operator_norm d (entries electric k)).trans_eq
  simp only [BoundedMaterialKernel.bound, entries, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, reactionBound]
  ring

/-- Literal reaction integral; both square-root multipliers and the actual
spherical-integral parity kernel occur in the statement. -/
theorem operator_actual {c : Coefficient} (d : SupportData c) (electric : Bool)
    (k : ℝ) (u : VectorL2) (i : Fin 3) :
    (fun x => operator d electric k u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
        ∑ j : Fin 3, ∫ y, SphereReactionKernel.reaction electric k x y i j *
          DynamicVolume.source c u j y := by
  have he (x : Space) (j : Fin 3) :
      (∫ y, SphereReactionKernel.reaction electric k x y i j *
        component j (StaticCoefficient.sqrtMultiplier c u) y) =
      ∫ y, SphereReactionKernel.reaction electric k x y i j * DynamicVolume.source c u j y := by
    apply integral_congr_ae
    filter_upwards [StaticNewton.material_source_ae c u j] with y hy
    rw [component_apply, hy]
    rfl
  have ha := BoundedMaterialKernel.component_operator_ae d (entries electric k) u i
  have hc := NewtonL2.physicalCoordinate_ae (operator d electric k u) i
  filter_upwards [ha, hc] with x hx hy
  change component i (operator d electric k u) x = _ at hx
  rw [← hy]
  change component i (operator d electric k u) x = _
  rw [hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact he x j

def perturbation {c : Coefficient} (d : SupportData c) (k B : ℝ) :
    VectorL2 →L[ℂ] VectorL2 :=
  DynamicVolume.weightedRemainder c k d.radius +
    ((B^2-1 : ℝ) : ℂ) • operator d true k +
    ((B⁻¹^2-1 : ℝ) : ℂ) • operator d false k

def perturbationBound {c : Coefficient} (d : SupportData c) (k B : ℝ) : ℝ :=
  DynamicSupportVolume.volumeBound c k d.radius d.carrier +
    (|B^2-1| + |B⁻¹^2-1|) * reactionBound d k

theorem perturbationBound_nonnegative {c : Coefficient} (d : SupportData c) (k B : ℝ) :
    0 ≤ perturbationBound d k B :=
  add_nonneg (DynamicSupportVolume.volumeBound_nonnegative c k d.radius d.carrier)
    (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (reactionBound_nonnegative d k))

theorem perturbation_norm {c : Coefficient} (d : SupportData c) (k B : ℝ) :
    ‖perturbation d k B‖ ≤ perturbationBound d k B := by
  have hd := DynamicSupportVolume.weightedRemainder_norm_le c k d.radius d.ballZero
    d.carrier d.measurable d.finite d.carrierZero
  have he := operator_norm d true k
  have hm := operator_norm d false k
  have hse : ‖((B^2-1 : ℝ) : ℂ) • operator d true k‖ ≤ |B^2-1| * reactionBound d k := by
    calc
      _ ≤ ‖((B^2-1 : ℝ) : ℂ)‖ * ‖operator d true k‖ := norm_smul_le _ _
      _ = |B^2-1| * ‖operator d true k‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := mul_le_mul_of_nonneg_left he (abs_nonneg _)
  have hsm : ‖((B⁻¹^2-1 : ℝ) : ℂ) • operator d false k‖ ≤ |B⁻¹^2-1| * reactionBound d k := by
    calc
      _ ≤ ‖((B⁻¹^2-1 : ℝ) : ℂ)‖ * ‖operator d false k‖ := norm_smul_le _ _
      _ = |B⁻¹^2-1| * ‖operator d false k‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (abs_nonneg _)
  unfold perturbation perturbationBound
  exact (norm_add_le _ _).trans
    ((add_le_add ((norm_add_le _ _).trans (add_le_add hd hse)) hsm).trans_eq (by ring))

theorem explicitBlock_isUnit {c : Coefficient} (d : SupportData c) (k B : ℝ)
    (hsmall : perturbationBound d k B < 1) :
    IsUnit (StaticCoefficient.weightedBlock c - perturbation d k B) :=
  StaticCoefficient.weightedBlock_perturbation_isUnit c _
    ((perturbation_norm d k B).trans_lt hsmall)

theorem explicitBlock_inverse_le_two {c : Coefficient} (d : SupportData c) (k B : ℝ)
    (hsmall : perturbationBound d k B ≤ 1/2) :
    ‖Ring.inverse (StaticCoefficient.weightedBlock c - perturbation d k B)‖ ≤ 2 := by
  have hn := (perturbation_norm d k B).trans hsmall
  have hlt : ‖perturbation d k B‖ < 1 := by linarith
  apply (StaticCoefficient.weightedBlock_perturbation_inverse c _ hlt).trans
  exact (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by linarith)

end OQ14.ParityReactionVolume

#print axioms OQ14.ParityReactionVolume.reactionBound_nonnegative
#print axioms OQ14.ParityReactionVolume.operator_norm
#print axioms OQ14.ParityReactionVolume.operator_actual
#print axioms OQ14.ParityReactionVolume.perturbationBound_nonnegative
#print axioms OQ14.ParityReactionVolume.perturbation_norm
#print axioms OQ14.ParityReactionVolume.explicitBlock_isUnit
#print axioms OQ14.ParityReactionVolume.explicitBlock_inverse_le_two
