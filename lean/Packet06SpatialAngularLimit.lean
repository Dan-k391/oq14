import Packet06DominatedL2
import ConicalAnnularCoefficient
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SpatialAngularLimit
open Filter Set MeasureTheory OQ14.Maxwell OQ14.AngularPower OQ14.ConicalMomentWeights
  OQ14.ConicalTangentialDivergence OQ14.ConicalAnnularCoefficient
open scoped Topology

def angularTest (ζ : ℝ → ℝ) (a d t : ℝ) (i : Fin 3) (x : Maxwell.Space) : ℂ :=
  ((t⁻¹ : ℝ) : ℂ)*tangent a d t i (ConicalCapField.unit x)*(ζ ‖x‖ : ℂ)

def limitTest (ζ : ℝ → ℝ) (i : Fin 3) (x : Maxwell.Space) : ℂ :=
  (((basis 2-(((ConicalCapField.unit x : Sphere) : Maxwell.Space) 2) •
    ((ConicalCapField.unit x : Sphere) : Maxwell.Space)) i : ℝ) : ℂ)*(ζ ‖x‖ : ℂ)

theorem angularTest_memLp (ζ : ℝ → ℝ) (hζ : Continuous ζ) (hc : HasCompactSupport ζ)
    (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    MemLp (angularTest ζ a d t i) 2 volume := by
  have h := ((tangentField_memLp a d t ha hd ht ht1 ζ hζ hc i).ofReal).const_mul ((t⁻¹ : ℝ) : ℂ)
  apply h.ae_eq
  filter_upwards with x
  simp only [angularTest,tangent_unit,tangentField,weightedTangent]
  push_cast
  simp only [mul_comm, mul_left_comm, mul_assoc]
  rfl

theorem limitTest_eq (ζ : ℝ → ℝ) (t : ℝ) (ht : 0 < t) (i : Fin 3) :
    limitTest ζ i = angularTest ζ 2 0 t i := by
  funext x
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  simp only [limitTest,angularTest,tangent,CapSturmLiouville.coefficient,add_zero,ite_self,
    one_mul,SphereCapH1.gradient,Packet06ConeGradientLimit.slope_two,PiLp.smul_apply,smul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_inv]
  field_simp [ht0]

def limitTest_memLp (ζ : ℝ → ℝ) (hζ : Continuous ζ) (hc : HasCompactSupport ζ)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) : MemLp (limitTest ζ i) 2 volume := by
  rw [limitTest_eq ζ t ht i]
  exact angularTest_memLp ζ hζ hc 2 0 t (by norm_num) (by norm_num) ht ht1 i

theorem angularTest_tendsto (ell d : ℕ → ℝ) (hell : Tendsto ell atTop (𝓝 2))
    (hd : Tendsto d atTop (𝓝 0)) (hbound : ∀ j, ell j ∈ Icc (0 : ℝ) 2)
    (D : ℝ) (hD : 0 ≤ D) (hdBound : ∀ j, d j ∈ Icc (0 : ℝ) D)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : Continuous ζ) (hc : HasCompactSupport ζ)
    (i : Fin 3) :
    Tendsto (fun j => (angularTest_memLp ζ hζ hc (ell j) (d j) t (hbound j) (hdBound j).1 ht ht1 i).toLp
      (angularTest ζ (ell j) (d j) t i)) atTop
      (𝓝 ((limitTest_memLp ζ hζ hc t ht ht1 i).toLp (limitTest ζ i))) := by
  let f := fun j => angularTest ζ (ell j) (d j) t i
  let g := limitTest ζ i
  have hf j := angularTest_memLp ζ hζ hc (ell j) (d j) t (hbound j) (hdBound j).1 ht ht1 i
  have hg := limitTest_memLp ζ hζ hc t ht ht1 i
  obtain ⟨C,hC,hweights⟩ := Packet06ConeUniformWeights.uniform_weights t D ht ht1 hD
  let B : ℝ := t⁻¹*C+1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hζlp : MemLp (fun x : Maxwell.Space => ζ ‖x‖) 2 volume := by
    have hc' := ConicalRadialDivergence.radialReal_compact ζ hc
    exact (hζ.comp continuous_norm).memLp_of_hasCompactSupport hc'
  let H : Maxwell.Space → ℝ := fun x => B^2*‖ζ ‖x‖‖^2
  have hH : Integrable H := (hζlp.norm.integrable_sq).const_mul (B^2)
  have hpoint : ∀ᵐ x : Maxwell.Space, Tendsto (fun j => f j x) atTop (𝓝 (g x)) := by
    filter_upwards with x
    let q := ConicalCapField.unit x
    have hz := SphereCapWeak.coordinate_range q
    have hs := Packet06ConeGradientLimit.normalized_slope_tendsto ell hell hbound t ((q : Maxwell.Space) 2) ht ht1 hz.1 hz.2
    have hcoef : Tendsto (fun j => CapSturmLiouville.coefficient (d j) t ((q : Maxwell.Space) 2)) atTop (𝓝 1) := by
      unfold CapSturmLiouville.coefficient
      split_ifs
      · exact tendsto_const_nhds
      · simpa using tendsto_const_nhds.add hd
    have hsc : Tendsto (fun j => CapSturmLiouville.coefficient (d j) t ((q : Maxwell.Space) 2) *
      (CapSturmLiouville.slope (ell j) t ((q : Maxwell.Space) 2)/t)) atTop (𝓝 1) := by
      simpa using hcoef.mul hs
    have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp hsc
    have he : (fun j => f j x) = fun j =>
      ((CapSturmLiouville.coefficient (d j) t ((q : Maxwell.Space) 2) *
        (CapSturmLiouville.slope (ell j) t ((q : Maxwell.Space) 2)/t) : ℝ) : ℂ)*g x := by
      funext j
      simp only [f,g,angularTest,limitTest,tangent,SphereCapH1.gradient,PiLp.smul_apply,smul_eq_mul,
        Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_inv]
      dsimp only [q]
      ring
    rw [he]
    simpa using hcast.mul_const (g x)
  have hbound' (j : ℕ) : ∀ᵐ x : Maxwell.Space, ‖f j x-g x‖^2 ≤ H x := by
    filter_upwards with x
    let q := ConicalCapField.unit x
    have hq : ‖(basis 2-((q : Maxwell.Space) 2) • (q : Maxwell.Space)) i‖ ≤ 1 :=
      (PiLp.norm_apply_le _ i).trans (SphereCapH1.tangent_norm_le q)
    have hw := (hweights (ell j) (hbound j) (d j) (hdBound j) i q).2
    have hb : ‖f j x-g x‖ ≤ B*‖ζ ‖x‖‖ := by
      calc
        _ ≤ ‖f j x‖+‖g x‖ := norm_sub_le _ _
        _ ≤ (t⁻¹*C)*‖ζ ‖x‖‖ + 1*‖ζ ‖x‖‖ := by
          apply add_le_add
          · dsimp [f,angularTest]
            rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),Complex.norm_real]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (inv_pos.mpr ht).le) (norm_nonneg _)
          · dsimp [g,limitTest]
            rw [norm_mul,Complex.norm_real,Complex.norm_real]
            exact mul_le_mul_of_nonneg_right hq (norm_nonneg _)
        _ = _ := by dsimp [B]; ring
    exact (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq (by dsimp [H]; ring)
  exact Packet06DominatedL2.toLp_tendsto f g hf hg H hH hbound' hpoint
#print axioms OQ14.Packet06SpatialAngularLimit.angularTest_memLp
#print axioms OQ14.Packet06SpatialAngularLimit.limitTest_eq
#print axioms OQ14.Packet06SpatialAngularLimit.angularTest_tendsto
end OQ14.Packet06SpatialAngularLimit
