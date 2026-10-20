import ComplexConvolutionAnalytic
import NewtonReciprocity
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Bilateral reciprocity of the actual complex volume operator

The continuous complex-bilinear physical pairing turns operator reciprocity
into an entire scalar identity. Its actual real-frequency restriction vanishes,
so the identity principle extends it to all complex frequencies. Differentiating
that identity gives reciprocity of the parameter derivative in operator norm.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ComplexVolumeReciprocity

open MeasureTheory Metric KernelReciprocity
open OQ14.StaticCoefficient (Coefficient)
open scoped Topology

theorem scalarPair_smul_left (a : ℂ) (F G : ScalarL2) :
    scalarPair (a • F) G = a * scalarPair F G := by
  unfold scalarPair
  calc
    _ = ∫ x, a * (F x * G x) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul a F] with x hx
      simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
    _ = _ := integral_const_mul a _

theorem vectorPair_smul_left (a : ℂ) (F G : VectorL2) :
    vectorPair (a • F) G = a * vectorPair F G := by
  simp only [vectorPair, map_smul, scalarPair_smul_left, Finset.mul_sum]

def scalarPairFunctional (G : ScalarL2) : ScalarL2 →L[ℂ] ℂ where
  toFun F := scalarPair F G
  map_add' := fun F H => scalarPair_add_left F H G
  map_smul' := fun a F => scalarPair_smul_left a F G
  cont := by
    exact scalarPair_continuous.comp (f := fun F : ScalarL2 => (F, G))
      ((continuous_id : Continuous (fun F : ScalarL2 => F)).prodMk
        (continuous_const : Continuous (fun _ : ScalarL2 => G)))

def scalarReciprocityDefect (F G : ScalarL2) : (ScalarL2 →L[ℂ] ScalarL2) →L[ℂ] ℂ :=
  (scalarPairFunctional G).comp (ContinuousLinearMap.apply ℂ ScalarL2 F) -
    (scalarPairFunctional F).comp (ContinuousLinearMap.apply ℂ ScalarL2 G)

theorem scalarReciprocityDefect_apply (A : ScalarL2 →L[ℂ] ScalarL2) (F G : ScalarL2) :
    scalarReciprocityDefect F G A = scalarPair (A F) G - scalarPair F (A G) := by
  change scalarPair (A F) G - scalarPair (A G) F = _
  rw [scalarPair_comm (A G) F]

def pairFunctional (G : VectorL2) : VectorL2 →L[ℂ] ℂ where
  toFun F := vectorPair F G
  map_add' := fun F H => vectorPair_add_left F H G
  map_smul' := fun a F => vectorPair_smul_left a F G
  cont := by
    exact vectorPair_continuous.comp (f := fun F : VectorL2 => (F, G))
      ((continuous_id : Continuous (fun F : VectorL2 => F)).prodMk
        (continuous_const : Continuous (fun _ : VectorL2 => G)))

def reciprocityDefect (F G : VectorL2) : (VectorL2 →L[ℂ] VectorL2) →L[ℂ] ℂ :=
  (pairFunctional G).comp (ContinuousLinearMap.apply ℂ VectorL2 F) -
    (pairFunctional F).comp (ContinuousLinearMap.apply ℂ VectorL2 G)

theorem reciprocityDefect_apply (A : VectorL2 →L[ℂ] VectorL2) (F G : VectorL2) :
    reciprocityDefect F G A = vectorPair (A F) G - vectorPair F (A G) := by
  change vectorPair (A F) G - vectorPair (A G) F = _
  rw [vectorPair_comm (A G) F]

theorem entire_zero_of_real (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z)
    (hr : ∀ t : ℝ, f t = 0) : ∀ z, f z = 0 := by
  have hc : (0 : ℂ) ∈ closure ({z | f z = 0} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((ε / 2 : ℝ) : ℂ), ⟨hr _, ?_⟩, ?_⟩
    · simpa using (ne_of_gt (half_pos hε))
    · simpa [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hε] using (half_lt_self hε)
  exact fun z => (AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure
    (fun w _ => hf w) isPreconnected_univ (Set.mem_univ 0) hc) (Set.mem_univ z)

theorem entry_reciprocity (R : ℝ) (hR : 0 ≤ R) (k : ℂ) (i j : Fin 3)
    (F G : ScalarL2) :
    scalarPair (ComplexConvolutionAnalytic.entry k R i j F) G =
      scalarPair F (ComplexConvolutionAnalytic.entry k R i j G) := by
  have hz : ∀ z, scalarReciprocityDefect F G
      (ComplexConvolutionAnalytic.entry z R i j) = 0 := by
    apply entire_zero_of_real
    · intro z
      exact ((scalarReciprocityDefect F G).differentiable.comp
        (ComplexConvolutionAnalytic.entry_differentiable R hR i j)).analyticAt z
    · intro t
      rw [ComplexConvolutionAnalytic.entry_ofReal, scalarReciprocityDefect_apply,
        scalar_operator_reciprocity_all _ _ (kernel_even t R i j), sub_self]
  exact sub_eq_zero.mp ((scalarReciprocityDefect_apply _ F G).symm.trans (hz k))

theorem entry_deriv_reciprocity (R : ℝ) (hR : 0 ≤ R) (k : ℂ) (i j : Fin 3)
    (F G : ScalarL2) :
    scalarPair (deriv (fun z => ComplexConvolutionAnalytic.entry z R i j) k F) G =
      scalarPair F (deriv (fun z => ComplexConvolutionAnalytic.entry z R i j) k G) := by
  have he : (fun z => scalarReciprocityDefect F G
      (ComplexConvolutionAnalytic.entry z R i j)) = fun _ => 0 := by
    funext z
    rw [scalarReciprocityDefect_apply, entry_reciprocity R hR, sub_self]
  have hd := (scalarReciprocityDefect F G).hasFDerivAt.comp_hasDerivAt k
    ((ComplexConvolutionAnalytic.entry_differentiable R hR i j k).hasDerivAt)
  change HasDerivAt (fun z => scalarReciprocityDefect F G
    (ComplexConvolutionAnalytic.entry z R i j)) _ k at hd
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const k (0 : ℂ))
  exact sub_eq_zero.mp ((scalarReciprocityDefect_apply _ F G).symm.trans hz)

theorem volumeBlock_reciprocity (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (k : ℂ) (F G : VectorL2) :
    vectorPair (ComplexConvolutionAnalytic.volumeBlock c k R F) G =
      vectorPair F (ComplexConvolutionAnalytic.volumeBlock c k R G) := by
  have hz : ∀ z, reciprocityDefect F G
      (ComplexConvolutionAnalytic.volumeBlock c z R) = 0 := by
    apply entire_zero_of_real
    · intro z
      exact ((reciprocityDefect F G).differentiable.comp
        (ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR)).analyticAt z
    · intro t
      rw [ComplexConvolutionAnalytic.volumeBlock_ofReal, reciprocityDefect_apply,
        NewtonReciprocity.volumeBlock_reciprocity, sub_self]
  exact sub_eq_zero.mp ((reciprocityDefect_apply _ F G).symm.trans (hz k))

theorem volumeBlock_deriv_reciprocity (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (k : ℂ) (F G : VectorL2) :
    vectorPair (deriv (fun z => ComplexConvolutionAnalytic.volumeBlock c z R) k F) G =
      vectorPair F (deriv (fun z => ComplexConvolutionAnalytic.volumeBlock c z R) k G) := by
  have he : (fun z => reciprocityDefect F G
      (ComplexConvolutionAnalytic.volumeBlock c z R)) = fun _ => 0 := by
    funext z
    rw [reciprocityDefect_apply, volumeBlock_reciprocity c R hR, sub_self]
  have hd := (reciprocityDefect F G).hasFDerivAt.comp_hasDerivAt k
    ((ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR k).hasDerivAt)
  change HasDerivAt (fun z => reciprocityDefect F G
    (ComplexConvolutionAnalytic.volumeBlock c z R)) _ k at hd
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const k (0 : ℂ))
  exact sub_eq_zero.mp ((reciprocityDefect_apply _ F G).symm.trans hz)

end OQ14.ComplexVolumeReciprocity

#print axioms OQ14.ComplexVolumeReciprocity.scalarPair_smul_left
#print axioms OQ14.ComplexVolumeReciprocity.vectorPair_smul_left
#print axioms OQ14.ComplexVolumeReciprocity.scalarReciprocityDefect_apply
#print axioms OQ14.ComplexVolumeReciprocity.reciprocityDefect_apply
#print axioms OQ14.ComplexVolumeReciprocity.entire_zero_of_real
#print axioms OQ14.ComplexVolumeReciprocity.entry_reciprocity
#print axioms OQ14.ComplexVolumeReciprocity.entry_deriv_reciprocity
#print axioms OQ14.ComplexVolumeReciprocity.volumeBlock_reciprocity
#print axioms OQ14.ComplexVolumeReciprocity.volumeBlock_deriv_reciprocity
