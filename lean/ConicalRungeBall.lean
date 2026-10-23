import ConicalRungeAnnihilator
import Mathlib.Analysis.InnerProductSpace.Projection

/-! Actual compact source extension and transverse plane waves on a physical material ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalRungeBall
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalRungeAnnihilator
open scoped InnerProductSpace ComplexConjugate Topology
abbrev Space := Maxwell.Space
abbrev ScalarBall (a : ℝ) := Lp ℂ 2 (volume.restrict (closedBall (0 : Space) a))
abbrev BallL2 (a : ℝ) := PiLp 2 (fun _ : Fin 3 => ScalarBall a)

instance finite_ball (a : ℝ) : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) a)) := by
  constructor
  simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall (0 : Space) a).measure_lt_top

def density (a : ℝ) (g : BallL2 a) (j : Fin 3) : Space → ℂ :=
  (closedBall (0 : Space) a).indicator (fun x => conj (g j x))

theorem density_memLp (a : ℝ) (g : BallL2 a) (j : Fin 3) : MemLp (density a g j) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (Complex.conjCLE.toContinuousLinearMap.comp_memLp (g j))

def scalarExtension (a : ℝ) (g : BallL2 a) (j : Fin 3) : FourierL2.ScalarL2 :=
  (density_memLp a g j).toLp (density a g j)

def extension (a : ℝ) (g : BallL2 a) : VectorFourier.VectorL2 :=
  ∑ j : Fin 3, DynamicConvolution.insert j (scalarExtension a g j)

theorem extension_coordinate (a : ℝ) (g : BallL2 a) (j : Fin 3) :
    NewtonL2.physicalCoordinate (extension a g) j=scalarExtension a g j := by
  change DynamicConvolution.component j (∑ i : Fin 3, DynamicConvolution.insert i (scalarExtension a g i))=_
  simp only [map_sum,DynamicConvolution.component_insert]
  simp

theorem extension_ae (a : ℝ) (g : BallL2 a) (j : Fin 3) :
    NewtonL2.physicalCoordinate (extension a g) j =ᵐ[volume] density a g j := by
  rw [extension_coordinate]
  exact (density_memLp a g j).coeFn_toLp

theorem density_zero_outer (a : ℝ) (g : BallL2 a) (j : Fin 3) (x : Space)
    (hx : x ∉ closedBall (0 : Space) a) : density a g j x=0 :=
  indicator_of_not_mem hx _

theorem phase_norm (k : ℝ) (n x : Space) : ‖phase k n x‖=1 := by
  simp [phase,Complex.norm_exp]

def waveValue (k : ℝ) (n : Space) (i j : Fin 3) (x : Space) : ℂ :=
  phase k n x*DyadicRadiation.transverse n i j

theorem wave_memLp (k a : ℝ) (n : Space) (i j : Fin 3) :
    MemLp (waveValue k n i j) 2 (volume.restrict (closedBall (0 : Space) a)) := by
  have hc : Continuous (waveValue k n i j) := by
    unfold waveValue phase
    fun_prop
  apply MemLp.of_bound hc.aestronglyMeasurable 2
  filter_upwards with x
  simp only [waveValue,norm_mul,phase_norm,one_mul]
  exact DyadicRadiation.transverse_norm_bound n i j

def wave (k a : ℝ) (n : Space) (i : Fin 3) : BallL2 a :=
  (WithLp.equiv 2 (Fin 3 → ScalarBall a)).symm (fun j => (wave_memLp k a n i j).toLp (waveValue k n i j))

theorem density_integral (a : ℝ) (g : BallL2 a) (j : Fin 3) (f : Space → ℂ) :
    (∫ x, f x*density a g j x)=∫ x in closedBall (0 : Space) a, f x*conj (g j x) := by
  rw [← integral_indicator measurableSet_closedBall]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ closedBall (0 : Space) a <;> simp [density,hx]

theorem inner_wave_eq (k a : ℝ) (n : Space) (i : Fin 3) (g : BallL2 a) :
    ⟪g,wave k a n i⟫_ℂ=planePair k (density a g) n i := by
  rw [PiLp.inner_apply]
  unfold planePair
  apply Finset.sum_congr rfl
  intro j _
  rw [density_integral,← integral_const_mul,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(wave_memLp k a n i j).coeFn_toLp] with x hx
  change @inner ℂ ℂ _ (g j x) (((wave_memLp k a n i j).toLp (waveValue k n i j)) x)=_
  rw [hx]
  simp only [RCLike.inner_apply,waveValue]
  ring

end OQ14.ConicalRungeBall

#print axioms OQ14.ConicalRungeBall.density_memLp
#print axioms OQ14.ConicalRungeBall.extension_coordinate
#print axioms OQ14.ConicalRungeBall.extension_ae
#print axioms OQ14.ConicalRungeBall.density_zero_outer
#print axioms OQ14.ConicalRungeBall.phase_norm
#print axioms OQ14.ConicalRungeBall.wave_memLp
#print axioms OQ14.ConicalRungeBall.density_integral
#print axioms OQ14.ConicalRungeBall.inner_wave_eq
