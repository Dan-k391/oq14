import CapLegendreSeries
import Mathlib.Topology.Order.IntermediateValue

/-! A literal matching root for the cap-weighted axisymmetric Legendre equation.
The passage to a weak eigenfunction on the actual sphere is separate. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.CapAngularShooting
open Set OQ14.CapLegendreSeries

def determinant (d t a : ℝ) : ℝ :=
  (1+d)*poleD a t*odd a t - pole a t*oddD a t

theorem determinant_continuousOn (d t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    ContinuousOn (determinant d t) (Icc (0 : ℝ) 2) := by
  have hp : |(1-t)/2| < 1 := by rw [abs_of_pos (by linarith)]; linarith
  have ho : |t| < 1 := by rw [abs_of_pos ht]; exact ht1
  exact ((continuousOn_const.mul (poleD_parameter_continuousOn t hp)).mul
    (odd_parameter_continuousOn t ho)).sub
    ((pole_parameter_continuousOn t hp).mul (oddD_parameter_continuousOn t ho))

theorem determinant_zero_negative (d t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    determinant d t 0 < 0 := by
  have h := oddD_ge_one 0 t (by norm_num) (by rw [abs_of_pos ht]; exact ht1)
  simp only [determinant, poleD_zero, mul_zero, zero_mul, pole_zero, one_mul, zero_sub]
  linarith

theorem determinant_two (d t : ℝ) : determinant d t 2 = d*t := by
  simp only [determinant, poleD_two, odd_two, pole_two, oddD_two]
  ring

theorem exists_root (d t : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ a ∈ Ioo (0 : ℝ) 2, determinant d t a = 0 := by
  exact intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 2)
    (determinant_continuousOn d t ht ht1)
    ⟨determinant_zero_negative d t ht ht1, by rw [determinant_two]; exact mul_pos hd ht⟩

def exponent (a : ℝ) : ℝ := (Real.sqrt (1+4*a)-1)/2

theorem exponent_range (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 2) :
    exponent a ∈ Ioo (0 : ℝ) 1 := by
  have hsq := Real.sq_sqrt (by nlinarith [ha.1] : 0 ≤ 1+4*a)
  have hn := Real.sqrt_nonneg (1+4*a)
  constructor <;> dsimp [exponent] <;> nlinarith [ha.1, ha.2]

theorem exponent_equation (a : ℝ) (ha : 0 ≤ a) : exponent a * (exponent a+1) = a := by
  have hsq := Real.sq_sqrt (by linarith : 0 ≤ 1+4*a)
  dsimp [exponent]
  nlinarith

def interior (a t z : ℝ) : ℝ := pole a t*odd a z
def interiorD (a t z : ℝ) : ℝ := pole a t*oddD a z
def interiorDD (a t z : ℝ) : ℝ := pole a t*oddDD a z
def exterior (a t z : ℝ) : ℝ := odd a t*pole a z
def exteriorD (a t z : ℝ) : ℝ := odd a t*poleD a z
def exteriorDD (a t z : ℝ) : ℝ := odd a t*poleDD a z

theorem value_matching (a t : ℝ) : interior a t t = exterior a t t := mul_comm _ _

theorem flux_matching (d t a : ℝ) (hroot : determinant d t a = 0) :
    interiorD a t t = (1+d)*exteriorD a t t := by
  dsimp only [determinant] at hroot
  dsimp only [interiorD, exteriorD]
  nlinarith

theorem exterior_at_one (a t : ℝ) : exterior a t 1 = odd a t := by
  rw [exterior, pole_at_one, mul_one]

theorem exterior_nonzero (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    0 < exterior a t 1 := by rw [exterior_at_one]; exact odd_positive a t ha ht ht1

theorem interior_hasDerivAt (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |z| < 1) :
    HasDerivAt (interior a t) (interiorD a t z) z :=
  (odd_hasDerivAt a z ha hz).const_mul (pole a t)

theorem exterior_hasDerivAt (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |(1-z)/2| < 1) :
    HasDerivAt (exterior a t) (exteriorD a t z) z :=
  (pole_hasDerivAt a z ha hz).const_mul (odd a t)

theorem interiorD_hasDerivAt (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |z| < 1) :
    HasDerivAt (interiorD a t) (interiorDD a t z) z :=
  (oddD_hasDerivAt a z ha hz).const_mul (pole a t)

theorem exteriorD_hasDerivAt (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |(1-z)/2| < 1) :
    HasDerivAt (exteriorD a t) (exteriorDD a t z) z :=
  (poleD_hasDerivAt a z ha hz).const_mul (odd a t)

theorem interior_legendre (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |z| < 1) :
    (1-z^2)*interiorDD a t z - 2*z*interiorD a t z + a*interior a t z = 0 := by
  dsimp only [interior, interiorD, interiorDD]
  linear_combination (pole a t)*odd_legendre a z ha hz

theorem exterior_legendre (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |(1-z)/2| < 1) :
    (1-z^2)*exteriorDD a t z - 2*z*exteriorD a t z + a*exterior a t z = 0 := by
  dsimp only [exterior, exteriorD, exteriorDD]
  linear_combination (odd a t)*pole_legendre a z ha hz

theorem exists_matched_exponent (d t : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ a ∈ Ioo (0 : ℝ) 2,
      exponent a ∈ Ioo (0 : ℝ) 1 ∧ exponent a*(exponent a+1)=a ∧
      interior a t t = exterior a t t ∧ interiorD a t t = (1+d)*exteriorD a t t ∧
      0 < exterior a t 1 := by
  obtain ⟨a, ha, hr⟩ := exists_root d t hd ht ht1
  exact ⟨a, ha, exponent_range a ha, exponent_equation a ha.1.le,
    value_matching a t, flux_matching d t a hr, exterior_nonzero a t ⟨ha.1.le,ha.2.le⟩ ht ht1⟩

end OQ14.CapAngularShooting

#print axioms OQ14.CapAngularShooting.determinant_continuousOn
#print axioms OQ14.CapAngularShooting.determinant_zero_negative
#print axioms OQ14.CapAngularShooting.determinant_two
#print axioms OQ14.CapAngularShooting.exists_root
#print axioms OQ14.CapAngularShooting.exponent_range
#print axioms OQ14.CapAngularShooting.exponent_equation
#print axioms OQ14.CapAngularShooting.value_matching
#print axioms OQ14.CapAngularShooting.flux_matching
#print axioms OQ14.CapAngularShooting.exterior_at_one
#print axioms OQ14.CapAngularShooting.exterior_nonzero
#print axioms OQ14.CapAngularShooting.interior_hasDerivAt
#print axioms OQ14.CapAngularShooting.exterior_hasDerivAt
#print axioms OQ14.CapAngularShooting.interiorD_hasDerivAt
#print axioms OQ14.CapAngularShooting.exteriorD_hasDerivAt
#print axioms OQ14.CapAngularShooting.interior_legendre
#print axioms OQ14.CapAngularShooting.exterior_legendre
#print axioms OQ14.CapAngularShooting.exists_matched_exponent
