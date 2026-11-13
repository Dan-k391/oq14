import Packet05ScalarCutoffBound
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-! Construct all nested cutoff and translated-support inputs inside an actual open chart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05NestedChartCutoffs
open Set Metric Maxwell WeakCurl WeakConservation
open scoped Topology

def realTest {c : Space} (b : ContDiffBump c) : RealTest univ where
  function := b
  regular := b.contDiff
  compact := b.hasCompactSupport
  inside := subset_univ _

theorem test_smooth {c : Space} (b : ContDiffBump c) (n : ℕ) :
    ContDiff ℝ n (realTest b).function := b.contDiff

theorem test_support {c : Space} (b : ContDiffBump c) :
    tsupport (realTest b).function=closedBall c b.rOut := b.tsupport_eq

theorem test_one_eventually {c : Space} (b : ContDiffBump c) (x : Space)
    (hx : x ∈ ball c b.rIn) :
    (realTest b).function =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) ∧
    (realTest b).complexTest.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
  have h := b.eventuallyEq_one_of_mem_ball hx
  refine ⟨h,?_⟩
  filter_upwards [h] with y hy
  change (b y : ℂ)=1
  simp only [show b y=1 from hy,Complex.ofReal_one]

theorem test_value_bound {c : Space} (b : ContDiffBump c) (x : Space) :
    ‖(realTest b).complexTest.function x‖ ≤ 1 := by
  change ‖(b x : ℂ)‖ ≤ 1
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg b.nonneg] using b.le_one

theorem test_derivative_bound {c : Space} (b : ContDiffBump c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j x, ‖dcoord (realTest b).complexTest.function x j‖ ≤ C := by
  have hb (j : Fin 3) : ∃ C : ℝ, ∀ x, ‖dcoord (realTest b).complexTest.function x j‖ ≤ C :=
    ((realTest b).complexTest.compact.fderiv_apply ℝ (basis j)).exists_bound_of_continuous
      (partial_continuous (realTest b).complexTest.regular j)
  choose C hC using hb
  refine ⟨∑ j : Fin 3,max (C j) 0,Finset.sum_nonneg (fun _ _ => le_max_right _ _),?_⟩
  intro j x
  exact (hC j x).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ j)))

structure Data (Ω : Set Space) (c : Space) where
  r : ℝ
  positive : 0 < r
  outer : RealTest univ
  middle : RealTest univ
  inner : RealTest univ
  regular : ∀ n : ℕ, ContDiff ℝ n outer.function ∧ ContDiff ℝ n middle.function ∧ ContDiff ℝ n inner.function
  outer_support : tsupport outer.function ⊆ Ω
  outer_one : ∀ x ∈ ball c (8*r), outer.complexTest.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ))
  middle_one : ∀ x ∈ ball c (4*r), middle.function x=1
  shifted_support : ∀ t : Fin 3, ∀ h : ℝ, |h| < r → ∀ x ∈ tsupport middle.function,
    x ∈ ball c (8*r) ∧ x+h • basis t ∈ ball c (8*r)
  inner_support : tsupport inner.function ⊆ Ω
  inner_middle : tsupport inner.function ⊆ ball c (4*r)
  inner_one : ∀ x ∈ ball c (2*r), inner.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ))
  value_bound : ∀ x, ‖outer.complexTest.function x‖ ≤ 1 ∧
    ‖middle.complexTest.function x‖ ≤ 1 ∧ ‖inner.complexTest.function x‖ ≤ 1
  derivative_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ j x,
    ‖dcoord outer.complexTest.function x j‖ ≤ C ∧
    ‖dcoord middle.complexTest.function x j‖ ≤ C ∧
    ‖dcoord inner.complexTest.function x j‖ ≤ C

theorem exists_nested (Ω : Set Space) (hΩ : IsOpen Ω) (c : Space) (hc : c ∈ Ω) :
    Nonempty (Data Ω c) := by
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hΩ c hc
  let r := R/16
  have hr : 0 < r := by dsimp [r]; positivity
  let b₀ : ContDiffBump c := ⟨8*r,9*r,by positivity,by linarith⟩
  let b₁ : ContDiffBump c := ⟨4*r,5*r,by positivity,by linarith⟩
  let b₂ : ContDiffBump c := ⟨2*r,3*r,by positivity,by linarith⟩
  have h9 : 9*r<R := by dsimp [r]; linarith
  have ho : tsupport (realTest b₀).function ⊆ Ω := by
    rw [test_support]
    exact (closedBall_subset_ball h9).trans hball
  have hi : tsupport (realTest b₂).function ⊆ Ω := by
    rw [test_support]
    exact (closedBall_subset_ball (show 3*r<R by linarith)).trans hball
  obtain ⟨C₀,hC₀,hb₀⟩ := test_derivative_bound b₀
  obtain ⟨C₁,hC₁,hb₁⟩ := test_derivative_bound b₁
  obtain ⟨C₂,hC₂,hb₂⟩ := test_derivative_bound b₂
  refine ⟨⟨r,hr,realTest b₀,realTest b₁,realTest b₂,
    (fun n => ⟨test_smooth b₀ n,test_smooth b₁ n,test_smooth b₂ n⟩),ho,
    (fun x hx => (test_one_eventually b₀ x hx).2),?_,?_,hi,?_,
    (fun x hx => (test_one_eventually b₂ x hx).1),
    (fun x => ⟨test_value_bound b₀ x,test_value_bound b₁ x,test_value_bound b₂ x⟩),?_⟩⟩
  · intro x hx
    exact b₁.one_of_mem_closedBall (ball_subset_closedBall hx)
  · intro t h hh x hx
    rw [test_support] at hx
    have hx5 : dist x c ≤ 5*r := hx
    have hnorm : ‖basis t‖=1 := by simp [basis]
    have hdiff : dist (x+h • basis t) x=|h| := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul,hnorm,mul_one,Real.norm_eq_abs]
    have htri := dist_triangle (x+h • basis t) x c
    rw [hdiff] at htri
    exact ⟨show dist x c<8*r by linarith,show dist (x+h • basis t) c<8*r by linarith⟩
  · rw [test_support]
    exact closedBall_subset_ball (show 3*r<4*r by linarith)
  · refine ⟨C₀+C₁+C₂,by positivity,?_⟩
    intro j x
    have h0 := hb₀ j x
    have h1 := hb₁ j x
    have h2 := hb₂ j x
    exact ⟨by linarith,by linarith,by linarith⟩

end OQ14.Packet05NestedChartCutoffs
#print axioms OQ14.Packet05NestedChartCutoffs.test_smooth
#print axioms OQ14.Packet05NestedChartCutoffs.test_support
#print axioms OQ14.Packet05NestedChartCutoffs.test_one_eventually
#print axioms OQ14.Packet05NestedChartCutoffs.test_value_bound
#print axioms OQ14.Packet05NestedChartCutoffs.test_derivative_bound
#print axioms OQ14.Packet05NestedChartCutoffs.exists_nested
