import Packet06ComplexGauss
import Packet05RegionalDivergence

/-! Compact H1 scalar representatives and the genuine regional dielectric
equation, built from locally L2 potential data and a smooth-test Gauss law. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06ScalarGaussLocalization
open MeasureTheory Set Metric Filter Maxwell WeakCurl WeakGreen WeakPoynting
  DivCurlCompact ConicalGradientGraph Packet05RegionalDivergence PartialSmoothing
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space

def correction (χ : ContDiffBump (0 : Space)) (W : Field)
    (hW : ∀ i, Continuous (fun x => W x i)) (i : Fin 3) : L2Scalar :=
  (((Complex.continuous_ofReal.comp χ.continuous).mul (hW i)).memLp_of_hasCompactSupport
    ((χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right)).toLp
      (fun x => bump χ x*W x i)

theorem correction_ae (χ : ContDiffBump (0 : Space)) (W : Field)
    (hW : ∀ i, Continuous (fun x => W x i)) (i : Fin 3) :
    (correction χ W hW i : Space → ℂ) =ᵐ[volume] fun x => bump χ x*W x i :=
  MemLp.coeFn_toLp _

def weightL2 (ε : Space → ℂ) (hε : MemLp ε ⊤ volume) (f : L2Scalar) : L2Scalar :=
  ((Lp.memLp f).mul' hε).toLp (fun x => ε x*f x)

theorem weightL2_ae (ε : Space → ℂ) (hε : MemLp ε ⊤ volume) (f : L2Scalar) :
    (weightL2 ε hε f : Space → ℂ) =ᵐ[volume] fun x => ε x*f x :=
  MemLp.coeFn_toLp _

def flux (χ : ContDiffBump (0 : Space)) (u : PotentialData) (W : Field)
    (hW : ∀ i, Continuous (fun x => W x i)) (ε : Space → ℂ)
    (hε : MemLp ε ⊤ volume) : L2Vector :=
  fun i => weightL2 ε hε (gradient χ u i+correction χ W hW i)

theorem flux_ae (χ : ContDiffBump (0 : Space)) (u : PotentialData) (W : Field)
    (hW : ∀ i, Continuous (fun x => W x i)) (ε : Space → ℂ)
    (hε : MemLp ε ⊤ volume) (i : Fin 3) :
    (flux χ u W hW ε hε i : Space → ℂ) =ᵐ[volume]
      fun x => ε x*(gradient χ u i x + correction χ W hW i x) := by
  filter_upwards [weightL2_ae ε hε (gradient χ u i+correction χ W hW i),
    Lp.coeFn_add (gradient χ u i) (correction χ W hW i)] with x hw ha
  change weightL2 ε hε (gradient χ u i+correction χ W hW i) x=_
  rw [hw,ha]
  rfl

theorem schwartz_divergence_on (V : Set Space) (hV : IsOpen V) (P : L2Vector)
    (h : ∀ f : 𝓢(Space,ℂ), tsupport (f : Space → ℂ) ⊆ V →
      (∑ i : Fin 3, ∫ x, P i x*dcoord f x i)=0) : HasDivergenceOn V P 0 := by
  intro φ hφV
  let ψ : DomainCurl.Test V := ⟨φ,hφV⟩
  obtain ⟨K,f,hK,hKV,hfK,_hf,hd⟩ := InteriorTestDensity.interior_test_approximation hV ψ
  have hn (n : ℕ) : scalarProduct (P 0) (FourierL2.embed (GradientProjection.pderivative 0 (f n))) +
      scalarProduct (P 1) (FourierL2.embed (GradientProjection.pderivative 1 (f n))) +
      scalarProduct (P 2) (FourierL2.embed (GradientProjection.pderivative 2 (f n))) = 0 := by
    have hh := h (f n) ((hfK n).trans hKV)
    simpa only [Fin.sum_univ_three,scalarProduct_embed,GradientProjection.pderivative_apply] using hh
  have hl := (((scalarProduct (P 0)).continuous.tendsto _ |>.comp (hd 0)).add
    ((scalarProduct (P 1)).continuous.tendsto _ |>.comp (hd 1))).add
    ((scalarProduct (P 2)).continuous.tendsto _ |>.comp (hd 2))
  have hz := tendsto_nhds_unique hl (tendsto_const_nhds.congr'
    (Eventually.of_forall (fun n => (hn n).symm)))
  simpa only [ψ,testDerivativeL2,scalarProduct_continuousL2,derivativePair,
    valuePair,map_zero,zero_add] using hz

theorem compact_scalar_equation (χ : ContDiffBump (0 : Space)) (u : PotentialData)
    (W : Field) (hW : ∀ i, Continuous (fun x => W x i))
    (ε : Space → ℂ) (hε : MemLp ε ⊤ volume)
    (hGauss : ∀ f : 𝓢(Space,ℂ), tsupport (f : Space → ℂ) ⊆ ball (0 : Space) χ.rIn →
      (∑ i : Fin 3, ∫ x, ε x*(u.derivative i x+W x i)*dcoord f x i)=0) :
    CompactRepresentative (value χ u) ∧
    (∀ i, HasWeakPartial (value χ u) (gradient χ u i) i) ∧
    (∀ i, CompactRepresentative (correction χ W hW i)) ∧
    (∀ i, ∀ᵐ x ∂volume, x ∈ ball (0 : Space) χ.rIn →
      gradient χ u i x + correction χ W hW i x = u.derivative i x+W x i) ∧
    HasDivergenceOn (ball (0 : Space) χ.rIn) (flux χ u W hW ε hε) 0 := by
  have he (i : Fin 3) : ∀ᵐ x ∂volume, x ∈ ball (0 : Space) χ.rIn →
      gradient χ u i x+correction χ W hW i x=u.derivative i x+W x i := by
    filter_upwards [gradient_ae χ u i,correction_ae χ W hW i] with x hg hw hx
    obtain ⟨hb,hd⟩ := bump_inner χ x hx
    rw [hg,hw,hb,hd i]
    simp only [one_mul,zero_mul,add_zero]
  refine ⟨value_compact χ u,hasWeakPartial χ u,?_,he,?_⟩
  · intro i
    exact ⟨_,(χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right,
      correction_ae χ W hW i⟩
  · apply schwartz_divergence_on _ isOpen_ball
    intro f hf
    have hp (i : Fin 3) : (∫ x, flux χ u W hW ε hε i x*dcoord f x i)=
        ∫ x, ε x*(u.derivative i x+W x i)*dcoord f x i := by
      apply integral_congr_ae
      filter_upwards [flux_ae χ u W hW ε hε i,he i] with x hx hi
      by_cases hball : x ∈ ball (0 : Space) χ.rIn
      · rw [hx,hi hball]
      · have hn : x ∉ tsupport (f : Space → ℂ) := fun hh => hball (hf hh)
        simp only [dcoord,fderiv_of_not_mem_tsupport ℝ hn,ContinuousLinearMap.zero_apply,mul_zero]
    simpa only [hp] using hGauss f hf

end OQ14.Packet06ScalarGaussLocalization
#print axioms OQ14.Packet06ScalarGaussLocalization.correction_ae
#print axioms OQ14.Packet06ScalarGaussLocalization.weightL2_ae
#print axioms OQ14.Packet06ScalarGaussLocalization.flux_ae
#print axioms OQ14.Packet06ScalarGaussLocalization.schwartz_divergence_on
#print axioms OQ14.Packet06ScalarGaussLocalization.compact_scalar_equation
