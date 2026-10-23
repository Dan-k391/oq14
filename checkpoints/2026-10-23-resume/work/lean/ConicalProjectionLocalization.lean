import ConicalProjectionData

/-! Construct the generic spatial projection data from an actual locally L2 weak potential. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.ConicalProjectionLocalization
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume
  OQ14.ConicalGradientGraph OQ14.ConicalProjectionData
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space

def ofPotential (p : Data) (a : ℝ) (hai : a < p.cutoff.rIn) (u : PotentialData)
    (W : Field) (hW : ∀ i, Continuous (fun x => W x i))
    (hGauss : ∀ f : 𝓢(Space,ℂ), tsupport (f : Space → ℂ) ⊆ ball (0 : Space) a →
      (∑ i : Fin 3, ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
        (u.derivative i x+W x i)*dcoord f x i)=0) : System p a where
  graph := ConicalGradientGraph.ofPotential p.cutoff u
  correction i x := bump p.cutoff x*W x i
  continuous i := (Complex.continuous_ofReal.comp p.cutoff.continuous).mul (hW i)
  compact i := (p.cutoff.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right
  gauss f hf := by
    have he (i : Fin 3) : (∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
        ((ConicalGradientGraph.ofPotential p.cutoff u).gradient i x+bump p.cutoff x*W x i)*dcoord f x i)=
        ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*(u.derivative i x+W x i)*dcoord f x i := by
      apply integral_congr_ae
      filter_upwards [gradient_ae p.cutoff u i] with x hx
      change (ConicalLocalGauss.epsilon p x : ℂ)*(gradient p.cutoff u i x+bump p.cutoff x*W x i)*dcoord f x i=_
      by_cases hi : x ∈ ball (0 : Space) a
      · have hm := bump_inner p.cutoff x (ball_subset_ball hai.le hi)
        rw [hx,hm.1,hm.2 i]
        simp only [one_mul,zero_mul,add_zero]
      · have hn : x ∉ tsupport (f : Space → ℂ) := fun h => hi (hf h)
        simp only [dcoord,fderiv_of_not_mem_tsupport ℝ hn,ContinuousLinearMap.zero_apply,mul_zero]
    simpa only [he] using hGauss f hf

theorem total_inner (p : Data) (a : ℝ) (hai : a < p.cutoff.rIn) (u : PotentialData)
    (W : Field) (hW : ∀ i, Continuous (fun x => W x i))
    (hGauss : ∀ f : 𝓢(Space,ℂ), tsupport (f : Space → ℂ) ⊆ ball (0 : Space) a →
      (∑ i : Fin 3, ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
        (u.derivative i x+W x i)*dcoord f x i)=0) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) a →
      totalCoordinate (ofPotential p a hai u W hW hGauss) i x=u.derivative i x+W x i := by
  filter_upwards [totalCoordinate_ae (ofPotential p a hai u W hW hGauss) i,gradient_ae p.cutoff u i] with x ht hg
  intro hx
  have hm := bump_inner p.cutoff x (ball_subset_ball hai.le hx)
  rw [ht]
  change gradient p.cutoff u i x+bump p.cutoff x*W x i=_
  rw [hg,hm.1,hm.2 i]
  simp only [one_mul,zero_mul,add_zero]

end OQ14.ConicalProjectionLocalization

#print axioms OQ14.ConicalProjectionLocalization.ofPotential
#print axioms OQ14.ConicalProjectionLocalization.total_inner
