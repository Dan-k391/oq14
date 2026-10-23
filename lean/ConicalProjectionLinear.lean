import ConicalProjectionData
import PolarMomentAE

/-! Actual subtraction of spatial potential/Gauss systems and their continuous angular moments. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalProjectionLinear
open MeasureTheory Set OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.AngularPower
  OQ14.ConicalProjectionData OQ14.ConicalGradientGraph OQ14.ConicalMomentWeights OQ14.PolarMomentTesting
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space

def graphSub (g h : Graph) : Graph where
  value := g.value-h.value
  gradient i := g.gradient i-h.gradient i
  weak i φ := by
    simp only [DivCurlCompact.HasWeakPartial, map_sub]
    linear_combination g.weak i φ-h.weak i φ

theorem gauss_integrable {p : Data} {a : ℝ} (s : System p a) (i : Fin 3) (f : 𝓢(Space,ℂ)) :
    Integrable (fun x : Space => (ConicalLocalGauss.epsilon p x : ℂ)*
      (s.graph.gradient i x+s.correction i x)*dcoord f x i) := by
  apply (NewtonL2.scalar_pairing_integrable
    (ConicalLocalGauss.displacementL2 p (totalCoordinate s) i) (GradientProjection.pderivative i f)).congr
  filter_upwards [ConicalLocalGauss.displacementL2_ae p (totalCoordinate s) i,totalCoordinate_ae s i] with x hd ht
  rw [hd,ht,GradientProjection.pderivative_apply]

def sub {p : Data} {a : ℝ} (s t : System p a) : System p a where
  graph := graphSub s.graph t.graph
  correction i := s.correction i-t.correction i
  continuous i := (s.continuous i).sub (t.continuous i)
  compact i := by simpa only [sub_eq_add_neg] using (s.compact i).add (t.compact i).neg'
  gauss f hf := by
    have he (i : Fin 3) : (∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
        ((graphSub s.graph t.graph).gradient i x+(s.correction i-t.correction i) x)*dcoord f x i)=
        (∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*(s.graph.gradient i x+s.correction i x)*dcoord f x i)-
        ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*(t.graph.gradient i x+t.correction i x)*dcoord f x i := by
      rw [← integral_sub (gauss_integrable s i f) (gauss_integrable t i f)]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (s.graph.gradient i) (t.graph.gradient i)] with x hx
      change (ConicalLocalGauss.epsilon p x : ℂ)*
        ((s.graph.gradient i-t.graph.gradient i) x+(s.correction i-t.correction i) x)*dcoord f x i=_
      rw [hx]
      simp only [Pi.sub_apply]
      ring
    simp only [he,Finset.sum_sub_distrib,s.gauss f hf,t.gauss f hf,sub_self]

private theorem moment_integrable {p : Data} {a : ℝ} (s : System p a) (i : Fin 3)
    (σ : Sphere → ℂ) (hσ : Measurable σ) (C : ℝ) (hb : ∀ n, ‖σ n‖ ≤ C) (r : ℝ) :
    Integrable (fun n : Sphere => s.correction i (r • (n : Space))*σ n) angularMeasure := by
  obtain ⟨M,hM⟩ := (s.compact i).exists_bound_of_continuous (s.continuous i)
  apply (integrable_const (M*C)).mono'
    (((s.continuous i).comp (continuous_const.smul continuous_subtype_val)).measurable.mul hσ).aestronglyMeasurable
  filter_upwards with n
  rw [norm_mul]
  exact mul_le_mul (hM _) (hb n) (norm_nonneg _) ((norm_nonneg _).trans (hM 0))

theorem moment_sub {p : Data} {a : ℝ} (s t : System p a) (i : Fin 3)
    (σ : Sphere → ℂ) (hσ : Measurable σ) (C : ℝ) (hb : ∀ n, ‖σ n‖ ≤ C) (r : ℝ) :
    moment ((sub s t).correction i) σ r=moment (s.correction i) σ r-moment (t.correction i) σ r := by
  change (∫ n : Sphere, (s.correction i (r • (n : Space))-t.correction i (r • (n : Space)))*σ n ∂angularMeasure)=_
  simp only [moment]
  rw [← integral_sub (moment_integrable s i σ hσ C hb r) (moment_integrable t i σ hσ C hb r)]
  apply integral_congr_ae
  filter_upwards with n
  ring

theorem radialCorrection_sub {p : Data} {a : ℝ} (s t : System p a) :
    radialCorrection (sub s t)=radialCorrection s-radialCorrection t := by
  ext r
  simp only [radialCorrection,Pi.sub_apply,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨C,_,hb⟩ := radial_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
  exact moment_sub s t i _ (radial_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb r

theorem tangentCorrection_sub {p : Data} {a : ℝ} (s t : System p a) :
    tangentCorrection (sub s t)=tangentCorrection s-tangentCorrection t := by
  ext r
  simp only [tangentCorrection,Pi.sub_apply,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨C,_,hb⟩ := tangent_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
  exact moment_sub s t i _ (tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb r

end OQ14.ConicalProjectionLinear

#print axioms OQ14.ConicalProjectionLinear.graphSub
#print axioms OQ14.ConicalProjectionLinear.gauss_integrable
#print axioms OQ14.ConicalProjectionLinear.sub
#print axioms OQ14.ConicalProjectionLinear.moment_sub
#print axioms OQ14.ConicalProjectionLinear.radialCorrection_sub
#print axioms OQ14.ConicalProjectionLinear.tangentCorrection_sub
