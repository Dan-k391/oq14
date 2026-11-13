import Packet06PhysicalPairLimit
import Packet06SphereProjection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SpherePairIntegral
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.WeakGreen
  OQ14.Packet06SpatialAngularLimit OQ14.Packet06SphereProjection
open scoped Topology

theorem limit_pair_integral (b t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (g : ConicalRungeBall.BallL2 b) (F : Field) (hF : ∀ i, Continuous (fun x => F x i))
    (center : Maxwell.Space)
    (hg : ∀ i, (g i : Maxwell.Space → ℂ) =ᵐ[volume.restrict (closedBall 0 b)] fun x => F (center+x) i)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) b) :
    (∑ i : Fin 3, scalarProduct ((limitTest_memLp ζ hζ.continuous hc t ht ht1 i).toLp (limitTest ζ i))
      (NewtonL2.physicalCoordinate (ConicalBallExtension.vector b g) i)) =
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(ζ r : ℂ)*average F center r := by
  let Q : Maxwell.Space → ℂ := fun x => ∑ i : Fin 3, F (center+x) i*limitTest ζ i x
  have he (i : Fin 3) :
      (fun x => ((limitTest_memLp ζ hζ.continuous hc t ht ht1 i).toLp (limitTest ζ i)) x *
        NewtonL2.physicalCoordinate (ConicalBallExtension.vector b g) i x) =ᵐ[volume]
      fun x => F (center+x) i*limitTest ζ i x := by
    have hgi := (ae_restrict_iff' measurableSet_closedBall).mp (hg i)
    filter_upwards [(limitTest_memLp ζ hζ.continuous hc t ht ht1 i).coeFn_toLp,
      ConicalBallExtension.vector_ae b g i,hgi] with x htst hv hmatch
    rw [htst,hv]
    by_cases hx : x ∈ closedBall (0 : Maxwell.Space) b
    · rw [indicator_of_mem hx,hmatch hx]
      ring
    · have hz : ζ ‖x‖ = 0 := image_eq_zero_of_nmem_tsupport (fun hh => hx (by
        simpa only [mem_closedBall,dist_zero_right] using (hs hh).2.le))
      simp [limitTest,hz]
  have hi (i : Fin 3) : Integrable (fun x => F (center+x) i*limitTest ζ i x) :=
    (scalarProduct_integrable _ _).congr (he i)
  have hQ : Integrable Q := integrable_finset_sum Finset.univ (fun i _ => hi i)
  have hsum : (∑ i : Fin 3, scalarProduct ((limitTest_memLp ζ hζ.continuous hc t ht ht1 i).toLp (limitTest ζ i))
      (NewtonL2.physicalCoordinate (ConicalBallExtension.vector b g) i)) = ∫ x, Q x := by
    rw [integral_finset_sum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [scalarProduct_integral]
    exact integral_congr_ae (he i)
  rw [hsum, ComplexPolarIntegration.integral_polar_complex Q hQ]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp only [mul_assoc]
  change (r^2 : ℂ)*(∫ q : Sphere, Q (r • (q : Maxwell.Space)) ∂angularMeasure) =
    (r^2 : ℂ)*((ζ r : ℂ)*Packet06SphereProjection.average F center r)
  apply congrArg (fun z : ℂ => (r^2 : ℂ)*z)
  have hcont (i : Fin 3) : Continuous (fun q : Sphere => F (center+r • (q : Maxwell.Space)) i*tangent q i) := by
    have htang : Continuous (fun q : Sphere => tangent q i) := by
      simp only [tangent,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_mul]
      exact continuous_const.sub ((Complex.continuous_ofReal.comp (ConicalAngularTrial.coordinate_continuous 2)).mul
        (Complex.continuous_ofReal.comp (ConicalAngularTrial.coordinate_continuous i)))
    exact ((hF i).comp (continuous_const.add (continuous_const.smul continuous_subtype_val))).mul htang
  have hint (i : Fin 3) : Integrable (fun q : Sphere => F (center+r • (q : Maxwell.Space)) i*tangent q i) angularMeasure :=
    (hcont i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold Packet06SphereProjection.average
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with q
  have hrpos : 0 < r := hr
  have hnorm : ‖r • (q : Maxwell.Space)‖ = r := by simp [norm_smul,sphere_norm,abs_of_pos hrpos]
  simp only [Q,limitTest,ConicalCapField.unit_polar r hr q,hnorm,tangent,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
#print axioms OQ14.Packet06SpherePairIntegral.limit_pair_integral
end OQ14.Packet06SpherePairIntegral
