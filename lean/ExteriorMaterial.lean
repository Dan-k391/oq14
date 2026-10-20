import ExteriorContinuity
import SmallVolumeMaxwell

/-! # Material Maxwell fields with continuous exterior representatives

The explicit exterior replacement is globally equal almost everywhere to the
constructed volume response. Its local L2 regularity, material self-consistency
and weak Maxwell equations therefore follow from actual integral identities.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ExteriorMaterial

open MeasureTheory Metric OQ14.Maxwell OQ14.MaterialMaxwell

abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

def scattered (c : Coefficient) (k R : ℝ) (u : VectorL2) : Field :=
  ExteriorContinuity.representative k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) R

def total (c : Coefficient) (k R : ℝ) (u : VectorL2) (incident : Field) : Field :=
  fun x i => incident x i + scattered c k R u x i

theorem scattered_ae (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    scattered c k R u =ᵐ[volume] MaterialField.scattered c k u :=
  ExteriorContinuity.representative_ae k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u R hc)
    (StaticNewton.material_source_ae c u) R (DynamicVolume.source_zero c u R hc)

theorem total_ae (c : Coefficient) (k R : ℝ) (u : VectorL2) (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    total c k R u incident =ᵐ[volume] MaterialField.total c k u incident := by
  filter_upwards [scattered_ae c k R u hc] with x hx
  ext i
  simp only [total, MaterialField.total, hx]

theorem scattered_exterior (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (x : Space) (hx : R < ‖x‖) (i : Fin 3) :
    scattered c k R u x i = ∑ j, ∫ y,
      DynamicVolume.source c u j y * DyadicKernel.dyadic k (x-y) i j := by
  rw [scattered, ExteriorContinuity.representative_exterior k _ _ R x hx]
  rfl

theorem scattered_continuousAt (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (x : Space) (hx : R < ‖x‖) : ContinuousAt (scattered c k R u) x :=
  ExteriorContinuity.representative_continuousAt k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u R hc)
    R (DynamicVolume.source_zero c u R hc) x hx

theorem total_memLp_ball (c : Coefficient) (k R T : ℝ) (u : VectorL2) (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hE : ∀ i, MemLp (fun x => incident x i) 2 (volume.restrict (closedBall 0 T)))
    (i : Fin 3) :
    MemLp (fun x => total c k R u incident x i) 2 (volume.restrict (closedBall 0 T)) := by
  apply (SmallVolumeMaxwell.total_electric_memLp_ball c k R T u incident hc hE i).ae_eq
  filter_upwards [ae_restrict_of_ae (total_ae c k R u incident hc)] with x hx
  exact (congrFun hx i).symm

theorem fieldPair_congr (E F : Field) (h : E =ᵐ[volume] F) :
    fieldPair E = fieldPair F := by
  funext i f
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem testMaxwell_congr (k : ℝ) (ε : Space → ℝ) (E H E' H' : Field)
    (hE : E =ᵐ[volume] E') (hH : H =ᵐ[volume] H')
    (hM : TestMaxwell k ε E H) : TestMaxwell k ε E' H' := by
  have hpE := fieldPair_congr E E' hE
  have hpH := fieldPair_congr H H' hH
  intro i f
  have hi : (∫ x, (ε x : ℂ) * E x i * f.val x) =
      ∫ x, (ε x : ℂ) * E' x i * f.val x := by
    apply integral_congr_ae
    filter_upwards [hE] with x hx
    rw [hx]
  simpa only [hpE, hpH, hi] using hM i f

theorem material_relation (c : Coefficient) (k R : ℝ) (u f : VectorL2) (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * incident x i)
    (hsol : DynamicVolume.volumeBlock c k R u = f) (i : Fin 3) :
    DynamicVolume.source c u i =ᵐ[volume] fun x =>
      (c.value (VectorFourier.coordinateMap x) : ℂ) * total c k R u incident x i := by
  filter_upwards [MaterialField.material_relation c k R u f incident hc hincident hsol i,
    total_ae c k R u incident hc] with x hm he
  rw [hm, he]

/-- Actual dielectric fields with a pointwise continuous scattered electric
representative outside the source. The radiation estimate remains separate. -/
theorem exists_small_volume_fields (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hsmall : 252 * c.bound * k^2 * R^2 < 1)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (Einc Hinc : Field)
    (hE : ∀ T i, MemLp (fun x => Einc x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => Hinc x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : TestMaxwell k (fun _ => 1) Einc Hinc) :
    ∃ u : VectorL2,
      DynamicVolume.volumeBlock c k R u = IncidentLocalization.datum c R Einc hc (hE R) ∧
      ‖u‖ ≤ (1 - 252 * c.bound * k^2 * R^2)⁻¹ *
        ‖IncidentLocalization.datum c R Einc hc (hE R)‖ ∧
      TestMaxwell k (dielectric c) (total c k R u Einc) (totalMagnetic c k u Hinc) ∧
      (∀ T i, MemLp (fun x => total c k R u Einc x i) 2
        (volume.restrict (closedBall 0 T))) ∧
      (∀ T i, MemLp (fun x => totalMagnetic c k u Hinc x i) 2
        (volume.restrict (closedBall 0 T))) ∧
      (∀ x, R < ‖x‖ → ContinuousAt (scattered c k R u) x) ∧
      (∀ i, DynamicVolume.source c u i =ᵐ[volume] fun x =>
        (c.value (VectorFourier.coordinateMap x) : ℂ) * total c k R u Einc x i) := by
  obtain ⟨u, hu, hn, hM, _, hHu⟩ :=
    SmallVolumeMaxwell.exists_small_volume_fields c k R hR hsmall hc Einc Hinc hE hH hMax
  refine ⟨u, hu, hn, ?_, ?_, hHu, scattered_continuousAt c k R u hc, ?_⟩
  · exact testMaxwell_congr k (dielectric c) _ _ _ _
      (total_ae c k R u Einc hc).symm Filter.EventuallyEq.rfl hM
  · exact fun T i => total_memLp_ball c k R T u Einc hc (hE T) i
  · exact material_relation c k R u _ Einc hc
      (IncidentLocalization.datum_actual c R Einc hc (hE R)) hu

end OQ14.ExteriorMaterial

#print axioms OQ14.ExteriorMaterial.scattered_ae
#print axioms OQ14.ExteriorMaterial.total_ae
#print axioms OQ14.ExteriorMaterial.scattered_exterior
#print axioms OQ14.ExteriorMaterial.scattered_continuousAt
#print axioms OQ14.ExteriorMaterial.total_memLp_ball
#print axioms OQ14.ExteriorMaterial.fieldPair_congr
#print axioms OQ14.ExteriorMaterial.testMaxwell_congr
#print axioms OQ14.ExteriorMaterial.material_relation
#print axioms OQ14.ExteriorMaterial.exists_small_volume_fields
