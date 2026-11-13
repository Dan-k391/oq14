import Packet06ProjectedGreen
import Packet06GlobalField
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ProjectedGlobal
open MeasureTheory Metric Filter Set Maxwell Packet06SectorOperator Packet06MaterialSector
open Packet06ProjectedGreen Packet06ExternalResidue Packet06ExternalFreeMaxwell
open Packet06GlobalField Packet06LocalPencil Packet06ProjectedSupport
open scoped Topology
abbrev V := VectorFourier.VectorL2

def field (c : StaticCoefficient.Coefficient) (S J : ℝ) (z : ℂ) (f : V) : Maxwell.Field :=
  let g := project f
  let q : V := Ring.inverse (pencil c S z) (incidentDatum c S J z g)
  fun x i => (z^2)⁻¹ * (electric (supportCoefficient J) z J g x i + electric c z S q x i)

theorem field_matches_local (c : StaticCoefficient.Coefficient) (S J T : ℝ)
    (hST : S+1 ≤ T) (hJT : J+1 ≤ T) (z : ℂ) (f : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hf : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    (fun x => field c S J z f x i) =ᵐ[volume.restrict (closedBall 0 T)]
      fun x => projectedField c S J T z f (VectorFourier.coordinateMap x) i := by
  let g := project f
  let q : V := Ring.inverse (pencil c S z) (incidentDatum c S J z g)
  have hgs : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 J → g (VectorFourier.coordinateMap x) = 0 :=
    projected_supported J f hf
  have hfix := supported_multiplier_identity J g hgs
  have hfree := electric_matches_response (supportCoefficient J) z J T hJT g (supportCoefficient_support J) i
  have hsc := electric_matches_response c z S T hST q hc i
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_smul (z^2)⁻¹ (kernel z J T g + response c z S T q))
  have hadd := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_add (kernel z J T g) (response c z S T q))
  filter_upwards [hfree,hsc,ae_restrict_of_ae hs,ae_restrict_of_ae hadd] with x hfree hsc hs hadd
  change (z^2)⁻¹ * (electric (supportCoefficient J) z J g x i + electric c z S q x i) = _
  rw [hfree,hsc]
  change (z^2)⁻¹ * ((response (supportCoefficient J) z J T g) (VectorFourier.coordinateMap x) i + _) = _
  have heq : response (supportCoefficient J) z J T g = kernel z J T g := by
    change kernel z J T (StaticCoefficient.sqrtMultiplier (supportCoefficient J) g) = _
    rw [hfix]
  rw [heq]
  change _ = ((z^2)⁻¹ • (kernel z J T g + response c z S T q) : V) (VectorFourier.coordinateMap x) i
  rw [hs]
  simp only [Pi.smul_apply,PiLp.smul_apply,smul_eq_mul]
  rw [hadd]
  rfl

theorem field_outgoing (c : StaticCoefficient.Coefficient) (S J : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J)
    (z : ℂ) (f : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (n : Maxwell.Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => (r : ℂ)*Complex.exp (-Complex.I*z*r)*field c S J z f (r • n) i)
      atTop (𝓝 ((z^2)⁻¹ * (ComplexDyadicOutgoing.amplitude (supportCoefficient J) z (project f) n i +
        ComplexDyadicOutgoing.amplitude c z
          (Ring.inverse (pencil c S z) (incidentDatum c S J z (project f))) n i))) := by
  have h1 := electric_outgoing (supportCoefficient J) z J hJ (project f) (supportCoefficient_support J) n hn i
  have h2 := electric_outgoing c z S hS (Ring.inverse (pencil c S z) (incidentDatum c S J z (project f))) hc n hn i
  have h : Tendsto (fun r : ℝ => (z^2)⁻¹ *
      ((r : ℂ)*Complex.exp (-Complex.I*z*r)*electric (supportCoefficient J) z J (project f) (r • n) i +
       (r : ℂ)*Complex.exp (-Complex.I*z*r)*electric c z S
         (Ring.inverse (pencil c S z) (incidentDatum c S J z (project f))) (r • n) i)) atTop _ :=
    tendsto_const_nhds.mul (h1.add h2)
  apply h.congr'
  filter_upwards with r
  dsimp only [field]
  ring

theorem field_memLp_ball (c : StaticCoefficient.Coefficient) (S J T : ℝ) (z : ℂ) (f : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) : MemLp (fun x => field c S J z f x i) 2 (volume.restrict (closedBall 0 T)) := by
  have h1 := electric_memLp_ball (supportCoefficient J) z J T (project f) (supportCoefficient_support J) i
  have h2 := electric_memLp_ball c z S T (Ring.inverse (pencil c S z) (incidentDatum c S J z (project f))) hc i
  exact (h1.add h2).const_mul (z^2)⁻¹

#print axioms OQ14.Packet06ProjectedGlobal.field_memLp_ball
theorem field_test_integral (c : StaticCoefficient.Coefficient) (S J T : ℝ)
    (hST : S+1 ≤ T) (hJT : J+1 ≤ T) (z : ℂ) (f : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hf : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (φ : DynamicSource.Test) (hφ : tsupport (φ.val : Maxwell.Space → ℂ) ⊆ closedBall 0 T)
    (a : Maxwell.Space → ℂ) :
    (∫ x, a x * field c S J z f x i * φ.val x) =
      ∫ x, a x * projectedField c S J T z f (VectorFourier.coordinateMap x) i * φ.val x := by
  apply integral_congr_ae
  have he := (ae_restrict_iff' measurableSet_closedBall).mp
    (field_matches_local c S J T hST hJT z f hc hf i)
  filter_upwards [he] with x hx
  by_cases hmem : x ∈ closedBall (0 : Maxwell.Space) T
  · rw [hx hmem]
  · have hz : φ.val x = 0 := image_eq_zero_of_nmem_tsupport (fun h => hmem (hφ h))
    simp [hz]

/-- One globally defined outgoing electric field solves the exact projected
source Maxwell equation against every compact smooth test. -/
theorem field_global_maxwell (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (hz : z ≠ 0) (hunit : IsUnit (pencil c S z)) (f : V)
    (hf : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (φ : DynamicSource.Test) :
    (∑ l : Fin 3, ∫ x : Maxwell.Space,
      field c S J z f x l * (DynamicSource.testPartial l (DynamicSource.testPartial i φ)).val x) -
    (∑ l : Fin 3, ∫ x : Maxwell.Space,
      field c S J z f x i * (DynamicSource.testPartial l (DynamicSource.testPartial l φ)).val x) -
    z^2 * (∫ x : Maxwell.Space, (1+(c.value (VectorFourier.coordinateMap x) : ℂ)) *
      field c S J z f x i * φ.val x) =
    ∫ x : Maxwell.Space, (project f) (VectorFourier.coordinateMap x) i * φ.val x := by
  obtain ⟨T₀,hT₀⟩ := φ.property.isBounded.subset_closedBall (0 : Maxwell.Space)
  let T := max T₀ (max (S+1) (J+1))
  have hST : S+1 ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hJT : J+1 ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  have hφ : tsupport (φ.val : Maxwell.Space → ℂ) ⊆ closedBall 0 T :=
    hT₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hp (j k : Fin 3) : tsupport ((DynamicSource.testPartial j (DynamicSource.testPartial k φ)).val : Maxwell.Space → ℂ) ⊆ closedBall 0 T :=
    (ComplexResponseRealWeak.partial_support j _).trans ((ComplexResponseRealWeak.partial_support k _).trans hφ)
  have he (j k l : Fin 3) :
      (∫ x : Maxwell.Space, field c S J z f x j * (DynamicSource.testPartial k (DynamicSource.testPartial l φ)).val x) =
      ∫ x : Maxwell.Space, projectedField c S J T z f (VectorFourier.coordinateMap x) j *
        (DynamicSource.testPartial k (DynamicSource.testPartial l φ)).val x := by
    simpa only [one_mul] using field_test_integral c S J T hST hJT z f hc hf j
      (DynamicSource.testPartial k (DynamicSource.testPartial l φ)) (hp k l) (fun _ => 1)
  simp_rw [he]
  rw [field_test_integral c S J T hST hJT z f hc hf i φ hφ]
  rw [← Packet06GreenPhysical.maxwell_test_physical,
    projected_source_maxwell c ha hm S J T hS hJ (by linarith) hc z hz hunit f hf i φ hφ,
    ComplexResponseTests.testPair_integral]

#print axioms OQ14.Packet06ProjectedGlobal.field_test_integral
#print axioms OQ14.Packet06ProjectedGlobal.field_global_maxwell
#print axioms OQ14.Packet06ProjectedGlobal.field_matches_local
#print axioms OQ14.Packet06ProjectedGlobal.field_outgoing
end OQ14.Packet06ProjectedGlobal
